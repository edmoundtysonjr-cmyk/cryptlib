/****************************************************************************
*																			*
*						Semaphores, Mutexes, and Threads					*
*						Copyright Peter Gutmann 1997-2025					*
*																			*
****************************************************************************/

#if defined( INC_ALL )
  #include "crypt.h"
  #include "acl.h"
  #include "kernel.h"
#else
  #include "crypt.h"
  #include "kernel/acl.h"
  #include "kernel/kernel.h"
#endif /* Compiler-specific includes */

/****************************************************************************
*																			*
*							Init/Shutdown Functions							*
*																			*
****************************************************************************/

/* A template to initialise the semaphore table.  Thread handles may be 
   pointers or scalars so we don't try and specify any initialisers beyond
   the first one, and let the compiler take care of the details */

static const SEMAPHORE_INFO SEMAPHORE_INFO_TEMPLATE = \
				{ SEMAPHORE_STATE_UNINITED };

/* Create and destroy the semaphores and mutexes.  Since mutexes usually 
   aren't scalar values and are declared and accessed via macros that 
   manipulate various fields, we have to handle a pile of them individually 
   rather than using an array of mutexes */

CHECK_RETVAL \
int initSemaphores( void )
	{
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );
	LOOP_INDEX i;
	int status;

	/* Make sure that we've got the correct number of mutexes, which run
	   between MUTEX_NONE and MUTEX_LAST */
#if defined( USE_SESSIONS )
	static_assert( MUTEX_LAST == 6, "Mutex value" );
#elif defined( USE_TCP )
	static_assert( MUTEX_LAST == 4, "Mutex value" );
#else
	static_assert( MUTEX_LAST == 3, "Mutex value" );
#endif /* USE_SESSIONS */

	REQUIRES( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );

	/* Clear the semaphore table */
	LOOP_SMALL( i = 0, i < SEMAPHORE_LAST, i++ )
		{
		ENSURES( LOOP_INVARIANT_SMALL( i, 0, SEMAPHORE_LAST - 1 ) );

		krnlData->semaphoreInfo[ i ] = SEMAPHORE_INFO_TEMPLATE;
		}
	ENSURES( LOOP_BOUND_OK );

	/* Initialize any data structures required to make the semaphore table
	   thread-safe */
	MUTEX_CREATE( semaphore, status );
	ENSURES( cryptStatusOK( status ) );

	/* Initialize the mutexes */
	MUTEX_CREATE( mutex1, status );
	ENSURES( cryptStatusOK( status ) );
	MUTEX_CREATE( mutex2, status );
	ENSURES( cryptStatusOK( status ) );
#ifdef USE_SESSIONS
	MUTEX_CREATE( mutex3, status );
	ENSURES( cryptStatusOK( status ) );
#endif /* USE_SESSIONS */
#ifdef USE_TCP
	MUTEX_CREATE( mutex4, status );
	ENSURES( cryptStatusOK( status ) );
#endif /* USE_TCP */
#ifdef USE_SESSIONS
	MUTEX_CREATE( mutex5, status );
	ENSURES( cryptStatusOK( status ) );
#endif /* USE_SESSIONS */

	return( CRYPT_OK );
	}

void endSemaphores( void )
	{
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );

	REQUIRES_V( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );
	REQUIRES_V( ( krnlData->initLevel == INIT_LEVEL_KRNLDATA && \
				  ( krnlData->shutdownLevel == SHUTDOWN_LEVEL_NONE || \
					krnlData->shutdownLevel == SHUTDOWN_LEVEL_MESSAGES ) ) || \
				( krnlData->initLevel == INIT_LEVEL_FULL && \
				  krnlData->shutdownLevel >= SHUTDOWN_LEVEL_MESSAGES ) );

	/* Signal that kernel mechanisms are no longer available */
	krnlData->shutdownLevel = SHUTDOWN_LEVEL_MUTEXES;

	/* Shut down the mutexes */
#ifdef USE_SESSIONS
	MUTEX_DESTROY( mutex5 );
#endif /* USE_SESSIONS */
#ifdef USE_TCP
	MUTEX_DESTROY( mutex4 );
#endif /* USE_TCP */
#ifdef USE_SESSIONS
	MUTEX_DESTROY( mutex3 );
#endif /* USE_SESSIONS */
	MUTEX_DESTROY( mutex2 );
	MUTEX_DESTROY( mutex1 );

	/* Destroy any data structures required to make the semaphore table
	   thread-safe */
	MUTEX_DESTROY( semaphore );
	}

/****************************************************************************
*																			*
*							Semaphore Functions								*
*																			*
****************************************************************************/

#ifdef USE_THREAD_FUNCTIONS

/* Under multithreaded OSes, we often need to wait for certain events before
   we can continue (for example when asynchronously accessing system
   objects anything that depends on the object being available needs to
   wait for the access to complete) or handle mutual exclusion when accessing
   a shared resource.  The following functions abstract this handling,
   providing a lightweight semaphore mechanism via mutexes, which is used 
   before checking a system synchronisation object (mutexes usually don't
   require a kernel entry, while semaphores usually do).  The semaphore 
   function works a bit like the Win32 Enter/LeaveCriticalSection() 
   routines, which perform a quick check on a user-level lock and only call 
   the kernel-level handler if necessary (in most cases this isn't 
   necessary).  A useful side-effect is that since they work with 
   lightweight local locks instead of systemwide locking objects, they 
   aren't vulnerable to security problems where (for example) another 
   process can mess with a globally visible object handle.  This is 
   particularly problematic under Windows, where (for example) CreateMutex()
   can return a handle to an already-existing object of the same name rather
   than a newly-created object (there's no O_EXCL functionality).

   Semaphores are one-shots, so that once set and cleared they can't be
   reset.  This is handled by enforcing the following state transitions:

	Uninited -> Set | Clear
	Set -> Set | Clear
	Clear -> Clear

   The handling is complicated somewhat by the fact that on some systems the
   semaphore has to be explicitly deleted, but only the last thread to use it
   can safely delete it.  In order to handle this, we reference-count the
   semaphore and let the last thread out delete it.  This is handled by
   introducing an additional state preClear, which indicates that while the
   semaphore object is still present, the last thread out should delete it,
   bringing it to the true clear state */

void setSemaphore( IN_ENUM( SEMAPHORE ) const SEMAPHORE_TYPE semaphore,
				   const MUTEX_HANDLE semaphoreObject,
				   const THREAD_HANDLE threadObject )
	{
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );
	SEMAPHORE_INFO *semaphoreInfo;

	REQUIRES_V( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );
	REQUIRES_V( isEnumRange( semaphore, SEMAPHORE ) );

	/* If we're in a shutdown and the semaphores have been destroyed, don't
	   try and acquire the semaphore mutex.  In this case anything that 
	   they're protecting should be set to a shutdown state in which any 
	   access fails, so this isn't a problem */
	if( krnlData->shutdownLevel >= SHUTDOWN_LEVEL_MUTEXES )
		return;

	/* It's safe to get a pointer to this outside the lock, we just can't
	   access it yet */
	semaphoreInfo = &krnlData->semaphoreInfo[ semaphore ];

	/* Lock the semaphore table, set the semaphore, and unlock it again */
	MUTEX_LOCK( semaphore );
	if( semaphoreInfo->state == SEMAPHORE_STATE_UNINITED )
		{
		/* The semaphore can only be set if it's currently in the uninited 
		   state */
		*semaphoreInfo = SEMAPHORE_INFO_TEMPLATE;
		semaphoreInfo->state = SEMAPHORE_STATE_SET;
		semaphoreInfo->semaphoreObject = semaphoreObject;
		semaphoreInfo->threadObject = threadObject;
		}
	MUTEX_UNLOCK( semaphore );
	}

void clearSemaphore( IN_ENUM( SEMAPHORE ) const SEMAPHORE_TYPE semaphore )
	{
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );
	SEMAPHORE_INFO *semaphoreInfo;

	REQUIRES_V( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );
	REQUIRES_V( isEnumRange( semaphore, SEMAPHORE ) );

	/* If we're in a shutdown and the semaphores have been destroyed, don't
	   try and acquire the semaphore mutex.  In this case anything that 
	   they're protecting should be set to a shutdown state in which any 
	   access fails, so this isn't a problem */
	if( krnlData->shutdownLevel >= SHUTDOWN_LEVEL_MUTEXES )
		return;

	/* It's safe to get a pointer to this outside the lock, we just can't
	   access it yet */
	semaphoreInfo = &krnlData->semaphoreInfo[ semaphore ];

	/* Lock the semaphore table, clear the semaphore, and unlock it again */
	MUTEX_LOCK( semaphore );
	if( semaphoreInfo->state == SEMAPHORE_STATE_UNINITED )
		{
		/* It's theoretically possible that we can get here before the 
		   semaphore has been set, which could happen if the thread exits 
		   before krnlDispatchThread() gets to the setSemaphore() call.
		   This makes the clearSemaphore() a no-op, so we move it 
		   directly into the cleared state and exit */
		semaphoreInfo->state = SEMAPHORE_STATE_CLEAR;
		MUTEX_UNLOCK( semaphore );
		return;
		}
	if( semaphoreInfo->state == SEMAPHORE_STATE_SET )
		{
		/* Make sure that the reference count is valid.  This is yet another
		   should-never-occur condition, we can't touch the reference count
		   but can at least put the semaphore into the pre-clear condition 
		   to try and get it cleaned up later */
		if( semaphoreInfo->refCount < 0 || \
			semaphoreInfo->refCount >= MAX_INTLENGTH_SHORT - 1 )
			{
			semaphoreInfo->state = SEMAPHORE_STATE_PRECLEAR;
			DEBUG_DIAG(( "Semaphore lock count %d invalid", 
						 semaphoreInfo->refCount ));
			MUTEX_UNLOCK( semaphore );
			assert( DEBUG_WARN );
			return;
			}

		/* If there are threads waiting on this semaphore, tell the last
		   thread out to turn out the lights */
		if( semaphoreInfo->refCount > 0 )
			semaphoreInfo->state = SEMAPHORE_STATE_PRECLEAR;
		else
			{
			/* No threads waiting on the semaphore, we can delete it and set
			   the state to done */
			THREAD_CLOSE( semaphoreInfo->threadObject );
			*semaphoreInfo = SEMAPHORE_INFO_TEMPLATE;
			semaphoreInfo->state = SEMAPHORE_STATE_CLEAR;
			}
		}
	MUTEX_UNLOCK( semaphore );
	}

/* Wait on a semaphore.  This occurs in two phases, first we extract the
   information that we need from the semaphore table, then we unlock it and 
   wait on the semaphore if necessary.  This is necessary because the wait 
   can take an indeterminate amount of time and we don't want to tie up the 
   other semaphores while this occurs.  Note that this type of waiting on 
   local (rather than system) semaphores where possible greatly improves
   performance, in some cases the wait on a signalled system semaphore can
   take several seconds whereas waiting on the local semaphore only takes a
   few ms.  Once the wait has completed, we update the semaphore state as
   per the longer description above */

STDC_NONNULL_ARG( ( 1 ) ) \
static void releaseRefOpt( SEMAPHORE_INFO *semaphoreInfo )
	{
	assert( isWritePtr( semaphoreInfo, sizeof( SEMAPHORE_INFO ) ) );
	
	/* If the semaphore isn't set, there's nothing to do */
	if( semaphoreInfo->state != SEMAPHORE_STATE_SET && \
		semaphoreInfo->state != SEMAPHORE_STATE_PRECLEAR )
		return;

	/* Make sure that the lock count is valid */
	if( !isShortIntegerRangeNZ( semaphoreInfo->refCount ) )
		{
		DEBUG_DIAG(( "Semaphore lock count %d invalid", 
					 semaphoreInfo->refCount ));
		assert( DEBUG_WARN );
		return;
		}

	/* The semaphore is still set, update the reference count */
	REQUIRES_V( !checkOverflowDec( semaphoreInfo->refCount ) );
	semaphoreInfo->refCount--;

	/* If the object owner has signalled that it's done with the object and 
	   the reference count has reached zero, we can delete it */
	if( semaphoreInfo->state == SEMAPHORE_STATE_PRECLEAR && \
		semaphoreInfo->refCount <= 0 )
		{
		/* No threads waiting on the semaphore, we can delete it and set
		   the state to done */
		THREAD_CLOSE( semaphoreInfo->threadObject );
		*semaphoreInfo = SEMAPHORE_INFO_TEMPLATE;
		semaphoreInfo->state = SEMAPHORE_STATE_CLEAR;
		}
	}

CHECK_RETVAL_BOOL \
BOOLEAN krnlWaitSemaphore( IN_ENUM( SEMAPHORE ) const SEMAPHORE_TYPE semaphore )
	{
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );
	SEMAPHORE_INFO *semaphoreInfo;
#ifdef NONSCALAR_HANDLES
	MUTEX_HANDLE *semaphoreObject DUMMY_INIT_PTR;
	THREAD_HANDLE *threadObject DUMMY_INIT_PTR;
#else
	MUTEX_HANDLE semaphoreObject DUMMY_INIT_MUTEX;
	THREAD_HANDLE threadObject DUMMY_INIT_THREAD;
#endif /* NONSCALAR_HANDLES */
	BOOLEAN semaphoreSet = FALSE;
	int status = CRYPT_OK;

	REQUIRES_B( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );
	REQUIRES_B( isEnumRange( semaphore, SEMAPHORE ) );

	/* If we're in a shutdown and the semaphores have been destroyed, don't
	   try and acquire the semaphore mutex.  In this case anything that 
	   they're protecting should be set to a shutdown state in which any 
	   access fails, so this isn't a problem */
	if( krnlData->shutdownLevel >= SHUTDOWN_LEVEL_MUTEXES )
		return( FALSE );

	/* Lock the semaphore table, extract the information that we need, and 
	   unlock it again */
	semaphoreInfo = &krnlData->semaphoreInfo[ semaphore ];
	MUTEX_LOCK( semaphore );
	if( semaphoreInfo->state == SEMAPHORE_STATE_SET )
		{
		/* Precondition: The reference count is valid.  Note that we have to
		   make this an assert() rather than a REQUIRES() because the latter
		   would exit with the semaphore still held */
		assert( semaphoreInfo->refCount >= 0 );

		/* Make sure that the lock count is valid.  This partly mirrors the
		   precondition but is mostly to catch excessively high lock counts.
		   We also have to check for one less than the isShortIntegerRange()
		   check because we're about to increment it */
		if( !isShortIntegerRange( semaphoreInfo->refCount ) || \
			semaphoreInfo->refCount >= MAX_INTLENGTH_SHORT - 1 )
			{
			DEBUG_DIAG(( "Semaphore lock count %d invalid", 
						 semaphoreInfo->refCount ));
			MUTEX_UNLOCK( semaphore );
			assert( DEBUG_WARN );
			return( FALSE );
			}

		/* The semaphore is set and not in use, extract the information we
		   require and mark it as being in use */
#ifdef NONSCALAR_HANDLES
		semaphoreObject = &semaphoreInfo->semaphoreObject;
		threadObject = &semaphoreInfo->threadObject;
#else
		semaphoreObject = semaphoreInfo->semaphoreObject;
		threadObject = semaphoreInfo->threadObject;
#endif /* NONSCALAR_HANDLES */
		REQUIRES_MUTEX_B( !checkOverflowInc( semaphoreInfo->refCount ),
						  semaphore );
		semaphoreInfo->refCount++;
		semaphoreSet = TRUE;
		}
	MUTEX_UNLOCK( semaphore );

	/* If the semaphore wasn't set or is in use, exit now */
	if( !semaphoreSet )
		return( TRUE );

	/* Wait on the object */
#ifdef NONSCALAR_HANDLES
	assert( memcmp( semaphoreObject, 
					&SEMAPHORE_INFO_TEMPLATE.semaphoreObject,
					sizeof( MUTEX_HANDLE ) ) );
#else
	assert( memcmp( &semaphoreObject, 
					&SEMAPHORE_INFO_TEMPLATE.semaphoreObject,
					sizeof( MUTEX_HANDLE ) ) );
#endif /* NONSCALAR_HANDLES */
	THREAD_WAIT( threadObject, semaphoreObject, status );
	if( cryptStatusError( status ) )
		{
		/* The wait failed, if it wasn't due to a shutdown in progress then 
		   we still have to reset the reference count that we incremented
		   earlier.  We also have to do this on state 
		   SEMAPHORE_STATE_PRECLEAR, which clearSemaphore() will move the 
		   semaphore into if it sees that it's set */
		if( krnlData->shutdownLevel >= SHUTDOWN_LEVEL_MUTEXES )
			return( FALSE );
		MUTEX_LOCK( semaphore );
		releaseRefOpt( semaphoreInfo );
		MUTEX_UNLOCK( semaphore );
		DEBUG_DIAG(( "Wait on object failed" ));
		assert( DEBUG_WARN );
		return( FALSE );
		}

	/* Since we can have waited for an arbitrary amount of time, another 
	   thread could have shut us down in the meantime so we perform another
	   shutdown check before trying to re-lock the semaphore table */
	if( krnlData->shutdownLevel >= SHUTDOWN_LEVEL_MUTEXES )
		{
		/* The return status is a bit of an odd one, we've waited on the 
		   semaphore but haven't updated the information, so the wait 
		   occurred but the overall operation didn't complete.  Returning 
		   TRUE is less wrong than returning FALSE */
		return( TRUE );
		}

	/* Lock the semaphore table, update the information, and unlock it
	   again */
	MUTEX_LOCK( semaphore );
	releaseRefOpt( semaphoreInfo );
	MUTEX_UNLOCK( semaphore );
	
	return( TRUE );
	}
#else

/* krnlWaitSemaphore() is only used if threading functions are enabled, 
   however this is an externally-visible API so we need to provide a dummy
   replacement for it as opposed to the kernel-internal setSemaphore()/
   clearSemaphore() which can be replaced with a #define */ 

CHECK_RETVAL_BOOL \
BOOLEAN krnlWaitSemaphore( IN_ENUM( SEMAPHORE ) const SEMAPHORE_TYPE semaphore )
	{
	return( TRUE );
	}
#endif /* USE_THREAD_FUNCTIONS */

/****************************************************************************
*																			*
*								Mutex Functions								*
*																			*
****************************************************************************/

/* Enter and exit a mutex */

CHECK_RETVAL \
int krnlEnterMutex( IN_ENUM( MUTEX ) const MUTEX_TYPE mutex )
	{
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );

	REQUIRES( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );
	REQUIRES( isEnumRange( mutex, MUTEX ) );

	/* If we're in a shutdown and the mutexes have been destroyed, don't
	   try and acquire them.  In this case anything that they're protecting
	   should be set to a shutdown state in which any access fails, so this
	   isn't a problem */
	if( krnlData->shutdownLevel >= SHUTDOWN_LEVEL_MUTEXES )
		return( CRYPT_ERROR_PERMISSION );

	switch( mutex )
		{
		case MUTEX_RANDOM:
			MUTEX_LOCK( mutex1 );
			break;

		case MUTEX_RANDOMNONCE:
			MUTEX_LOCK( mutex2 );
			break;

#ifdef USE_SESSIONS
		case MUTEX_SCOREBOARD:
			MUTEX_LOCK( mutex3 );
			break;
#endif /* USE_SESSIONS */

#ifdef USE_TCP
		case MUTEX_SOCKETPOOL:
			MUTEX_LOCK( mutex4 );
			break;
#endif /* USE_TCP */

#ifdef USE_SESSIONS
		case MUTEX_CRYPTODELAY:
			MUTEX_LOCK( mutex5 );
			break;
#endif /* USE_SESSIONS */

		default:
			retIntError();
		}

	return( CRYPT_OK );
	}

void krnlExitMutex( IN_ENUM( MUTEX ) const MUTEX_TYPE mutex )
	{	
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );

	REQUIRES_V( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );
	REQUIRES_V( isEnumRange( mutex, MUTEX ) );

	/* If we're in a shutdown and the mutexes have been destroyed, 
	   krnlEnterMutex() won't try and acquire them so we shouldn't be
	   releasing them */
	if( krnlData->shutdownLevel >= SHUTDOWN_LEVEL_MUTEXES )
		return;

	switch( mutex )
		{
		case MUTEX_RANDOM:
			MUTEX_UNLOCK( mutex1 );
			break;

		case MUTEX_RANDOMNONCE:
			MUTEX_UNLOCK( mutex2 );
			break;

#ifdef USE_SESSIONS
		case MUTEX_SCOREBOARD:
			MUTEX_UNLOCK( mutex3 );
			break;
#endif /* USE_SESSIONS */

#ifdef USE_TCP
		case MUTEX_SOCKETPOOL:
			MUTEX_UNLOCK( mutex4 );
			break;
#endif /* USE_TCP */

#ifdef USE_SESSIONS
		case MUTEX_CRYPTODELAY:
			MUTEX_UNLOCK( mutex5 );
			break;
#endif /* USE_SESSIONS */

		default:
			retIntError_Void();
		}
	}

/****************************************************************************
*																			*
*								Thread Functions							*
*																			*
****************************************************************************/

/* Execute a function in a background thread.  This takes a pointer to the 
   function to execute in the background thread and a semaphore ID to set 
   once the thread is started.  A function is run via a background thread as 
   follows:

	void threadFunction( const THREAD_PARAMS *threadParams )
		{
		}

	krnlDispatchThread( threadFunction, SEMAPHORE_ID ); */

#ifdef USE_THREAD_FUNCTIONS

/* The function that's run as a thread.  This calls the user-supplied
   service function with the user-supplied parameters.  The macro
   turns 'THREADFUNC_DEFINE( name, arg )' into 
   'RETURN_TYPE name( ARG_TYPE arg )', for example 
   'void *name( void *arg )' */

THREADFUNC_DEFINE( threadServiceFunction, threadInfoPtr )
	{
	const THREAD_INFO *threadInfo = ( const THREAD_INFO * ) threadInfoPtr;
	const THREAD_FUNCTION threadFunction = ( THREAD_FUNCTION ) \
							FNPTR_GET( threadInfo->threadFunction );
	ORIGINAL_INT_VAR( intParam, threadInfo->threadParams.intParam );
	ORIGINAL_INT_VAR( semaphore, threadInfo->semaphore );
		/* Note that the above two macros give initialised-but-not-
		   referenced warnings in release builds due to the assert() turning 
		   into a no-op */

	assert( isReadPtr( threadInfoPtr, sizeof( THREAD_INFO ) ) );

	if( threadFunction == NULL )
		{
		/* It's a bit unclear what we should do in this case since it's a 
		   shouldn't-occur condition, exiting now seems to be the least
		   unsafe action.  THREAD_EXIT() is a noreturn function so there's
		   no explicit return that follows it */
		clearSemaphore( threadInfo->semaphore );
		THREAD_EXIT( threadInfo->syncHandle );
		}

	/* We're running as a thread, call the thread service function and clear
	   the associated semaphore when we're done.  We check to make sure that 
	   the thread params are unchanged to catch erroneous use of stack-based 
	   storage for the parameter data.
	   
	   The conditional compile of the assert() is a bit awkward, if 
	   CONFIG_CONSERVE_MEMORY_EXTRA is enabled in debug mode then 
	   ORIGINAL_VALUE() becomes a no-op that we can't easily work around so 
	   we have to explicitly only enable the code if this isn't enabled */
	threadFunction( &threadInfo->threadParams );
#ifndef CONFIG_CONSERVE_MEMORY_EXTRA
	assert( threadInfo->threadParams.intParam == ORIGINAL_VALUE( intParam ) );
	assert( threadInfo->semaphore == ORIGINAL_VALUE( semaphore ) );
#endif /* !CONFIG_CONSERVE_MEMORY_EXTRA */
	clearSemaphore( threadInfo->semaphore );
	THREAD_EXIT( threadInfo->syncHandle );
	}

/* Dispatch a function in a background thread.  This is only called from the 
   init code for the threaded driver bind, so it uses the thread information
   storage in the kernel data */

CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
int krnlDispatchThread( THREAD_FUNCTION threadFunction,
						IN_ENUM( SEMAPHORE ) const SEMAPHORE_TYPE semaphore )
	{
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );
	THREAD_INFO *threadInfo = &krnlData->threadInfo;
	int status;

	/* Preconditions: The parameters appear valid */
	REQUIRES( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );
	REQUIRES( threadFunction != NULL );
	REQUIRES( isEnumRange( semaphore, SEMAPHORE ) );
	
	/* Initialise the thread parameters.  Only a single thread is ever 
	   created (see the comment above) so we only need a single fixed slot 
	   in the kernel data */
	memset( threadInfo, 0, sizeof( THREAD_INFO ) );
	FNPTR_SET( threadInfo->threadFunction, threadFunction );
	threadInfo->semaphore = semaphore;

	/* Fire up the thread and set the associated semaphore if required.
	   There's no problem with the thread exiting before we set the
	   semaphore because it's a one-shot, so if the thread gets there first
	   the attempt to set the semaphore below is ignored */
	THREAD_CREATE( threadServiceFunction, threadInfo, 
				   threadInfo->threadHandle, threadInfo->syncHandle, 
				   status );
	if( cryptStatusOK( status ) )
		{
		setSemaphore( semaphore, threadInfo->syncHandle, 
					  threadInfo->threadHandle );
		}
	return( status );
	}
#endif /* USE_THREAD_FUNCTIONS */
