/****************************************************************************
*																			*
*							Secure Memory Management						*
*						Copyright Peter Gutmann 1995-2025					*
*																			*
****************************************************************************/

#if defined( __STDC__ ) || defined( _MSC_VER )
  /* Needed for offsetof(), VC++ wasn't __STDC__ for a long time so we need 
     an explicit exception for that case */
  #include <stddef.h>
#endif /* __STDC__ || Visual Studio */
#if defined( INC_ALL )
  #include "crypt.h"
  #include "acl.h"
  #include "kernel.h"
#else
  #include "crypt.h"
  #include "kernel/acl.h"
  #include "kernel/kernel.h"
#endif /* Compiler-specific includes */

/* The minimum and maximum amount of secure memory that we can ever 
   allocate.  Contexts can include storage for scheduled keys so they
   can get quite large */

#define MIN_ALLOC_SIZE			8
#define MAX_ALLOC_SIZE			8192

/* Memory block flags.  These are:

	FLAG_LOCKED: The memory block has been page-locked to prevent it from 
			being swapped to disk and will need to be unlocked when it's 
			freed */

#define MEM_FLAG_NONE			0x00	/* No memory flag */
#define MEM_FLAG_LOCKED			0x01	/* Memory block is page-locked */
#define MEM_FLAG_MAX			0x01	/* Maximum possible flag value */

/* To support page locking and other administration tasks we need to store 
   some additional information with the memory block.  We do this by 
   reserving an extra memory block at the start of the allocated block and 
   saving the information there.

   The information stored in the extra block is flags that control the use
   of the memory block, the size of the block, and pointers to the next and 
   previous pointers in the list of allocated blocks (this is used by the 
   thread that walks the block list touching each one).  We also insert a 
   canary at the start and end of each allocated memory block to detect 
   memory overwrites and modification, which is just a checksum of the memory
   header that doubles as a canary (which also makes it somewhat 
   unpredictable).

   The resulting memory block looks as follows:

			External mem.ptr
					|						Canary
					v						  v
		+-------+---+-----------------------+---+
		| Hdr	|###| Memory				|###|
		+-------+---+-----------------------+---+
		^									^	|
		|<----------- memHdrPtr->size --------->|
		|									|
	memPtr (BYTE *)							|
	memHdrPtr (MEM_INFO_HDR *)		memTrlPtr (MEM_INFO_TRL *) */

typedef struct {
	SAFE_FLAGS flags;		/* Flags for this memory block.  The memory 
							   header is checksummed so we don't strictly
							   have to use safe flags, but we do it anyway
							   for appearances' sake */
	int size;				/* Size of the block, including the size
							   of the MEM_INFO_HEADER header and 
							   MEM_INFO_TRAILER trailer */
	DATAPTR prev, next;		/* Next, previous memory block */
	int checksum;			/* Header checksum+canary for spotting overwrites */
	} MEM_INFO_HEADER;

typedef struct {
	int checksum;			/* Memory block checksum or canary (= header chks) */
	} MEM_INFO_TRAILER;

#ifdef SYSTEM_64BIT
  #define MEM_ROUNDSIZE		16
#else
  #define MEM_ROUNDSIZE		8
#endif /* SYSTEM_64BIT */
#define MEM_INFO_HEADERSIZE	roundUp( sizeof( MEM_INFO_HEADER ), MEM_ROUNDSIZE )
#define MEM_INFO_TRAILERSIZE sizeof( MEM_INFO_TRAILER )

/****************************************************************************
*																			*
*						OS-Specific Nonpageable Allocators					*
*																			*
****************************************************************************/

/* Some OSes handle page-locking by explicitly locking an already-allocated
   address range, others require the use of a special allocate-nonpageable-
   memory function.  For the latter class we redefine the standard 
   clAlloc()/clFree() macros to use the appropriate OS-specific allocators */

#if defined( __BEOS__xxx )	/* See comment below */

/* BeOS' create_area(), like most of the low-level memory access functions 
   provided by different OSes, functions at the page level so we round the 
   size up to the page size.  We can mitigate the granularity somewhat by 
   specifying lazy locking, which means that the page isn't locked until it's 
   committed.

   In pre-open-source BeOS, areas were bit of a security tradeoff because 
   they were globally visible(!!!) through the use of find_area(), so that 
   any other process in the system could find them.  An attacker could 
   always find the app's malloc() arena anyway because of this, but putting 
   data directly into areas made the attacker's task somewhat easier.  Open-
   source BeOS fixed this, mostly because it would have taken extra work to 
   make areas explicitly globally visible and no-one could see a reason for 
   this, so it's somewhat safer there.

   However, the implementation of create_area() in the open-source BeOS 
   seems to be rather flaky (simply creating an area and then immediately 
   destroying it again causes a segmentation violation) so it may be 
   necessary to turn it off for some BeOS releases.
   
   In more recent open-source BeOS releases create_area() simply maps to
   mmap(), and that uses a function convert_area_protection_flags() to
   convert the BeOS to Posix flags which simply discards everything but
   AREA_READ, AREA_WRITE, and AREA_EXEC, so it appears that create_area()
   can no longer allocate non-pageable memory.  If the original behaviour is 
   ever restored then the code will need to be amended to add the following
   member to MEM_INFO_HEADER:

	area_id areaID;				// Needed for page locking under BeOS

   and save the areaID after the create_area() call:

	memHdrPtr->areaID = areaID; */

#define clAlloc( string, size )		beosAlloc( size )
#define clFree( string, memblock )	beosFree( memblock )

static void *beosAlloc( const int size )
	{ 
	void *memPtr = NULL; 
	area_id areaID; 

	areaID = create_area( "memory_block", &memPtr, B_ANY_ADDRESS,
						  roundUp( MEM_INFO_HEADERSIZE + size + \
								   MEM_INFO_TRAILERSIZE, B_PAGE_SIZE ),
						  B_LAZY_LOCK, B_READ_AREA | B_WRITE_AREA );
	if( areaID < B_NO_ERROR )
		return( NULL );

	return( memPtr );
	}

static void beosFree( void *memPtr )
	{
	MEM_INFO_HEADER *memHdrPtr = memPtr;
	area_id areaID; 

	areaID = memHdrPtr->areaID;
	REQUIRES( isIntegerRangeNZ( memHdrPtr->size ) ); 
	zeroise( memPtr, memHdrPtr->size );
	delete_area( areaID );
	}

#elif defined( __CHORUS__ )

/* ChorusOS is one of the very few embedded OSes with paging capabilities,
   fortunately there's a way to allocate nonpageable memory if paging is
   enabled */

#include <mem/chMem.h>

#define clAlloc( string, size )		chorusAlloc( size )
#define clFree( string, memblock )	chorusFree( memblock )

static void *chorusAlloc( const int size )
	{ 
	const int alignedSize = roundUp( size, MEM_ROUNDSIZE );
	const int memSize = MEM_INFO_HEADERSIZE + alignedSize + \
						MEM_INFO_TRAILERSIZE;
	KnRgnDesc rgnDesc = { K_ANYWHERE, memSize, K_WRITEABLE | K_NODEMAND };

	if( rgnAllocate( K_MYACTOR, &rgnDesc ) != K_OK )
		return( NULL );

	return( rgnDesc.startAddr );
	}

static void chorusFree( void *memPtr )
	{
	MEM_INFO_HEADER *memHdrPtr = memPtr;
	KnRgnDesc rgnDesc = { K_ANYWHERE, 0, 0 };

	rgnDesc.size = memHdrPtr->size;
	rgnDesc.startAddr = memPtr;
	REQUIRES( isIntegerRangeNZ( memHdrPtr->size ) ); 
	zeroise( memPtr, memHdrPtr->size );
	rgnFree( K_MYACTOR, &rgnDesc );
	}
#endif /* OS-specific nonpageable allocation handling */

/****************************************************************************
*																			*
*								Utility Functions							*
*																			*
****************************************************************************/

/* Calculate the checksum for a memory header block */

STDC_NONNULL_ARG( ( 1 ) ) \
static int checksumMemHdr( IN_PTR const MEM_INFO_HEADER *memHdrPtr )
	{
	return( \
		checksumData( memHdrPtr, offsetof( MEM_INFO_HEADER, checksum ) ) );
	}

/* Set the checksum for a block of memory */

STDC_NONNULL_ARG( ( 1 ) ) \
static void setMemChecksum( INOUT_PTR MEM_INFO_HEADER *memHdrPtr )
	{
	MEM_INFO_TRAILER *memTrlPtr;

	assert( isWritePtr( memHdrPtr, sizeof( MEM_INFO_HEADER ) ) );

	memHdrPtr->checksum = checksumMemHdr( memHdrPtr );
	memTrlPtr = ( MEM_INFO_TRAILER * ) \
				( ( BYTE * ) memHdrPtr + memHdrPtr->size - MEM_INFO_TRAILERSIZE );
	memTrlPtr->checksum = memHdrPtr->checksum;
	}

/* Sanity-check a memory block */

CHECK_RETVAL_BOOL STDC_NONNULL_ARG( ( 1 ) ) \
static BOOLEAN sanityCheckMemBlockHdr( IN_PTR const MEM_INFO_HEADER *memHdrPtr )
	{
	const MEM_INFO_TRAILER *memTrlPtr;
	int checksum;

	assert( isReadPtr( memHdrPtr, sizeof( MEM_INFO_HEADER ) ) );

	/* Make sure that the general header information is valid.  This is a 
	   quick check for obviously-invalid blocks, as well as ensuring that a 
	   corrupted size member doesn't result in us reading off into the 
	   weeds */
	if( memHdrPtr->size < MEM_INFO_HEADERSIZE + MIN_ALLOC_SIZE + \
						  MEM_INFO_TRAILERSIZE || \
		memHdrPtr->size > MEM_INFO_HEADERSIZE + MAX_ALLOC_SIZE + \
						  MEM_INFO_TRAILERSIZE )
		return( FALSE );
	if( !CHECK_FLAGS( memHdrPtr->flags, MEM_FLAG_NONE, 
					  MEM_FLAG_MAX ) )
		return( FALSE );

	/* Everything seems kosher so far, check that the header hasn't been 
	   altered */
	checksum = checksumMemHdr( memHdrPtr );
	if( checksum != memHdrPtr->checksum )
		return( FALSE );

	/* Check that the trailer hasn't been altered */
	memTrlPtr = ( MEM_INFO_TRAILER * ) \
				( ( BYTE * ) memHdrPtr + memHdrPtr->size - MEM_INFO_TRAILERSIZE );
	if( checksum != memTrlPtr->checksum )
		return( FALSE );
	
	return( TRUE );
	}

/* Insert and unlink a memory block from a list of memory blocks, with 
   appropriate updates of memory checksums and other information.  Because
   of this additional processing we can't use the standard 
   insertSingleListElement()/deleteSingleListElement() operations but have
   to do things explicitly.
   
   We keep the code for this in distinct functions to make sure that an 
   exception-condition doesn't force an exit without the memory mutex 
   unlocked */

CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 3 ) ) \
static int insertMemBlock( INOUT_PTR MEM_INFO_HEADER **allocatedListHeadPtr, 
						   INOUT_PTR MEM_INFO_HEADER **allocatedListTailPtr, 
						   INOUT_PTR MEM_INFO_HEADER *memHdrPtr )
	{
	MEM_INFO_HEADER *allocatedListHead = *allocatedListHeadPtr;
	MEM_INFO_HEADER *allocatedListTail = *allocatedListTailPtr;

	assert( isWritePtr( allocatedListHeadPtr, sizeof( MEM_INFO_HEADER * ) ) );
	assert( allocatedListHead == NULL || \
			isWritePtr( allocatedListHead, sizeof( MEM_INFO_HEADER ) ) );
	assert( isWritePtr( allocatedListTailPtr, sizeof( MEM_INFO_HEADER * ) ) );
	assert( allocatedListTail == NULL || \
			isWritePtr( allocatedListTail, sizeof( MEM_INFO_HEADER ) ) );
	assert( isWritePtr( memHdrPtr, sizeof( MEM_INFO_HEADER ) ) );

	/* Precondition: The memory block list is empty, or there's at least a 
	   one-entry list present */
	REQUIRES( ( allocatedListHead == NULL && allocatedListTail == NULL ) || \
			  ( allocatedListHead != NULL && allocatedListTail != NULL ) );

	/* If it's a new list, set up the head and tail pointers and return */
	if( allocatedListHead == NULL )
		{
		/* In yet another of gcc's endless supply of compiler bugs, if the
		   following two lines of code are combined into a single line then
		   the write to the first value, *allocatedListHeadPtr, ends up 
		   going to some arbitrary memory location and only the second
		   write goes to the correct location (completely different code is
		   generated for the two writes)  This leaves 
		   krnlData->allocatedListHead as a NULL pointer, leading to an
		   exception being triggered the next time that it's accessed */
#if defined( __GNUC__ ) && ( __GNUC__ == 4 )
		*allocatedListHeadPtr = memHdrPtr;
		*allocatedListTailPtr = memHdrPtr;
#else
		*allocatedListHeadPtr = *allocatedListTailPtr = memHdrPtr;
#endif /* gcc 4.x compiler bug */

		return( CRYPT_OK );
		}
	ENSURES( allocatedListHead != NULL && allocatedListTail != NULL );

	/* It's an existing list, add the new element to the end */
	REQUIRES( sanityCheckMemBlockHdr( allocatedListTail ) );
	DATAPTR_SET( allocatedListTail->next, memHdrPtr );
	setMemChecksum( allocatedListTail );
	DATAPTR_SET( memHdrPtr->prev, allocatedListTail );
	*allocatedListTailPtr = memHdrPtr;

	/* Postcondition: The new block has been linked into the end of the 
	   list */
	ENSURES( DATAPTR_GET( allocatedListTail->next ) == memHdrPtr && \
			 DATAPTR_GET( memHdrPtr->prev ) == allocatedListTail && \
			 DATAPTR_ISNULL( memHdrPtr->next ) );

	return( CRYPT_OK );
	}

CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 3 ) ) \
static int unlinkMemBlock( INOUT_PTR MEM_INFO_HEADER **allocatedListHeadPtr, 
						   INOUT_PTR MEM_INFO_HEADER **allocatedListTailPtr, 
						   INOUT_PTR MEM_INFO_HEADER *memHdrPtr )
	{
	MEM_INFO_HEADER *allocatedListHead = *allocatedListHeadPtr;
	MEM_INFO_HEADER *allocatedListTail = *allocatedListTailPtr;
	MEM_INFO_HEADER *nextBlockPtr = DATAPTR_GET( memHdrPtr->next );
	MEM_INFO_HEADER *prevBlockPtr = DATAPTR_GET( memHdrPtr->prev );

	assert( isWritePtr( allocatedListHeadPtr, sizeof( MEM_INFO_HEADER * ) ) );
	assert( allocatedListHead == NULL || \
			isWritePtr( allocatedListHead, sizeof( MEM_INFO_HEADER ) ) );
	assert( isWritePtr( allocatedListTailPtr, sizeof( MEM_INFO_HEADER * ) ) );
	assert( allocatedListTail == NULL || \
			isWritePtr( allocatedListTail, sizeof( MEM_INFO_HEADER ) ) );
	assert( isWritePtr( memHdrPtr, sizeof( MEM_INFO_HEADER ) ) );

	REQUIRES( DATAPTR_ISVALID( memHdrPtr->next ) );
	REQUIRES( DATAPTR_ISVALID( memHdrPtr->prev ) );

	/* Pre-validate everything (it's checked again below on a case-by-case 
	   basis to make what's going on explicit) before we try and modify 
	   things, so that a failure can't leave the list in an inconsistent 
	   state */
	if( prevBlockPtr != NULL )
		{
		REQUIRES( sanityCheckMemBlockHdr( prevBlockPtr ) );
		REQUIRES( DATAPTR_GET( prevBlockPtr->next ) == memHdrPtr );
		}
	if( nextBlockPtr != NULL )
		{
		REQUIRES( sanityCheckMemBlockHdr( nextBlockPtr ) );
		REQUIRES( DATAPTR_GET( nextBlockPtr->prev ) == memHdrPtr );
		}

	/* If we're removing the block from the start of the list, make the
	   start the next block */
	if( memHdrPtr == allocatedListHead )
		{
		REQUIRES( prevBlockPtr == NULL );

		*allocatedListHeadPtr = nextBlockPtr;
		}
	else
		{
		REQUIRES( prevBlockPtr != NULL && \
				  DATAPTR_GET( prevBlockPtr->next ) == memHdrPtr );

		/* Delete from the middle or end of the list */
		REQUIRES( sanityCheckMemBlockHdr( prevBlockPtr ) );
		DATAPTR_SET( prevBlockPtr->next, nextBlockPtr );
		setMemChecksum( prevBlockPtr );
		}
	if( nextBlockPtr != NULL )
		{
		REQUIRES( DATAPTR_GET( nextBlockPtr->prev ) == memHdrPtr );

		REQUIRES( sanityCheckMemBlockHdr( nextBlockPtr ) );
		DATAPTR_SET( nextBlockPtr->prev, prevBlockPtr );
		setMemChecksum( nextBlockPtr );
		}

	/* If we've removed the last element, update the end pointer */
	if( memHdrPtr == allocatedListTail )
		{
		REQUIRES( nextBlockPtr == NULL );

		*allocatedListTailPtr = prevBlockPtr;
		}

	/* Clear the current block's pointers, just to be clean */
	DATAPTR_SET( memHdrPtr->next, NULL );
	DATAPTR_SET( memHdrPtr->prev, NULL );

	return( CRYPT_OK );
	}

/* Some OSes handle memory locking on a per-page basis, which means that we
   can't unlock a block of memory without knowing that it doesn't share a
   page with another block of locked memory which would also be unlocked.
   The following helper function retrieves the size and address of each
   allocated block of memory to allow its presence in an about-to-be-
   unlocked page to be checked.  Note that one of these will be the address
   being unlocked, which has to be filtered out by the caller.
   
   If used, this is called from krnlMemfree() via 
   misc/os_spec.c:unlockMemory(), which means that the allocation mutex is 
   held throughout by krnlMemfree().  
   
   Currently only Windows uses this function */

#if defined( MEM_UNLOCK_REQUIRES_BLOCKLIST )

CHECK_RETVAL STDC_NONNULL_ARG( ( 2, 3 ) ) \
int getBlockListInfo( IN_PTR_OPT const void *currentBlockPtr, 
					  OUT_PTR_PTR_COND const void **address, 
					  OUT_LENGTH_Z int *size )
	{
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );
	const MEM_INFO_HEADER *currentBlock = currentBlockPtr;

	assert( ( currentBlockPtr == NULL ) || \
			isReadPtr( currentBlockPtr, sizeof( MEM_INFO_HEADER ) ) );
	assert( isReadPtr( address, sizeof( void * ) ) );
	assert( isWritePtr( size, sizeof( int ) ) );

	REQUIRES( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );
	REQUIRES( currentBlock == NULL || \
			  sanityCheckMemBlockHdr( currentBlock ) );

	/* Clear return values */
	*address = NULL;
	*size = 0;

	/* Get the first or next block in the list */
	if( currentBlock == NULL )
		currentBlock = DATAPTR_GET( krnlData->allocatedListHead );
	else
		currentBlock = DATAPTR_GET( currentBlock->next );
	if( currentBlock == NULL )
		return( CRYPT_ERROR_NOTFOUND );
	ENSURES( sanityCheckMemBlockHdr( currentBlock ) );

	*address = currentBlock;
	*size = currentBlock->size;

	return( CRYPT_OK );
	}
#endif /* MEM_UNLOCK_REQUIRES_BLOCKLIST */

/****************************************************************************
*																			*
*							Init/Shutdown Functions							*
*																			*
****************************************************************************/

/* Create and destroy the secure allocation information */

CHECK_RETVAL \
int initAllocation( void )
	{
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );
	int status;

	assert( isWritePtr( krnlData, sizeof( KERNEL_DATA ) ) );

	REQUIRES( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );

	/* Clear the allocated block list head and tail pointers */
	DATAPTR_SET( krnlData->allocatedListHead, NULL );
	DATAPTR_SET( krnlData->allocatedListTail, NULL );

	/* Initialize any data structures required to make the allocation thread-
	   safe */
	MUTEX_CREATE( allocation, status );
	ENSURES( cryptStatusOK( status ) );

	return( CRYPT_OK );
	}

void endAllocation( void )
	{
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );

	REQUIRES_V( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );

	/* Warn if there's still allocated memory blocks */
	if( DATAPTR_ISSET( krnlData->allocatedListHead ) || \
		DATAPTR_ISSET( krnlData->allocatedListTail ) )
		{
		DEBUG_DIAG(( "Kernel memory list still contains allocated blocks" ));
		assert( DEBUG_WARN );
		}

	/* Destroy any data structures required to make the allocation thread-
	   safe */
	MUTEX_DESTROY( allocation );
	}

/****************************************************************************
*																			*
*						Secure Memory Allocation Functions					*
*																			*
****************************************************************************/

/* A safe malloc function that performs page locking if possible */

CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
int krnlMemalloc( OUT_BUFFER_ALLOC_OPT( size ) void **pointer, 
				  IN_LENGTH int size )
	{
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );
	MEM_INFO_HEADER *allocatedListHeadPtr, *allocatedListTailPtr; 
	MEM_INFO_HEADER *memHdrPtr;
	BYTE *memPtr;
	BOOLEAN isLocked = FALSE;
	int alignedSize, memSize, status;

	static_assert( MEM_INFO_HEADERSIZE >= sizeof( MEM_INFO_HEADER ), \
				   "Memlock header size" );

	assert( isWritePtr( pointer, sizeof( void * ) ) );
	
	REQUIRES( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );
	REQUIRES( size >= MIN_ALLOC_SIZE && size <= MAX_ALLOC_SIZE );

	/* Now that we've checked everything, set up the various values that
	   we'll need */
	REQUIRES( !checkOverflowRoundup( size, MEM_ROUNDSIZE ) );
	alignedSize = roundUp( size, MEM_ROUNDSIZE );
	REQUIRES( !checkOverflowAdd( alignedSize, MEM_INFO_HEADERSIZE + \
											  MEM_INFO_TRAILERSIZE ) );
	memSize = MEM_INFO_HEADERSIZE + alignedSize + MEM_INFO_TRAILERSIZE;

	/* Clear return values */
	*pointer = NULL;

	/* Allocate and clear the memory */
	REQUIRES( isIntegerRangeNZ( memSize ) );
	if( ( memPtr = clAlloc( "krnlMemAlloc", memSize ) ) == NULL )
		return( CRYPT_ERROR_MEMORY );
	memset( memPtr, 0, memSize );

	/* Set up the memory block header and trailer */
	memHdrPtr = ( MEM_INFO_HEADER * ) memPtr;
	INIT_FLAGS( memHdrPtr->flags, MEM_FLAG_NONE );
	memHdrPtr->size = memSize;
	DATAPTR_SET( memHdrPtr->next, NULL );
	DATAPTR_SET( memHdrPtr->prev, NULL );

	/* Try to lock the pages in memory */
	if( lockMemory( memHdrPtr, memHdrPtr->size ) )
		{
		SET_FLAG( memHdrPtr->flags, MEM_FLAG_LOCKED );
		isLocked = TRUE;
		}

	/* Lock the memory list */
	MUTEX_LOCK( allocation );

	/* Check safe pointers */
	if( !DATAPTR_ISVALID( krnlData->allocatedListHead ) || \
		!DATAPTR_ISVALID( krnlData->allocatedListTail ) )
		{
		/* Since the block list isn't valid, we can only unlock the
		   memory block if it doesn't require the block list */
#ifndef MEM_UNLOCK_REQUIRES_BLOCKLIST
		if( isLocked )
			unlockMemory( memHdrPtr, memSize, TRUE );
#endif /* MEM_UNLOCK_REQUIRES_BLOCKLIST */
		MUTEX_UNLOCK( allocation );
		clFree( "krnlMemAlloc", memPtr );
		DEBUG_DIAG(( "Kernel memory data corrupted" ));
		retIntError();
		}

	/* Insert the new block into the list */
	allocatedListHeadPtr = DATAPTR_GET( krnlData->allocatedListHead );
	allocatedListTailPtr = DATAPTR_GET( krnlData->allocatedListTail );
	status = insertMemBlock( &allocatedListHeadPtr, &allocatedListTailPtr, 
							 memHdrPtr );
	if( cryptStatusError( status ) )
		{
		/* The insert failed in some way, the block list may or may not be 
		   valid but since the new block wasn't inserted we can just unlock
		   the memory block and free it again.  On systems where we need to
		   check getBlockListInfo() (only Windows) before unlocking this can 
		   in theory unlock another memory block on the same page, but 
		   that's better than slowly shrinking the working set over time.
		   In any case this is a should-not-occur condition so shouldn't
		   actually be an issue */
		if( isLocked )
			unlockMemory( memHdrPtr, memSize, TRUE );
		MUTEX_UNLOCK( allocation );
		clFree( "krnlMemAlloc", memPtr );
		DEBUG_DIAG(( "Kernel memory block insertion failed, status %d",
					 status ));
		retIntError();
		}
	DATAPTR_SET( krnlData->allocatedListHead, allocatedListHeadPtr );
	DATAPTR_SET( krnlData->allocatedListTail, allocatedListTailPtr );

	/* Calculate the checksums for the memory block */
	setMemChecksum( memHdrPtr );

	/* Perform heap sanity-checking if the functionality is available */
#ifdef USE_HEAP_CHECKING
	/* Sanity check to detect memory chain corruption */
	assert( _CrtIsValidHeapPointer( memHdrPtr ) );
	assert( DATAPTR_ISNULL( memHdrPtr->next ) );
	assert( DATAPTR_GET( krnlData->allocatedListHead ) == \
				DATAPTR_GET( krnlData->allocatedListTail ) || \
			_CrtIsValidHeapPointer( DATAPTR_GET( memHdrPtr->prev ) ) );
#endif /* USE_HEAP_CHECKING */

	MUTEX_UNLOCK( allocation );

	*pointer = memPtr + MEM_INFO_HEADERSIZE;

	return( CRYPT_OK );
	}

/* A safe free function that scrubs memory and zeroes the pointer.

	"You will softly and suddenly vanish away
	 And never be met with again"	- Lewis Carroll,
									  "The Hunting of the Snark" */

CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
int krnlMemfree( INOUT_PTR_PTR void **pointer )
	{
	KERNEL_DATA *krnlData = getSystemStorage( SYSTEM_STORAGE_KRNLDATA );
	MEM_INFO_HEADER *allocatedListHeadPtr, *allocatedListTailPtr; 
	MEM_INFO_HEADER *memHdrPtr;
	BYTE *memPtr;
	BOOLEAN isLocked;
	int size, status;

	assert( isReadPtr( pointer, sizeof( void * ) ) );
	assert( isReadPtr( *pointer, MIN_ALLOC_SIZE ) );

	REQUIRES( checkBuiltinStorage( SYSTEM_STORAGE_KRNLDATA ) );

	/* Recover the actual allocated memory block data from the pointer */
	memPtr = ( ( BYTE * ) *pointer ) - MEM_INFO_HEADERSIZE;
	if( !isReadPtr( memPtr, MEM_INFO_HEADERSIZE ) )
		retIntError();
	memHdrPtr = ( MEM_INFO_HEADER * ) memPtr;

	/* Lock the memory list */
	MUTEX_LOCK( allocation );

	/* Check safe pointers */
	if( !DATAPTR_ISVALID( krnlData->allocatedListHead ) || \
		!DATAPTR_ISVALID( krnlData->allocatedListTail ) )
		{
		MUTEX_UNLOCK( allocation );
		DEBUG_DIAG(( "Kernel memory data corrupted" ));
		retIntError();
		}

	/* Make sure that the memory header information and canaries are 
	   valid */
	if( !sanityCheckMemBlockHdr( memHdrPtr ) )
		{
		MUTEX_UNLOCK( allocation );

		/* The memory block doesn't look right, don't try and go any 
		   further */
		DEBUG_DIAG(( "Attempt to free invalid memory segment at %p inside "
					 "memory block at %p", *pointer, memHdrPtr ));
		retIntError();
		}

	/* Perform heap sanity-checking if the functionality is available */
#ifdef USE_HEAP_CHECKING
	/* Sanity check to detect memory chain corruption */
	assert( _CrtIsValidHeapPointer( memHdrPtr ) );
	assert( DATAPTR_ISNULL( memHdrPtr->next ) || \
			_CrtIsValidHeapPointer( DATAPTR_GET( memHdrPtr->next ) ) );
	assert( DATAPTR_ISNULL( memHdrPtr->prev ) || \
			_CrtIsValidHeapPointer( DATAPTR_GET( memHdrPtr->prev ) ) );
#endif /* USE_HEAP_CHECKING */

	/* Remember the memory block information that we'll need later */
	isLocked = TEST_FLAG( memHdrPtr->flags, MEM_FLAG_LOCKED ) ? \
			   TRUE : FALSE;
	size = memHdrPtr->size;

	/* Unlink the memory block from the list.  We continue if there's a 
	   problem with the unlink, which would indicate corruption in the block
	   list, because zeroising sensitive material takes precedence.  The
	   corruption will be detected through sanityCheckMemBlockHdr() and 
	   other checks, so it won't get any worse once it happens */
	allocatedListHeadPtr = DATAPTR_GET( krnlData->allocatedListHead );
	allocatedListTailPtr = DATAPTR_GET( krnlData->allocatedListTail );
	status = unlinkMemBlock( &allocatedListHeadPtr, &allocatedListTailPtr, 
							 memHdrPtr );
	if( cryptStatusError( status ) )
		{
		DEBUG_DIAG(( "Kernel memory block corruption detected" ));
		assert( DEBUG_WARN );
		if( allocatedListHeadPtr == memHdrPtr )
			{
			/* If the block that we've failed to unlink is the one at the 
			   start of the list, the best that we can do is clear the list 
			   since we're about to zeroise it which means that all further
			   accesses would fail */
			DATAPTR_SET( krnlData->allocatedListHead, NULL );
			DATAPTR_SET( krnlData->allocatedListTail, NULL );
			}
		}
	else
		{
		DATAPTR_SET( krnlData->allocatedListHead, allocatedListHeadPtr );
		DATAPTR_SET( krnlData->allocatedListTail, allocatedListTailPtr );
		}

	/* If we need the block list locked for unlockMemory(), we have to 
	   perform the unlock now.  This introduces a minute chance of a race
	   condition between the unlock and the zeroise below, but it's 
	   unlikely that we'll get paged out across three lines of code */
#ifdef MEM_UNLOCK_REQUIRES_BLOCKLIST
	if( isLocked )
		unlockMemory( memHdrPtr, size, TRUE );
#endif /* MEM_UNLOCK_REQUIRES_BLOCKLIST */

	MUTEX_UNLOCK( allocation );

	/* Zeroise the memory (including the memlock info), free it, and zero
	   the pointer.  There is one case where we can't free it and that's
	   when there's corruption in the memory block list, meaning that we
	   couldn't unlink the block from the list.  This is another can't-
	   occur condition because if the list has been corrupted then we can't
	   follow it any more so it won't matter if a link that we can't get
	   to is left pointing to freed memory, but overall it seems safer to
	   not free the memory (that the link doesn't reliably point to) than
	   to free it.
	   
	   Another option would be to set allocatedListHead and 
	   allocatedListTail to NULL, effectively clearing the memory block 
	   list */
	REQUIRES( isIntegerRangeNZ( size ) ); 
	zeroise( memPtr, size );
#ifndef MEM_UNLOCK_REQUIRES_BLOCKLIST
	if( isLocked )
		unlockMemory( memHdrPtr, size, TRUE );
#endif /* MEM_UNLOCK_REQUIRES_BLOCKLIST */
	if( cryptStatusOK( status ) )
		clFree( "krnlMemFree", memPtr );
	*pointer = NULL;

	return( status );
	}
