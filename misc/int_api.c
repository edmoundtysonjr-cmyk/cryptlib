/****************************************************************************
*																			*
*							cryptlib Internal API							*
*						Copyright Peter Gutmann 1992-2025					*
*																			*
****************************************************************************/

/* A generic module that implements a rug under which all problems not
   solved elsewhere are swept */

#if defined( INC_ALL )
  #include "crypt.h"
  #include "asn1.h"
  #include "asn1_ext.h"
  #include "stream.h"
#else
  #include "crypt.h"
  #include "enc_dec/asn1.h"
  #include "enc_dec/asn1_ext.h"
  #include "io/stream.h"
#endif /* Compiler-specific includes */

/* Emit a warning if TRUE was redefined.  We can't do this in the header 
   where the check is performed because it would produce a warning for every
   single file */

#if ( defined( _MSC_VER ) || defined( __GNUC__ ) || defined( __clang__ ) ) && \
	defined( TRUE_REDEFINED )
  #pragma message( "Warning: TRUE has been defined externally, redefining for cryptlib use." )
#endif /* TRUE_REDEFINED */

/* Perform a bounds check on pointers to blocks of memory, verifying that an
   inner block of memory is contained entirely within an outer block of 
   memory */

CHECK_RETVAL_BOOL \
BOOLEAN pointerBoundsCheck( IN_PTR_OPT const void *data,
							IN_LENGTH_Z const int dataLength,
							IN_PTR_OPT const void *innerData,
							IN_LENGTH_SHORT_Z const int innerDataLength )
	{
	REQUIRES_B( isIntegerRange( dataLength ) );
	REQUIRES_B( isShortIntegerRange( innerDataLength ) );

	/* Check for general problems with the parameters */
	if( ( data != NULL && dataLength <= 0 ) || \
		( data == NULL && dataLength > 0 ) )
		return( FALSE );
	if( ( innerData != NULL && innerDataLength <= 0 ) || \
		( innerData == NULL && innerDataLength > 0 ) )
		return( FALSE );

	assert( data == NULL || isReadPtrDynamic( data, dataLength ) );
	assert( innerData == NULL || \
			isReadPtrDynamic( innerData, innerDataLength ) );
	
	/* If there's no data present then there's nothing to check, although 
	   we do have to make sure that there's then no inner data present 
	   either */
	if( data == NULL )
		{
		if( innerData != NULL || innerDataLength != 0 )
			return( FALSE );

		return( TRUE );
		}

	/* If there's no inner data present then there's nothing to check */
	if( innerData == NULL )
		{
		/* This is already checked in the general parameter check above, but
		   we make it explicit here as well */
		REQUIRES_B( innerDataLength == 0 );

		return( TRUE );
		}

	/* Make sure that the inner data is contained within the outer data.  
	   This has to remain a best-effort check because the C standard says 
	   that comparing two values in the same linear address space is UB.
	   All known commercial compilers get this right, and so far even gcc
	   hasn't decided to take advantage of the standard allowing it to 
	   gratuitously break the code that implements this no-brainer check */
	if( ( const BYTE * ) innerData < ( const BYTE * ) data || \
		( ( const BYTE * ) innerData + innerDataLength > \
										( const BYTE * ) data + dataLength ) )
		return( FALSE );

	return( TRUE );
	}

/* Helper functions used to check that a sequence of CFI tokens have been 
   processed in order.  These are used both to ensure that inline macros to
   perform the CFI checking don't get too complex and to reduce the chances
   of a compiler being able to turn the CFI check into a compile-time 
   constant expression.
   
   These functions aren't decorated with attributes because they both take 
   and produce arbitrary-range integers.  They also don't check for 
   overflows and similar because it doesn't matter if a few bits get lost, 
   as long as the results are consistent */

#ifndef CONFIG_CONSERVE_MEMORY_EXTRA

CFI_CHECK_TYPE cfiCheckSequence3( const CFI_CHECK_TYPE initValue, 
								  const CFI_CHECK_TYPE label1Value,
								  const CFI_CHECK_TYPE label2Value, 
								  const CFI_CHECK_TYPE label3Value )
	{
	CFI_CHECK_TYPE cfiCheckValue = initValue;

	cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label1Value;
	if( label2Value != ( CFI_CHECK_TYPE ) -1 )
		cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label2Value;
	if( label3Value != ( CFI_CHECK_TYPE ) -1 )
		cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label3Value;

	return( cfiCheckValue );
	}

CFI_CHECK_TYPE cfiCheckSequence6( const CFI_CHECK_TYPE initValue, 
								  const CFI_CHECK_TYPE label1Value,
								  const CFI_CHECK_TYPE label2Value, 
								  const CFI_CHECK_TYPE label3Value,
								  const CFI_CHECK_TYPE label4Value,
								  const CFI_CHECK_TYPE label5Value,
								  const CFI_CHECK_TYPE label6Value )
	{
	CFI_CHECK_TYPE cfiCheckValue = initValue;

	cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label1Value;
	cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label2Value;
	cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label3Value;
	cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label4Value;
	if( label5Value != ( CFI_CHECK_TYPE ) -1 )
		cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label5Value;
	if( label6Value != ( CFI_CHECK_TYPE ) -1 )
		cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label6Value;

	return( cfiCheckValue );
	}

CFI_CHECK_TYPE cfiCheckSequence9( const CFI_CHECK_TYPE initValue, 
								  const CFI_CHECK_TYPE label1Value,
								  const CFI_CHECK_TYPE label2Value, 
								  const CFI_CHECK_TYPE label3Value,
								  const CFI_CHECK_TYPE label4Value,
								  const CFI_CHECK_TYPE label5Value,
								  const CFI_CHECK_TYPE label6Value,
								  const CFI_CHECK_TYPE label7Value,
								  const CFI_CHECK_TYPE label8Value,
								  const CFI_CHECK_TYPE label9Value )
	{
	CFI_CHECK_TYPE cfiCheckValue = initValue;

	cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label1Value;
	cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label2Value;
	cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label3Value;
	cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label4Value;
	cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label5Value;
	cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label6Value;
	cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label7Value;
	if( label8Value != ( CFI_CHECK_TYPE ) -1 )
		cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label8Value;
	if( label9Value != ( CFI_CHECK_TYPE ) -1 )
		cfiCheckValue = ( cfiCheckValue * CFI_PRIME ) + label9Value;

	return( cfiCheckValue );
	}
#endif /* !CONFIG_CONSERVE_MEMORY_EXTRA */

/* Copy a string attribute to external storage, with various range checks
   to follow the cryptlib semantics (these will already have been done by
   the caller, this is just a backup check).  There are two forms for this
   function, one that takes a MESSAGE_DATA parameter containing all of the 
   result parameters in one place and the other that takes distinct result
   parameters, typically because they've been passed down through several
   levels of function call beyond the point where they were in a 
   MESSAGE_DATA */

CHECK_RETVAL STDC_NONNULL_ARG( ( 3 ) ) \
int attributeCopyParams( OUT_BUFFER_OPT( destMaxLength, \
										 *destLength ) void *dest, 
						 IN_LENGTH_SHORT_Z const int destMaxLength, 
						 OUT_LENGTH_BOUNDED_SHORT_Z( destMaxLength ) \
							int *destLength, 
						 IN_BUFFER_OPT( sourceLength ) const void *source, 
						 IN_LENGTH_SHORT_Z const int sourceLength )
	{
	assert( ( dest == NULL && destMaxLength == 0 ) || \
			( isWritePtrDynamic( dest, destMaxLength ) ) );
	assert( isWritePtr( destLength, sizeof( int ) ) );
	assert( ( source == NULL && sourceLength == 0 ) || \
			isReadPtrDynamic( source, sourceLength ) );

	REQUIRES( ( dest == NULL && destMaxLength == 0 ) || \
			  ( dest != NULL && \
				isShortIntegerRangeNZ( destMaxLength ) ) );
	REQUIRES( ( source == NULL && sourceLength == 0 ) || \
			  ( source != NULL && \
			    isShortIntegerRangeNZ( sourceLength ) ) );

	/* Clear return values */
	*destLength = 0;
	if( dest != NULL )
		memset( dest, 0, min( 16, destMaxLength ) );

	if( sourceLength <= 0 )
		return( CRYPT_ERROR_NOTFOUND );
	ENSURES( source != NULL );
	if( dest != NULL )
		{
		assert( isReadPtrDynamic( source, sourceLength ) );

		if( sourceLength > destMaxLength || \
			!isWritePtrDynamic( dest, sourceLength ) )
			return( CRYPT_ERROR_OVERFLOW );
		REQUIRES( rangeCheck( sourceLength, 1, destMaxLength ) );
		memcpy( dest, source, sourceLength );
		}
	*destLength = sourceLength;

	return( CRYPT_OK );
	}

CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2 ) ) \
int attributeCopy( INOUT_PTR MESSAGE_DATA *msgData, 
				   IN_BUFFER( attributeLength ) const void *attribute, 
				   IN_LENGTH_SHORT const int attributeLength )
	{
	assert( isWritePtr( msgData, sizeof( MESSAGE_DATA ) ) );
	assert( isReadPtrDynamic( attribute, attributeLength ) );

	REQUIRES( ( msgData->data == NULL && \
				msgData->length == 0 ) || \
			  ( msgData->data != NULL && \
				isShortIntegerRangeNZ( msgData->length ) ) );
	REQUIRES( isShortIntegerRangeNZ( attributeLength ) );

	return( attributeCopyParams( msgData->data, msgData->length, 
								 &msgData->length, attribute, 
								 attributeLength ) );
	}

/* Check whether a given algorithm is available */

CHECK_RETVAL_BOOL \
BOOLEAN algoAvailable( IN_ALGO const CRYPT_ALGO_TYPE cryptAlgo )
	{
	CRYPT_QUERY_INFO queryInfo;

	REQUIRES_B( isEnumRange( cryptAlgo, CRYPT_ALGO ) );

	/* Short-circuit check for frequently-queried and/or always-available 
	   algorithms */
	switch( cryptAlgo )
		{
		/* The kernel won't initialise without the symmetric and hash 
		   algorithms being present (SHA-x implies HMAC-SHAx) so it's safe 
		   to hardcode them in here */
		case CRYPT_ALGO_AES:
		case CRYPT_ALGO_SHA1:
		case CRYPT_ALGO_HMAC_SHA1:
		case CRYPT_ALGO_SHA2:
		case CRYPT_ALGO_HMAC_SHA2:
			return( TRUE );
			
		/* Frequently-queried algorithms.  These are present as native
		   implementations but may not be present if a custom hardware 
		   profile is being used */
#if !defined( CONFIG_CRYPTO_HW1 ) && !defined( CONFIG_CRYPTO_HW2 )
		case CRYPT_ALGO_RSA:
  #ifdef USE_ECDSA
		case CRYPT_ALGO_ECDSA:
  #endif /* USE_ECDSA */
  #ifdef USE_3DES
		case CRYPT_ALGO_3DES:
  #endif /* USE_3DES */
			return( TRUE );
#endif /* !CONFIG_CRYPTO_HW1 && !CONFIG_CRYPTO_HW2 */

		default:
			/* Everything else ends up here and gets routed via the (slower) 
			   kernel check */
			break;
		}
		
	return( cryptStatusOK( krnlSendMessage( SYSTEM_OBJECT_HANDLE,
									IMESSAGE_DEV_QUERYCAPABILITY, &queryInfo,
									cryptAlgo ) ) ? TRUE : FALSE );
	}

/* For a given hash algorithm pair, check whether the first is stronger than 
   the second.  The order is:

	SNAng > SHA2 > SHA-1 > all others */

CHECK_RETVAL_BOOL \
BOOLEAN isStrongerHash( IN_ALGO const CRYPT_ALGO_TYPE algorithm1,
						IN_ALGO const CRYPT_ALGO_TYPE algorithm2 )
	{
	static const CRYPT_ALGO_TYPE algoPrecedence[] = {
		CRYPT_ALGO_SHAng, CRYPT_ALGO_SHA2, CRYPT_ALGO_SHA1, 
		CRYPT_ALGO_NONE, CRYPT_ALGO_NONE };
	LOOP_INDEX algo1index, algo2index;

	REQUIRES_B( isHashAlgo( algorithm1 ) );
	REQUIRES_B( isHashAlgo( algorithm2 ) );

	/* Find the relative positions on the scale of the two algorithms */
	LOOP_SMALL( algo1index = 0, 
				algo1index < FAILSAFE_ARRAYSIZE( algoPrecedence, \
												 CRYPT_ALGO_TYPE ) && \
						algoPrecedence[ algo1index ] != algorithm1,
				algo1index++ )
		{
		ENSURES_B( LOOP_INVARIANT_SMALL( algo1index, 0, 
										 FAILSAFE_ARRAYSIZE( algoPrecedence, \
															 CRYPT_ALGO_TYPE ) - 1 ) );

		/* If we've reached an unrated algorithm, it can't be stronger than 
		   the other one */
		if( algoPrecedence[ algo1index ] == CRYPT_ALGO_NONE )
			return( FALSE );
		}
	ENSURES_B( LOOP_BOUND_OK );
	ENSURES_B( algo1index < FAILSAFE_ARRAYSIZE( algoPrecedence, \
												CRYPT_ALGO_TYPE ) );
	LOOP_SMALL( algo2index = 0, 
				algo2index < FAILSAFE_ARRAYSIZE( algoPrecedence, \
												 CRYPT_ALGO_TYPE ) && \
						algoPrecedence[ algo2index ] != algorithm2,
				algo2index++ )
		{
		ENSURES_B( LOOP_INVARIANT_SMALL( algo2index, 0, 
										 FAILSAFE_ARRAYSIZE( algoPrecedence, \
															 CRYPT_ALGO_TYPE ) - 1 ) );

		/* If we've reached an unrated algorithm, it's weaker than the other 
		   one */
		if( algoPrecedence[ algo2index ] == CRYPT_ALGO_NONE )
			return( TRUE );
		}
	ENSURES_B( LOOP_BOUND_OK );
	ENSURES_B( algo2index < FAILSAFE_ARRAYSIZE( algoPrecedence, \
												CRYPT_ALGO_TYPE ) );

	/* If the first algorithm has a smaller index than the second, it's a
	   stronger algorithm */
	return( ( algo1index < algo2index ) ? TRUE : FALSE );
	}

/* Return a random small positive integer.  This is used to perform 
   lightweight randomisation of various algorithms in order to make DoS 
   attacks harder.  Because of this the values don't have to be 
   cryptographically strong, so all that we do is cache the data from 
   CRYPT_IATTRIBUTE_RANDOM_NONCE and pull out a small integer's worth on 
   each call.  For the same reason, we don't care that the function isn't
   thread-safe (and in any case cryptlib is very rarely run non-single-
   threaded) */

#define RANDOM_BUFFER_SIZE	64

CHECK_RETVAL_RANGE_NOERROR( 0, 32767 ) \
int getRandomInteger( void )
	{
	static BYTE nonceData[ RANDOM_BUFFER_SIZE + 8 ];
	static int nonceIndex = 0;
	int returnValue, status;

	REQUIRES_EXT( rangeCheck( nonceIndex, 0, RANDOM_BUFFER_SIZE - 2 ), 0 );
				  /* -2 because we're reading two bytes at a time */
	REQUIRES_EXT( !( nonceIndex & 1 ), 0 );

	/* Initialise/reinitialise the nonce data if necessary.  See the long 
	   comment for getNonce() in system.c for the reason why we don't bail 
	   out on error but continue with a lower-quality generator */
	if( nonceIndex <= 0 )
		{
		MESSAGE_DATA msgData;

		setMessageData( &msgData, nonceData, RANDOM_BUFFER_SIZE );
		status = krnlSendMessage( SYSTEM_OBJECT_HANDLE,
								  IMESSAGE_GETATTRIBUTE_S, &msgData,
								  CRYPT_IATTRIBUTE_RANDOM_NONCE );
		if( cryptStatusError( status ) )
			return( ( int ) getTime( GETTIME_NOFAIL ) & 0x7FFF );
		}

	/* Extract the next random integer value from the buffered data.  We're
	   only extracting 16 bits so we don't have to bother with 
	   checkOverflowShift() */
	returnValue = ( byteToInt( nonceData[ nonceIndex ] ) << 8 ) | \
					byteToInt( nonceData[ nonceIndex + 1 ] );
	nonceIndex = ( nonceIndex + 2 ) % RANDOM_BUFFER_SIZE;
	ENSURES_EXT( rangeCheck( nonceIndex, 0, RANDOM_BUFFER_SIZE - 2 ), 0 );

	/* Return the value constrained to lie within the range 0...32767 */
	return( returnValue & 0x7FFF );
	}

/* Map one value to another, used to map values from one representation 
   (e.g. PGP algorithms or HMAC algorithms) to another (cryptlib algorithms
   or the underlying hash used for the HMAC algorithm) */

CHECK_RETVAL STDC_NONNULL_ARG( ( 2, 3 ) ) \
int mapValue( IN_INT_SHORT_Z const int srcValue,
			  OUT_INT_SHORT_Z int *destValue,
			  IN_ARRAY( mapTblSize ) const MAP_TABLE *mapTbl,
			  IN_RANGE( 1, 100 ) const int mapTblSize )
	{
	LOOP_INDEX i;

	assert( isWritePtr( destValue, sizeof( int ) ) );
	assert( isReadPtr( mapTbl, mapTblSize * sizeof( MAP_TABLE ) ) );

	REQUIRES( isShortIntegerRange( srcValue ) );
	REQUIRES( mapTblSize >= 1 && mapTblSize <= 100 );
	REQUIRES( mapTbl[ mapTblSize - 1 ].source == CRYPT_ERROR );

	/* Clear return value */
	*destValue = 0;

	/* Convert the given value into the equivalent mapped value */
	LOOP_MED( i = 0, 
			  i < mapTblSize && mapTbl[ i ].source != CRYPT_ERROR, 
			  i++ )
		{
		ENSURES( LOOP_INVARIANT_MED( i, 0, mapTblSize - 1 ) );

		if( mapTbl[ i ].source == srcValue )
			{
			*destValue = mapTbl[ i ].destination;

			return( CRYPT_OK );
			}
		}
	ENSURES( LOOP_BOUND_OK );
	ENSURES( i < mapTblSize );

	return( CRYPT_ERROR_NOTAVAIL );
	}

#ifdef USE_ERRMSGS

/* Map an object type to a string description of the type, used for printing
   diagnostic messages.  Note that the end-of-table delimiter is 0, not 
   CRYPT_ERROR, since one of the object types whose name we need to look up 
   is status values */

CHECK_RETVAL_PTR_NONNULL STDC_NONNULL_ARG( ( 1 ) ) \
const char *getObjectName( IN_ARRAY( objectNameInfoSize ) \
								const OBJECT_NAME_INFO *objectNameInfo,
						   IN_LENGTH_SHORT const int objectNameInfoSize,
						   const int objectType )
	{
	LOOP_INDEX i;

	assert( isReadPtr( objectNameInfo, 
					   sizeof( OBJECT_NAME_INFO ) * objectNameInfoSize ) );

	REQUIRES_EXT( isShortIntegerRange( objectNameInfoSize ),
				  "<Internal error>" );

	LOOP_LARGE( i = 0,
				i < objectNameInfoSize && \
					objectNameInfo[ i ].objectType != objectType && \
					objectNameInfo[ i ].objectType != 0,
				i++ )
		{
		ENSURES_EXT( LOOP_INVARIANT_LARGE( i, 0, objectNameInfoSize - 1 ),
					 "<Internal error>" );
		}
	ENSURES_EXT( LOOP_BOUND_OK, "<Internal error>" );
	ENSURES_EXT( i < objectNameInfoSize, "<Internal error>" );
	ENSURES_EXT( objectNameInfo[ i ].objectName != NULL, 
				 "<Internal error>" );

	return( objectNameInfo[ i ].objectName );
	}
#endif /* USE_ERRMSGS */

/****************************************************************************
*																			*
*							Data-checking Functions							*
*																			*
****************************************************************************/

/* Perform the FIPS-140 statistical checks that are feasible on a byte
   string.  The full suite of tests assumes that an infinite source of
   values (and time) is available, the following is a scaled-down version
   used to sanity-check keys and other short random data blocks.  Note that
   this check requires at least 64 bits of data in order to produce useful
   results */

CHECK_RETVAL_BOOL STDC_NONNULL_ARG( ( 1 ) ) \
static BOOLEAN checkNontrivialKey( IN_BUFFER( dataLength ) const BYTE *data, 
								   IN_LENGTH_SHORT_MIN( MIN_KEYSIZE ) \
										const int dataLength )
	{
	LOOP_INDEX i;
	int count = 0;

	REQUIRES_B( isShortIntegerRangeMin( dataLength, MIN_KEYSIZE ) );

	/* Check that it's not just a text string */
	LOOP_LARGE( i = 0, i < dataLength, i++	)
		{
		ENSURES_B( LOOP_INVARIANT_LARGE( i, 0, dataLength - 1 ) );

		if( !isAlNum( byteToInt( data[ i ] ) ) )
			break;
		}
	ENSURES_B( LOOP_BOUND_OK );
	if( i >= dataLength )
		return( FALSE );

	/* Check for a run of more than 64 bits of identical or near-identical 
	   values.  This isn't detected by checkEntropy() because it looks at
	   the overall entropy, not localised blocks of low entropy.
	   
	   The lower bound of 64 bits of identical values is for the fixed DH 
	   values which have all ones in the MSB and LSB */
	LOOP_LARGE( i = 1, i < dataLength, i++ )
		{
		ENSURES_B( LOOP_INVARIANT_LARGE( i, 1, dataLength - 1 ) );
		
		if( abs( data[ i ] - data[ i - 1 ] ) <= 8 )
			{
			count++;
			if( count > 8 )
				return( FALSE );
			}
		else
			{
			count = 0;
			}
		}
	ENSURES_B( LOOP_BOUND_OK );

	return( TRUE );
	}

CHECK_RETVAL_BOOL STDC_NONNULL_ARG( ( 1 ) ) \
BOOLEAN checkEntropy( IN_BUFFER( dataLength ) const BYTE *data, 
					  IN_LENGTH_SHORT_MIN( MIN_KEYSIZE ) const int dataLength )
	{
	const int minCount = dataLength / 4;
	LOOP_INDEX i;
	int bitCount[ 4 + 8 ], noOnes, errorCount = 0;

	assert( isReadPtrDynamic( data, dataLength ) );

	REQUIRES_B( isShortIntegerRangeMin( dataLength, MIN_KEYSIZE ) );

	/* Make sure that we haven't been given an obviously non-random key */
	if( !checkNontrivialKey( data, dataLength ) )
		return( FALSE );

	/* Count the number of two-bit pairs in each byte, giving a total of
	   ( 4 * dataLength ) samples */
	memset( bitCount, 0, 4 * sizeof( int ) );
	LOOP_LARGE( i = 0, i < dataLength, i++ )
		{
		int value;

		ENSURES_B( LOOP_INVARIANT_LARGE( i, 0, dataLength - 1 ) );

		value = byteToInt( data[ i ] );
		bitCount[ value & 3 ]++;
		bitCount[ ( value >> 2 ) & 3 ]++;
		bitCount[ ( value >> 4 ) & 3 ]++;
		bitCount[ ( value >> 6 ) & 3 ]++;
		}
	ENSURES_B( LOOP_BOUND_OK );

	/* Monobit test: Make sure that at least 1/4 of the bits are ones and 1/4
	   are zeroes */
	noOnes = bitCount[ 1 ] + bitCount[ 2 ] + ( 2 * bitCount[ 3 ] );
	if( noOnes < dataLength * 2 || noOnes > dataLength * 6 )
		{
		zeroise( bitCount, 4 * sizeof( int ) );
		return( FALSE );
		}

	/* Poker test (almost): Make sure that each bit pair is present at least
	   1/16 of the time.  The FIPS 140 version uses 4-bit values but the
	   number of samples available from the keys is far too small for this so
	   we can only use 2-bit values.  The FP rate for this for minimum-length
	   values of 128 bits is P( bitCount[ n ] <= 3 ) ~= 0.002% per bin and
	   ~0.007% per key across all the bins */	
	LOOP_SMALL( i = 0, i < 4, i++ )
		{
		ENSURES_B( LOOP_INVARIANT_SMALL( i, 0, 3 ) );

		if( bitCount[ i ] < minCount )
			errorCount++;
		}
	ENSURES_B( LOOP_BOUND_OK );
	zeroise( bitCount, 4 * sizeof( int ) );

	return( ( errorCount > 0 ) ? FALSE : TRUE );
	}

/* Check a bignum for suspicious patterns.  This is very vaguely-defined and 
   is only enabled in debug mode to prevent false positives, for now all that
   we do is the basic entropy check applied to all keys */

#ifndef NDEBUG

CHECK_RETVAL_BOOL STDC_NONNULL_ARG( ( 1 ) ) \
BOOLEAN checkEntropyInteger( IN_BUFFER( length ) const BYTE *buffer, 
							 IN_LENGTH_PKC_Z const int length )
	{
	assert( isReadPtrDynamic( buffer, length ) );

	REQUIRES_B( length >= 0 && length <= CRYPT_MAX_PKCSIZE );

	/* If the data amount is too small to be able to draw any conclusions 
	   from it, don't try and perform any checking */
	if( length < MIN_KEYSIZE )
		return( TRUE );

	/* Perform a basic entropy check */
	if( !checkEntropy( buffer, length ) )
		return( FALSE );

	/* Optional further checks here */

	return( TRUE );
	}
#endif /* !NDEBUG */

/* Check whether a block of 64 bits of data is all-zeroes, used for sanity-
   check functions that check contexts for validity so the usage
   is checking whether { data[], length } is all-zero.  Because of this the 
   length value provided to this function isn't the length of the data being 
   provided, which is fixed at 8 bytes, but the length value that the caller 
   has for the data.  If it's nonzero then we don't check the data contents, 
   only if it's zero do we go on to check whether the data it's matched with 
   is also zero */

CHECK_RETVAL_BOOL STDC_NONNULL_ARG( ( 1 ) ) \
BOOLEAN isEmptyData( IN_BUFFER_C( 8 ) const BYTE data[ 8 ],
					 IN_LENGTH_SHORT_Z const int dataLengthValue )
	{
	assert( isReadPtr( data, 8 ) );

	REQUIRES_B( isShortIntegerRange( dataLengthValue ) );

	/* Perform a quick-reject check before calling the more expensive
	   memcmp() */
	if( dataLengthValue != 0 || data[ 0 ] != 0x00 )
		return( FALSE );

	/* Check whether the first 64 bits are zero */
	return( memcmp( data, "\x00\x00\x00\x00\x00\x00\x00\x00", 8 ) ? \
			FALSE : TRUE );
	}

/* When we're comparing two cryptographic values, for example two MAC 
   values, and the developer's been careful to implement things really 
   badly, it may be possible to use a timing attack to guess a MAC value a
   byte at a time by using a high-resolution timer to check at which byte
   the memcmp() exits, thus guessing the MAC value a byte at a time in the
   same way that the old TENEX password-guessing bug worked.
   
   This seems highly unlikely given that cryptlib implementations of 
   protocols won't allow themselves to be used as an oracle in this manner 
   and for someone using cryptlib to implement their own protocol the 
   overhead of a trip through the kernel will mask out a few clock cycles of 
   difference in the memcmp() at the end, but we defend against it anyway 
   because no doubt someone will eventually publish a CERT advisory on it 
   being a problem in some app somewhere.  Note that we explicitly return 
   TRUE or FALSE since calling functions explicitly check for a return value 
   of TRUE rather than just zero/non-zero.
   
   Test for compiler mangling with the following, with -O it produces code
   as expected, with -O2/O3 it produces an incomprehensible mass of SSE 
   instructions:

	int compare( const void *src, const void *dest, const int length )
		{
		const unsigned char *srcPtr = src, *destPtr = dest;
		int value = 0, i;

		for( i = 0; i < length; i++ )
			value |= srcPtr[ i ] ^ destPtr[ i ];

		return( value ? 0x12345 : 0 );
		} 

   Note that this function has different semantics than memcmp(), returning 
   a pure boolean TRUE = same, FALSE = not the same */

CHECK_RETVAL_BOOL STDC_NONNULL_ARG( ( 1, 2 ) ) \
BOOLEAN compareDataConstTime( IN_BUFFER( length ) const void *src,
							  IN_BUFFER( length ) const void *dest,
							  IN_LENGTH_SHORT const int length )
	{
	const BYTE *srcPtr = src, *destPtr = dest;
	LOOP_INDEX i;
	int value = 0;

	assert( isReadPtrDynamic( src, length ) );
	assert( isReadPtrDynamic( dest, length ) );

	REQUIRES_B( isShortIntegerRangeNZ( length ) );

	/* Compare the two values in a time-independent manner */
	LOOP_MAX( i = 0, i < length, i++ )
		{
		ENSURES_B( LOOP_INVARIANT_MAX( i, 0, length - 1 ) );

		value |= srcPtr[ i ] ^ destPtr[ i ];
		}
	ENSURES_B( LOOP_BOUND_OK );

	return( value ? FALSE : TRUE );
	}

/* Check for a block of zeroes in a time-independent manner.  This is used 
   to check bignum values for suspicious amounts of leading zeroes, typically
   (ECD)DH outputs to make sure that an attacker hasn't forced us into a 
   small subrange of values.

   Test for compiler mangling with the following, with -O it produces code
   as expected, with -O2/O3 it produces an incomprehensible mass of SSE 
   instructions:

	int check( const void *data, const int length )
		{
		const unsigned char *dataPtr = data;
		int value = 0, i;

		for( i = 0; i < length; i++ )
			value |= dataPtr[ i ];

		return( value ? 0 : 0x12345 );
		} */

CHECK_RETVAL_BOOL STDC_NONNULL_ARG( ( 1 ) ) \
BOOLEAN checkZeroConstTime( IN_BUFFER( length ) const void *data,
							IN_LENGTH_SHORT const int length )
	{
	const BYTE *dataPtr = data;
	LOOP_INDEX i;
	int value = 0;

	assert( isReadPtrDynamic( data, length ) );

	REQUIRES_EXT( isShortIntegerRangeNZ( length ), TRUE );

	LOOP_MAX( i = 0, i < length, i++ )
		{
		ENSURES_EXT( LOOP_INVARIANT_MAX( i, 0, length - 1 ), TRUE );

		value |= dataPtr[ i ];
		}
	ENSURES_EXT( LOOP_BOUND_OK, TRUE );

	return( value ? FALSE : TRUE );
	}

/****************************************************************************
*																			*
*							Checksum/Hash Functions							*
*																			*
****************************************************************************/

/* Calculate a Fowler/Noll/Vo FNV-1a checksum (hash) as per RFC 9923.  As per 
   the RFC "their good dispersion makes them particularly well suited for 
   hashing nearly identical strings" which is exactly what we'd get in the
   presence of bit flips and similar corruption.  It truncates (slightly) the
   result to fit an integer but this isn't a big deal since all we need is 
   consistent results for identical data, the value itself is never 
   communicated externally.
   
   In the few cases where it's used in critical checks it's merely used as 
   a quick pre-check for a full hash-based check, so it doesn't have to be 
   perfect.  In addition it's not in any way cryptographically secure for 
   the same reason, there's no particular need for it to have that 
   property */

#if UINT_MAX > 0xFFFFFFFFUL
  #define FNV1A_INIT	0xCBF29CE484222325ULL
  #define FNV_PRIME		0x100000001B3ULL
#else
  #define FNV1A_INIT	0x811C9DC5
  #define FNV_PRIME		0x01000193
#endif /* 32 vs. 64-bit int */

RETVAL_RANGE( 0, INT_MAX ) STDC_NONNULL_ARG( ( 1 ) ) \
int checksumDataExt( IN_BUFFER( dataLength ) const void *data,
					 IN_DATALENGTH const int dataLength,
					 const unsigned int initialValue )
	{
	const BYTE *dataPtr = data;
	LOOP_INDEX i;
	unsigned int hashValue = \
					( initialValue == CHECKSUMDATA_INIT_VALUE ) ? \
					  FNV1A_INIT : initialValue;

	assert( isReadPtrDynamic( data, dataLength ) );

	REQUIRES( data != NULL );
	REQUIRES( isBufsizeRangeNZ( dataLength ) );

	LOOP_MAX( i = 0, i < dataLength, i++ )
		{
		ENSURES( LOOP_INVARIANT_MAX( i, 0, dataLength - 1 ) );

		hashValue ^= byteToInt( dataPtr[ i ] );
		hashValue *= FNV_PRIME;
		}
	ENSURES( LOOP_BOUND_OK );

	return( hashValue & INT_MAX );
	}

RETVAL_RANGE( 0, INT_MAX ) STDC_NONNULL_ARG( ( 1 ) ) \
int checksumData( IN_BUFFER( dataLength ) const void *data,
				  IN_DATALENGTH const int dataLength )
	{
	return( checksumDataExt( data, dataLength, 
							 CHECKSUMDATA_INIT_VALUE ) );
	}

/* Calculate the hash of a block of data.  We use SHA-1 because it's the 
   built-in default, but any algorithm will do since we're only using it
   to transform a variable-length value to a fixed-length one for easy
   comparison purposes */

STDC_NONNULL_ARG( ( 1, 3 ) ) \
void hashData( OUT_BUFFER_FIXED( hashMaxLength ) BYTE *hash, 
			   IN_LENGTH_HASH const int hashMaxLength, 
			   IN_BUFFER( dataLength ) const void *data, 
			   IN_DATALENGTH const int dataLength )
	{
	HASH_FUNCTION_ATOMIC hashFunctionAtomic = NULL;
	BYTE hashBuffer[ CRYPT_MAX_HASHSIZE + 8 ];
	int hashSize = 0;

	assert( isWritePtrDynamic( hash, hashMaxLength ) );
	assert( hashMaxLength >= MIN_HASHSIZE && \
			hashMaxLength <= CRYPT_MAX_HASHSIZE );
	assert( isReadPtrDynamic( data, dataLength ) );
	assert( isBufsizeRangeNZ( dataLength ) );

	/* Get the hash algorithm information necessary.  
	   getHashAtomicParameters() always initialises its output parameters so 
	   the setting to dummy values above is just to keep code analysers 
	   happy */
	getHashAtomicParameters( CRYPT_ALGO_SHA1, 0, &hashFunctionAtomic, 
							 &hashSize );

	/* Error handling: If there's a problem, return a zero hash.  We use 
	   this strategy since this is a void function and so the usual 
	   REQUIRES() predicate won't be effective.  Note that this can lead to 
	   a false-positive match if we're called multiple times with invalid 
	   input, in theory we could fill the return buffer with nonce data to 
	   ensure that we never get a false-positive match but since this is a 
	   should-never-occur condition anyway it's not certain whether forcing 
	   a match or forcing a non-match is the preferred behaviour */
	if( data == NULL || !isBufsizeRangeNZ( dataLength ) || \
		hashMaxLength < MIN_HASHSIZE || hashMaxLength > hashSize || \
		hashMaxLength > CRYPT_MAX_HASHSIZE || hashFunctionAtomic == NULL )
		{
		if( hashMaxLength < MIN_HASHSIZE || \
			hashMaxLength > CRYPT_MAX_HASHSIZE )
			{
			/* This is a shouldn't-occur on top of a shouldn't-occur, the 
			   best that we can do is zero at least 64 bits */
			ENSURES_V( isShortIntegerRangeNZ( hashMaxLength ) );
			memset( hash, 0, min( 8, hashMaxLength ) );
			}
		else
			{
			REQUIRES_V( isShortIntegerRangeNZ( hashMaxLength ) ); 
			memset( hash, 0, hashMaxLength );
			}
		retIntError_Void();
		}

	/* Hash the data and copy as many bytes as the caller has requested to
	   the output.  Typically they'll require only a subset of the full 
	   amount since all that we're doing is transforming a variable-length
	   value to a fixed-length value for easy comparison purposes */
	hashFunctionAtomic( hashBuffer, hashSize, data, dataLength );
	REQUIRES_V( rangeCheck( hashMaxLength, 1, hashSize ) );
	memcpy( hash, hashBuffer, hashMaxLength );
	REQUIRES_V( isShortIntegerRangeNZ( hashSize ) ); 
	zeroise( hashBuffer, hashSize );
	}

/****************************************************************************
*																			*
*							Stream Export/Import Routines					*
*																			*
****************************************************************************/

/* Export attribute or certificate data to a stream.  In theory we would
   have to export this via a dynbuf and then write it to the stream but we 
   can save some overhead by writing it directly to the stream's buffer.
   
   Some attributes have a user-defined size (e.g. 
   CRYPT_IATTRIBUTE_RANDOM_NONCE) so we allow the caller to specify an 
   optional length parameter indicating how much of the attribute should be 
   exported */

CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
static int exportAttr( INOUT_PTR STREAM *stream, 
					   IN_HANDLE const CRYPT_HANDLE cryptHandle,
					   IN_ATTRIBUTE const CRYPT_ATTRIBUTE_TYPE attributeType,
					   IN_LENGTH_INDEF const int length )
							/* Declared as LENGTH_INDEF because SHORT_INDEF
							   doesn't make sense */
	{
	MESSAGE_DATA msgData;
	void *dataPtr = NULL;
	int attrLength = 0, status;

	assert( isWritePtr( stream, sizeof( STREAM ) ) );
	assert( sStatusOK( stream ) );

	REQUIRES( cryptHandle == SYSTEM_OBJECT_HANDLE || \
			  isHandleRangeValid( cryptHandle ) );
	REQUIRES( isAttribute( attributeType ) || \
			  isInternalAttribute( attributeType ) );
	REQUIRES( ( length == CRYPT_UNUSED ) || \
			  isShortIntegerRangeMin( length, 8 ) );

	/* Get access to the stream buffer if required.  If it's a size check 
	   via a NULL stream then we continue with msgData = { NULL, 0 } */
	if( !sIsNullStream( stream ) )
		{
		if( length != CRYPT_UNUSED )
			{
			/* It's an explicit-length attribute, make sure that there's 
			   enough room left in the stream for it */
			attrLength = length;
			status = sMemGetDataBlock( stream, &dataPtr, length );
			}
		else
			{
			/* It's an implicit-length attribute whose maximum length is 
			   defined by the stream size */
			status = sMemGetDataBlockRemaining( stream, &dataPtr, 
												&attrLength );
			}
		if( cryptStatusError( status ) )
			return( status );
		}

	/* Export the attribute directly into the stream buffer */
	setMessageData( &msgData, dataPtr, 
					min( attrLength, MAX_INTLENGTH_SHORT - 1 ) );
	status = krnlSendMessage( cryptHandle, IMESSAGE_GETATTRIBUTE_S,
							  &msgData, attributeType );
	if( cryptStatusOK( status ) )
		status = sExtend( stream, msgData.length, SSKIP_MAX );
	return( status );
	}

CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
int exportAttributeToStream( INOUT_PTR TYPECAST( STREAM * ) struct ST *streamPtr, 
							 IN_HANDLE const CRYPT_HANDLE cryptHandle,
							 IN_ATTRIBUTE \
								const CRYPT_ATTRIBUTE_TYPE attributeType )
	{
	assert( isWritePtr( streamPtr, sizeof( STREAM ) ) );

	REQUIRES( isHandleRangeValid( cryptHandle ) );
	REQUIRES( isAttribute( attributeType ) || \
			  isInternalAttribute( attributeType ) );

	return( exportAttr( streamPtr, cryptHandle, attributeType, \
						CRYPT_UNUSED ) );
	}

CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
int exportVarsizeAttributeToStream( INOUT_PTR TYPECAST( STREAM * ) struct ST *streamPtr,
									IN_HANDLE const CRYPT_HANDLE cryptHandle,
									IN_LENGTH_FIXED( CRYPT_IATTRIBUTE_RANDOM_NONCE ) \
										const CRYPT_ATTRIBUTE_TYPE attributeType,
									IN_RANGE( 8, MAX_ATTRIBUTE_SIZE ) \
										const int attributeDataLength )
	{
	assert( isWritePtr( streamPtr, sizeof( STREAM ) ) );

	REQUIRES( cryptHandle == SYSTEM_OBJECT_HANDLE );
	REQUIRES( attributeType == CRYPT_IATTRIBUTE_RANDOM_NONCE );
	REQUIRES( attributeDataLength >= 8 && \
			  attributeDataLength <= MAX_ATTRIBUTE_SIZE );

	return( exportAttr( streamPtr, cryptHandle, attributeType, 
						attributeDataLength ) );
	}

CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
int exportCertToStream( INOUT_PTR TYPECAST( STREAM * ) struct ST *streamPtr,
						IN_HANDLE const CRYPT_CERTIFICATE cryptCertificate,
						IN_ENUM( CRYPT_CERTFORMAT ) \
							const CRYPT_CERTFORMAT_TYPE certFormatType )
	{
	MESSAGE_DATA msgData;
	STREAM *stream = streamPtr;
	void *dataPtr = NULL;
	int length = 0, status;

	assert( isWritePtr( stream, sizeof( STREAM ) ) );
	assert( sStatusOK( stream ) );

	REQUIRES( isHandleRangeValid( cryptCertificate ) );
	REQUIRES( isEnumRange( certFormatType, CRYPT_CERTFORMAT ) );

	/* Get access to the stream buffer if required */
	if( !sIsNullStream( stream ) )
		{
		status = sMemGetDataBlockRemaining( stream, &dataPtr, &length );
		if( cryptStatusError( status ) )
			return( status );
		}

	/* Export the certificate directly into the stream buffer */
	setMessageData( &msgData, dataPtr, length );
	status = krnlSendMessage( cryptCertificate, IMESSAGE_CRT_EXPORT,
							  &msgData, certFormatType );
	if( cryptStatusOK( status ) )
		status = sExtend( stream, msgData.length, SSKIP_MAX );
	return( status );
	}

CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 7 ) ) \
int importCertFromStream( INOUT_PTR TYPECAST( STREAM * ) struct ST *streamPtr,
						  OUT_HANDLE_OPT CRYPT_CERTIFICATE *cryptCertificate,
						  IN_HANDLE const CRYPT_USER iCryptOwner,
						  IN_ENUM( CRYPT_CERTTYPE ) \
							const CRYPT_CERTTYPE_TYPE certType, 
						  IN_LENGTH_SHORT_MIN( MIN_CRYPT_OBJECTSIZE ) \
							const int certDataLength,
						  IN_FLAGS_Z( KEYMGMT ) const int options,
						  INOUT_PTR ERROR_INFO *errorInfo )
	{
	MESSAGE_CREATEOBJECT_INFO createInfo;
	STREAM *stream = streamPtr;
	void *dataPtr;
	int status;

	assert( isWritePtr( stream, sizeof( STREAM ) ) );
	assert( sStatusOK( stream ) );
	assert( isWritePtr( cryptCertificate, sizeof( CRYPT_CERTIFICATE ) ) );
	assert( isWritePtr( errorInfo, sizeof( ERROR_INFO ) ) );

	REQUIRES( iCryptOwner == DEFAULTUSER_OBJECT_HANDLE || \
			  isHandleRangeValid( iCryptOwner ) );
	REQUIRES( isEnumRange( certType, CRYPT_CERTTYPE ) );
	REQUIRES( isShortIntegerRangeMin( certDataLength, \
									  MIN_CRYPT_OBJECTSIZE ) );
	REQUIRES( isFlagRangeZ( options, KEYMGMT ) && \
			  ( options & ~KEYMGMT_FLAG_DATAONLY_CERT ) == 0 );

	/* Clear return value */
	*cryptCertificate = CRYPT_ERROR;

	/* Get access to the stream buffer and skip over the certificate data */
	status = sMemGetDataBlock( stream, &dataPtr, certDataLength );
	if( cryptStatusOK( status ) )
		status = sSkip( stream, certDataLength, SSKIP_MAX );
	if( cryptStatusError( status ) )
		return( status );

	/* Import the certificate directly from the stream buffer */
	setMessageCreateObjectIndirectInfoEx( &createInfo, dataPtr, 
						certDataLength, certType,
						( options & KEYMGMT_FLAG_DATAONLY_CERT ) ? \
							KEYMGMT_FLAG_DATAONLY_CERT : KEYMGMT_FLAG_NONE,
						errorInfo );
	createInfo.cryptOwner = iCryptOwner;
	status = krnlSendMessage( SYSTEM_OBJECT_HANDLE,
							  IMESSAGE_DEV_CREATEOBJECT_INDIRECT,
							  &createInfo, OBJECT_TYPE_CERTIFICATE );
	if( cryptStatusError( status ) )
		return( status );

	*cryptCertificate = createInfo.cryptHandle;

	return( CRYPT_OK );
	}

/****************************************************************************
*																			*
*							Public-key Import Routines						*
*																			*
****************************************************************************/

#ifdef USE_INT_ASN1

/* Read a public key from an X.509 SubjectPublicKeyInfo record, creating the
   context necessary to contain it in the process.  This is used by a variety
   of modules including certificate-management, keysets, and crypto devices */

CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
static int checkKeyLength( INOUT_PTR STREAM *stream,
						   IN_ALGO const CRYPT_ALGO_TYPE cryptAlgo,
						   IN_BOOL const BOOLEAN hasAlgoParameters )
	{
	const int startPos = stell( stream );
	int keyLength, status;

	assert( isWritePtr( stream, sizeof( STREAM ) ) );

	REQUIRES( isPkcAlgo( cryptAlgo ) );
	REQUIRES( isBooleanValue( hasAlgoParameters ) );
	REQUIRES( isIntegerRangeNZ( startPos ) );

	/* The Bernstein algorithms use a fixed-length encoding so we just check
	   that the key has the correct length */
	if( isBernsteinAlgo( cryptAlgo ) )
		{
		status = readBitStringHole( stream, &keyLength, 
									MIN_PKCSIZE_BERNSTEIN, DEFAULT_TAG );
		if( cryptStatusOK( status ) && keyLength != MIN_PKCSIZE_BERNSTEIN )
			status = CRYPT_ERROR_NOSECURE;
		if( cryptStatusError( status ) )
			return( status );

		return( sseek( stream, startPos ) );
		}

	/* ECC algorithms are a complete mess to handle because of the arbitrary
	   manner in which the algorithm parameters can be represented.  To deal 
	   with this we skip the (always-present) parameters and read the public 
	   key value, which is a point on a curve stuffed in a variety of 
	   creative ways into an BIT STRING.  Since this contains two values 
	   (the x and y coordinates) we divide the lengths used by two to get an 
	   approximation of the nominal key size */
	if( isEccAlgo( cryptAlgo ) )
		{
		if( !hasAlgoParameters )
			return( CRYPT_ERROR_BADDATA );
		readUniversal( stream );	/* Skip algorithm parameters */
		status = readBitStringHole( stream, &keyLength, 
									MIN_PKCSIZE_ECCPOINT_THRESHOLD, 
									DEFAULT_TAG );
		if( cryptStatusOK( status ) && \
			( checkOverflowDiv( keyLength, 2 ) || \
			  isShortECCKey( keyLength / 2 ) ) )
			status = CRYPT_ERROR_NOSECURE;
		if( cryptStatusError( status ) )
			return( status );

		return( sseek( stream, startPos ) );
		}

	/* Read the key component that defines the nominal key size, either the 
	   first algorithm parameter or the first public-key component */
	if( hasAlgoParameters )
		{
		readSequence( stream, NULL );
		status = readGenericHole( stream, &keyLength, MIN_PKCSIZE_THRESHOLD, 
								  BER_INTEGER );
		}
	else
		{
		readBitStringHole( stream, NULL, MIN_PKCSIZE_THRESHOLD, DEFAULT_TAG );
		readSequence( stream, NULL );
		status = readGenericHole( stream, &keyLength, MIN_PKCSIZE_THRESHOLD, 
								  BER_INTEGER );
		}
	if( cryptStatusError( status ) )
		return( status );

	/* Check whether the nominal keysize is within the range defined as 
	   being a weak key */
	if( isShortPKCKey( keyLength ) )
		return( CRYPT_ERROR_NOSECURE );

	return( sseek( stream, startPos ) );
	}

CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2 ) ) \
int iCryptReadSubjectPublicKey( INOUT_PTR TYPECAST( STREAM * ) struct ST *streamPtr, 
								OUT_HANDLE_OPT CRYPT_CONTEXT *iPubkeyContext,
								IN_HANDLE const CRYPT_DEVICE iCreatorHandle, 
								IN_BOOL const BOOLEAN deferredLoad )
	{
	CRYPT_ALGO_TYPE cryptAlgo;
	CRYPT_CONTEXT iCryptContext;
	MESSAGE_CREATEOBJECT_INFO createInfo;
	MESSAGE_DATA msgData;
	STREAM *stream = streamPtr;
	ALGOID_PARAMS algoIDparams;
	void *spkiPtr DUMMY_INIT_PTR;
	const int startPos = stell( stream );
	int spkiLength, position, status;

	assert( isWritePtr( stream, sizeof( STREAM ) ) );
	assert( isWritePtr( iPubkeyContext, sizeof( CRYPT_CONTEXT ) ) );

#if defined( CONFIG_CRYPTO_HW1 ) || defined( CONFIG_CRYPTO_HW2 )
	REQUIRES( iCreatorHandle == SYSTEM_OBJECT_HANDLE || \
			  iCreatorHandle == CRYPTO_OBJECT_HANDLE || \
			  isHandleRangeValid( iCreatorHandle ) );
#else
	REQUIRES( iCreatorHandle == SYSTEM_OBJECT_HANDLE || \
			  isHandleRangeValid( iCreatorHandle ) );
#endif /* CONFIG_CRYPTO_HW1 || CONFIG_CRYPTO_HW2 */
	REQUIRES( isBooleanValue( deferredLoad ) );
	REQUIRES( isIntegerRange( startPos ) );

	/* Clear return value */
	*iPubkeyContext = CRYPT_ERROR;

	/* Pre-parse the SubjectPublicKeyInfo, both to ensure that it's (at 
	   least generally) valid before we go to the extent of creating an 
	   encryption context to contain it and to get access to the 
	   SubjectPublicKeyInfo data and algorithm information.  Because all 
	   sorts of bizarre tagging exist due to things like CRMF we read the 
	   wrapper as a generic hole rather than the more obvious SEQUENCE */
	status = getStreamObjectLength( stream, &spkiLength, 16 );
	if( cryptStatusOK( status ) )
		status = sMemGetDataBlock( stream, &spkiPtr, spkiLength );
	if( cryptStatusOK( status ) )
		{
		status = readGenericHole( stream, NULL, 
								  MIN_PKCSIZE_ECCPOINT_THRESHOLD, 
								  DEFAULT_TAG );
		}
	if( cryptStatusError( status ) )
		return( status );
	status = readAlgoIDex( stream, &cryptAlgo, &algoIDparams, 
						   ALGOID_CLASS_PKC );
	if( cryptStatusError( status ) )
		return( status );

	/* Perform minimal key-length checking.  We need to do this at this 
	   point (rather than having it done implicitly in the 
	   SubjectPublicKeyInfo read code) because a too-short key (or at least 
	   too-short key data) will result in the kernel rejecting the 
	   SubjectPublicKeyInfo before it can be processed, leading to a rather 
	   misleading CRYPT_ERROR_BADDATA return status rather than the correct 
	   CRYPT_ERROR_NOSECURE */
	status = checkKeyLength( stream, cryptAlgo,
							 ( algoIDparams.extraLength > 0 ) ? \
							   TRUE : FALSE );
	if( cryptStatusError( status ) )
		return( status );

	/* Skip the remainder of the key components in the stream, first the
	   algorithm parameters (if there are any) and then the public-key 
	   data */
	if( algoIDparams.extraLength > 0 )
		readUniversal( stream );
	status = readUniversal( stream );
	if( cryptStatusError( status ) )
		return( status );

	/* Since we're doing a direct import of a memory block, make sure that 
	   the claimed object length as given in the wrapper matches the actual 
	   payload length */
	position = stell( stream );
	REQUIRES( isIntegerRangeNZ( position ) );
	if( checkOverflowSub( position, startPos ) || \
		position - startPos != spkiLength )
		return( CRYPT_ERROR_BADDATA );

	/* Create the public-key context and send the key data to it */
	setMessageCreateObjectInfo( &createInfo, cryptAlgo );
	status = krnlSendMessage( iCreatorHandle, IMESSAGE_DEV_CREATEOBJECT, 
							  &createInfo, OBJECT_TYPE_CONTEXT );
	if( cryptStatusError( status ) )
		return( status );
	iCryptContext = createInfo.cryptHandle;
	setMessageData( &msgData, spkiPtr, spkiLength );
	status = krnlSendMessage( iCryptContext, IMESSAGE_SETATTRIBUTE_S, 
							  &msgData, deferredLoad ? \
								CRYPT_IATTRIBUTE_KEY_SPKI_PARTIAL : \
								CRYPT_IATTRIBUTE_KEY_SPKI );
	if( cryptStatusError( status ) )
		{
		krnlSendNotifier( iCryptContext, IMESSAGE_DECREFCOUNT );
		if( status == CRYPT_ARGERROR_STR1 || \
			status == CRYPT_ARGERROR_NUM1 )
			{
			/* If the key data was rejected by the kernel before it got to 
			   the SubjectPublicKeyInfo read code (see the comment above) 
			   then it'll be rejected with an argument-error code, which we
			   have to convert to a bad-data error before returning it to 
			   the caller */
			return( CRYPT_ERROR_BADDATA );
			}
		if( cryptArgError( status ) )
			{
			DEBUG_DIAG(( "Public-key load returned argError status %d",
						 status ));
			assert( DEBUG_WARN );
			status = CRYPT_ERROR_BADDATA;
			}
		return( status );
		}
	*iPubkeyContext = iCryptContext;
	assert( !checkContextCapability( iCryptContext, 
									 MESSAGE_CHECK_PKC_PRIVATE ) );

	return( CRYPT_OK );
	}
#endif /* USE_INT_ASN1 */

/****************************************************************************
*																			*
*							Safe Text-line Read Functions					*
*																			*
****************************************************************************/

#if defined( USE_HTTP ) || defined( USE_BASE64 ) || \
	defined( USE_SCEP ) || defined( USE_SSH )

/* The maximum number of characters that we'll read, to handle DoS attacks.  
   If we see more than MAX_LINE_LENGTH characters in a line we bail out */

#define MAX_LINE_LENGTH		4096

/* Handle error reporting.  The extra level of indirection provided by this 
   function is necessary because the the extended error information isn't 
   accessible from outside the stream code so we can't set it in the usual 
   manner via a retExt().  Instead we call retExtFn() directly and then pass 
   the result down to the stream layer via an ioctl */

CHECK_RETVAL_ERROR STDC_NONNULL_ARG( ( 1, 2 ) ) \
static int exitTextLineError( INOUT_PTR STREAM *stream,
							  FORMAT_STRING const char *format, 
							  const int value1, const int value2,
							  OUT_OPT_BOOL BOOLEAN *localError,
							  IN_ERROR const int status )
	{
	ERROR_INFO localErrorInfo;

	assert( isWritePtr( stream, sizeof( STREAM ) ) );
	assert( isReadPtr( format, 4 ) );
	assert( localError == NULL || \
			isWritePtr( localError, sizeof( BOOLEAN ) ) );

	REQUIRES( cryptStatusError( status ) );

	/* If the stream doesn't support extended error information, we're 
	   done */
	if( localError == NULL )
		return( status );

	/* The CRYPT_ERROR_BADDATA is a dummy code used in order to be able to 
	   call retExtFn() to format the error string */
	clearErrorInfo( &localErrorInfo );
	*localError = TRUE;
#ifdef USE_ERRMSGS
	( void ) retExtFn( CRYPT_ERROR_BADDATA, &localErrorInfo, format, 
					   value1, value2 );	/* Fill in localErrorInfo */
#endif /* USE_ERRMSGS */
	sioctlSetString( stream, STREAM_IOCTL_ERRORINFO, &localErrorInfo, 
					 sizeof( ERROR_INFO ) );

	return( status );
	}

CHECK_RETVAL_ERROR STDC_NONNULL_ARG( ( 1 ) ) \
static int exitInvalidChar( INOUT_PTR STREAM *stream,
							IN_BYTE const int ch, 
							IN_LENGTH_SHORT const int position,
							OUT_OPT_BOOL BOOLEAN *localError )
	{
	assert( isWritePtr( stream, sizeof( STREAM ) ) );
	assert( localError == NULL || \
			isWritePtr( localError, sizeof( BOOLEAN ) ) );

	REQUIRES( rangeCheck( ch, 0, 0xFF ) );

	return( exitTextLineError( stream, "Invalid character 0x%02X at "
							   "position %d", ch, position, localError,
							   CRYPT_ERROR_BADDATA ) );
	}

CHECK_RETVAL_ERROR STDC_NONNULL_ARG( ( 1 ) ) \
static int exitUnderflow( INOUT_PTR STREAM *stream,
						  IN_LENGTH_SHORT const int position,
						  OUT_OPT_BOOL BOOLEAN *localError )
	{
	assert( isWritePtr( stream, sizeof( STREAM ) ) );
	assert( localError == NULL || \
			isWritePtr( localError, sizeof( BOOLEAN ) ) );

	return( exitTextLineError( stream, "Ran out of input at position %d, "
							   "expected further text", position, 0, 
							   localError, CRYPT_ERROR_UNDERFLOW ) );
	}

/* sgetc() only works on file and memory streams so we have to emulate a 
   network-stream sgetc() here.  We check for potential zero-length reads, 
   which shouldn't actually occur because they'll be converted into an error 
   status but in theory there are some special-case conditions where we 
   could make the stream nonblocking and/or allow partial reads for 
   speculative read-ahead where this could lead to a zero-byte read count.  
   This shouldn't actually happen to a stream on which readTextLine() is 
   called but to be safe we catch and convert the condition into an error */

CHECK_RETVAL_RANGE( 0, 255 ) STDC_NONNULL_ARG( ( 1 ) ) \
static int networkReadCharFunction( INOUT_PTR TYPECAST( STREAM * ) \
										struct ST *streamPtr )
	{
	STREAM *stream = streamPtr;
	BYTE ch;
	int length, status;

	assert( isWritePtr( stream, sizeof( STREAM ) ) );

	status = length = sread( stream, &ch, 1 );
	if( cryptStatusError( status ) )
		return( status );
	return( ( length <= 0 ) ? CRYPT_ERROR_READ : byteToInt( ch ) );
	}

/* Categorise a character into one of the classes that the parsing FSM 
   accepts.  Check the FSM_STATE_TYPE definition and FSM tables before 
   modifying the enum list */

typedef enum {
	CHAR_CLASS_NONE,		/* No character class */
	CHAR_CLASS_TEXT,		/* Text character */
	CHAR_CLASS_WS,			/* Whitespace */
	CHAR_CLASS_CONT,		/* Continuation character ';' */
	CHAR_CLASS_CR,			/* CR */
	CHAR_CLASS_LF,			/* LF */
	CHAR_CLASS_EOF,			/* EOF */
	CHAR_CLASS_ERROR,		/* Invalid character */
	CHAR_CLASS_LAST			/* Last possible character class */
	} CHAR_CLASS_TYPE;

CHECK_RETVAL_ENUM( CHAR_CLASS ) \
static CHAR_CLASS_TYPE getCharClass( IN_BYTE const int ch )
	{
	REQUIRES_EXT( rangeCheck( ch, 0, 0xFF ), CHAR_CLASS_ERROR );
	
	switch( ch )
		{
		case ';':
			return( CHAR_CLASS_CONT );
		
		case '\r':
			return( CHAR_CLASS_CR );
		
		case '\n':
			return( CHAR_CLASS_LF );
		
		case ' ':
		case '\t':
			/* We can't use isspace() for this because it includes all sorts 
			   of extra control characters that we don't want to allow, and 
			   no doubt there'll be locale-dependent interpretations that 
			   allow lowercase tabs and spaces with umlauts */
			return( CHAR_CLASS_WS );
			
		default:
			/* We add an extra guard around the entry-point to 
			   isValidTextChar() to catch wildy out-of-range values */
			if( ch < ' ' || ch > 0x7F )
				return( CHAR_CLASS_ERROR );
			if( isValidTextChar( ch ) )
				return( CHAR_CLASS_TEXT );
			return( CHAR_CLASS_ERROR );
		}
	
	retIntError_Ext( CHAR_CLASS_ERROR );
	}

/* The FSM state tables used to parse text lines.  We have to make the 
   states zero-based so that they can be used to index the FSM tables.  
   Notes on specific states:

	FSM_WS_SKIP: Used to skip leading whitespace.

	FSM_WS: Used to skip inline repeated whitespace.

	FSM_CR: Can only be followed by a LF or EOF */

typedef enum {
	FSM_STATE_NONE, 
	
	/* Standard FSM states */
	FSM_START = FSM_STATE_NONE, 
					/* Initial state, can't be moved to by the FSM */
	FSM_TEXT,		/* Record char, go to FSM_TRUNC if required */
	FSM_WS,			/* Record char, then go to FSM_WS_SKIP */
	FSM_WS_SKIP,	/* Skip if WS, otherwise record char */
	FSM_WS_LEAD,	/* As for FSM_WS_SKIP but for leading whitespace,
					   needs to be followed by a text char */
	FSM_CR, 
	FSM_CONT, 
	FSM_WS_CONT, 
	FSM_CR_CONT, 
	
	/* A state that can't be directly entered from the FSM but is triggered 
	   externally, used to consume remaining input */
	FSM_TRUNC,
	
	/* Non-FSM states that terminate processing */
	FSM_DONE, FSM_EOF, FSM_ERROR, 
	
	FSM_STATE_LAST
	} FSM_STATE_TYPE;

/* The FSM parsing tables.  Notes for each table:

   Text FSM: 
   
	For FSM_START/FSM_WS_LEAD, a CHAR_CONT at the start of the line isn't
	treated as a continuation character, it'd be continuing an empty line.  
	
	FSM_START can either allow or disallow leading whitespace.  Setting the
	CHAR_WS transition to FSM_WS_LEAD (not FSM_WS) enables skipping leading 
	whitespace, but we currently set it to FSM_ERROR since the lines that 
	we're reading (HTTP header, PEM, SSH ID) shouldn't have leading 
	whitespace.  Note that this currently makes FSM_WS_LEAD unreachable, 
	it's left there to preserve the table ordering and in case it's needed in
	the future.
		
	The FSM is currently set up to reject blank lines, e.g. "   \n", as 
	invalid rather than reducing them to empty lines, if required this can 
	be changed to treat them as plain empty lines.
	
   HTTP FSM:

	FSM_START explicitly disallows whitespace at the start of the line to
	implement the RFC 9112 section 5.2 ban on obs-fold, "a server that 
	receives an obs-fold in a request message that is not within a 
	"message/http" container MUST either reject the message by sending a 
	400 [..]", with gateways required to reject or sanitise the message
	into a non-folded form.  Returning a CRYPT_ERROR_BADDATA means that the
	calling code responds with a 400 error.
	
	This is for server-side, client-side we're supposed to unfold the line
	but the only time we'd ever see this is in a request-smuggling
	attack, no legitimate server would ever need to fold Content-Length, 
	Content-Type, Transfer-Encoding, Connection, or Server.
	
	We're also pretty strict about requiring a full CRLF (RFC 9112 section 
	2.1, "An HTTP/1.1 message consists of a start-line followed by a CRLF",
	with RFC 7230 before it saying, section 3.1.1, "A request-line begins 
	with a method token, followed by a single space (SP), the request-
	target, another single space (SP), the protocol version, and ends with 
	CRLF)" and the same with other line types, and RFC 2616 before that
	saying (section 2.2) "HTTP/1.1 defines the sequence CR LF as the end-of-
	line marker for all protocol elements except the entity-body".
	
	RFC 9112 section 2.2 says "Although the line terminator for the start-
	line and fields is the sequence CRLF, a recipient MAY recognize a single 
	LF as a line terminator and ignore any preceding CR" (RFC 7230 has no
	equivalent text) which seems to be saying that a parser can ignore the 
	CR part and only look for the LF rather than that it can accept 
	standalone LFs.  The text is actually somewhat ambiguous, which is why 
	some servers accept bare LFs, making request-smuggling possible, but in 
	our case we fail closed and reject bare LFs, forcing a full CRLF.
	
	Notable differences to the text FSM are that CHAR_EOF always results in
	FSM_ERROR because having the peer close the connection produces a
	truncated header and not a valid text line, and that no leading 
	whitespace (for the obsolete obs-fold line-continuation mechanism) or
	explicit line continuations as for the text FSM are allowed */

typedef FSM_STATE_TYPE FSM_TABLE_ENTRY[ 9 ];

static const FSM_TABLE_ENTRY textFSM[] = {
 /*	Current										Current Character
	State			CHAR_TEXT	CHAR_WS		CHAR_CONT		CHAR_CR		CHAR_LF		CHAR_EOF
	--------		---------	-------		--------		-------		-------		-------- */
  { FSM_START,		FSM_TEXT,	FSM_ERROR,	FSM_TEXT,		FSM_CR,		FSM_DONE,	FSM_ERROR },
  { FSM_TEXT,		FSM_TEXT,	FSM_WS,		FSM_CONT,		FSM_CR,		FSM_DONE,	FSM_EOF },
  { FSM_WS,			FSM_TEXT,	FSM_WS_SKIP,FSM_CONT,		FSM_CR,		FSM_DONE,	FSM_EOF },
  { FSM_WS_SKIP,	FSM_TEXT,	FSM_WS_SKIP,FSM_CONT,		FSM_CR,		FSM_DONE,	FSM_EOF },
  { FSM_WS_LEAD,	FSM_TEXT,	FSM_WS_LEAD,FSM_TEXT,		FSM_ERROR,	FSM_ERROR,	FSM_ERROR },
  { FSM_CR,			FSM_ERROR,	FSM_ERROR,	FSM_ERROR,		FSM_ERROR,	FSM_DONE,	FSM_EOF },
  { FSM_CONT,		FSM_TEXT,	FSM_WS_CONT,FSM_CONT,		FSM_CR_CONT,FSM_WS_SKIP,FSM_ERROR },
  { FSM_WS_CONT,	FSM_TEXT,	FSM_WS_CONT,FSM_CONT,		FSM_CR_CONT,FSM_WS_SKIP,FSM_ERROR },
  { FSM_CR_CONT,	FSM_ERROR,	FSM_ERROR,	FSM_ERROR,		FSM_CR_CONT,FSM_WS_SKIP,FSM_ERROR },
  { FSM_TRUNC,		FSM_TRUNC,	FSM_TRUNC,	FSM_TRUNC,		FSM_TRUNC,	FSM_DONE,	FSM_EOF },
	{ 0 }, { 0 }
	};

static const FSM_TABLE_ENTRY httpFSM[] = {
 /*	Current											Current Character
	State			CHAR_TEXT	CHAR_WS		CHAR_CONT		CHAR_CR		CHAR_LF		CHAR_EOF
	--------		---------	-------		--------		-------		-------		-------- */
  {	FSM_START,		FSM_TEXT,	FSM_ERROR,	FSM_TEXT,		FSM_CR,		FSM_ERROR,	FSM_ERROR },
  { FSM_TEXT,		FSM_TEXT,	FSM_WS,		FSM_TEXT,		FSM_CR,		FSM_ERROR,	FSM_ERROR },
  { FSM_WS,			FSM_TEXT,	FSM_WS_SKIP,FSM_TEXT,		FSM_CR,		FSM_ERROR,	FSM_ERROR },
  { FSM_WS_SKIP,	FSM_TEXT,	FSM_WS_SKIP,FSM_TEXT,		FSM_CR,		FSM_ERROR,	FSM_ERROR },
  { FSM_WS_LEAD,	FSM_ERROR,	FSM_ERROR,	FSM_ERROR,		FSM_ERROR,	FSM_ERROR,	FSM_ERROR },
  { FSM_CR,			FSM_ERROR,	FSM_ERROR,	FSM_ERROR,		FSM_ERROR,	FSM_DONE,	FSM_ERROR },
  { FSM_CONT,		FSM_ERROR,	FSM_ERROR,	FSM_ERROR,		FSM_ERROR,	FSM_ERROR,	FSM_ERROR },
  { FSM_WS_CONT,	FSM_ERROR,	FSM_ERROR,	FSM_ERROR,		FSM_ERROR,	FSM_ERROR,	FSM_ERROR },
  { FSM_CR_CONT,	FSM_ERROR,	FSM_ERROR,	FSM_ERROR,		FSM_ERROR,	FSM_ERROR,	FSM_ERROR },
  { FSM_TRUNC,		FSM_ERROR,	FSM_ERROR,	FSM_ERROR,		FSM_ERROR,	FSM_ERROR,	FSM_ERROR },
	{ 0 }, { 0 }
	};
	
/* Use the FSM table to read/parse a line of text */

CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 4, 5, 7 ) ) \
static int fsmParse( INOUT_PTR TYPECAST( STREAM * ) struct ST *streamPtr,
					 OUT_BUFFER( lineBufferMaxLen, *lineBufferSize ) \
						char *lineBuffer,
					 IN_LENGTH_SHORT_MIN( 16 ) const int lineBufferMaxLen, 
					 OUT_RANGE( 0, lineBufferMaxLen ) int *lineBufferSize, 
					 IN_ARRAY( fsmTableSize ) const FSM_TABLE_ENTRY *fsmTable,
					 IN_LENGTH_SHORT_MIN( 4 ) const int fsmTableSize,
					 IN_PTR READCHAR_FUNCTION readCharFunction, 
					 OUT_OPT_BOOL BOOLEAN *localError,
					 IN_ENUM_OPT( READTEXT ) const READTEXT_TYPE readOption )
	{
	FSM_STATE_TYPE fsmState = FSM_START, prevState;
	LOOP_INDEX totalChars;
	int bufPos = 0, restartPoint = CRYPT_ERROR;

	assert( isWritePtr( streamPtr, sizeof( STREAM ) ) );
	assert( isWritePtrDynamic( lineBuffer, lineBufferMaxLen ) );
	assert( isWritePtr( lineBufferSize, sizeof( int ) ) );
	assert( isReadPtrDynamic( fsmTable, 
							  fsmTableSize * sizeof( FSM_TABLE_ENTRY ) ) );
	assert( localError == NULL || \
			isWritePtr( localError, sizeof( BOOLEAN ) ) );

	REQUIRES( isShortIntegerRangeMin( lineBufferMaxLen, 16 ) );
	REQUIRES( isShortIntegerRangeMin( fsmTableSize, 4 ) );
	REQUIRES( isEnumRangeOpt( readOption, READTEXT ) );

	/* Clear return values */
	REQUIRES( isShortIntegerRangeNZ( lineBufferMaxLen ) ); 
	memset( lineBuffer, 0, min( 16, lineBufferMaxLen ) );
	*lineBufferSize = 0;
	if( localError != NULL )
		*localError = FALSE;

	/* Read up to MAX_LINE_LENGTH chars.  Anything longer than this is 
	   probably a DoS */
	LOOP_MAX( totalChars = 0, totalChars < MAX_LINE_LENGTH, totalChars++ )
		{
		CHAR_CLASS_TYPE charClass;
		int ch, status;

		ENSURES( LOOP_INVARIANT_MAX( totalChars, 0, MAX_LINE_LENGTH - 1 ) );

		/* Get the next input character and classify it into an FSM class */
		status = ch = readCharFunction( streamPtr );
		if( cryptStatusError( status ) )
			{
			/* Now we run into a special-case condition where some software 
			   may forget to end a line, or the final line in a longer 
			   message, with an EOL, in which case we get a 
			   CRYPT_ERROR_UNDERFLOW to indicate that we've run out of data
			   rather than encountering an EOL.  To deal with this, if we've
			   read at least 3 characters of text, we treat a 
			   CRYPT_ERROR_UNDERFLOW as if there was an EOL at this point */
			if( status == CRYPT_ERROR_UNDERFLOW && bufPos >= 3 )
				{
				/* Since we've run out of data in the stream it'll be in the
				   error state, so we need to reset it before continuing 
				   since we're emulating a valid read of an EOL */
				sClearError( streamPtr );
				charClass = CHAR_CLASS_EOF;
				ch = ' ';	/* Reset from error code to dummy value */
				}
			else
				{
				/* It's some other type of error or there's nothing to 
				   return, it's a real error */
				return( status );
				}
			}
		else
			{  
			/* Determine the FSM character class for the new character */
			charClass = getCharClass( ch );
			if( charClass == CHAR_CLASS_ERROR )
				{
				return( exitInvalidChar( streamPtr, ch, totalChars, 
										 localError ) );
				}

			/* Adjust the character class for the read options:
		
				If we're not reading in multiline mode than a continuation 
				character is just an ordinary text character.
			
				If we're reading in raw mode then whitespace is just an 
				ordinary text character */
			if( readOption != READTEXT_MULTILINE && \
				charClass == CHAR_CLASS_CONT )
				charClass = CHAR_CLASS_TEXT;
			if( readOption == READTEXT_RAW && charClass == CHAR_CLASS_WS )
				charClass = CHAR_CLASS_TEXT;

			/* If we're canonicalising whitespace, do so now */
			if( readOption != READTEXT_RAW && ch == '\t' )
				ch = ' ';
			}

		/* Move to the next state in the FSM after remembering the current 
		   state.  This is needed to determine whether a continuation 
		   character ';' is embedded in a piece of text, so it's just a 
		   plain character, or is an actual line-continuation character */
		REQUIRES( isEnumRangeOpt( charClass, CHAR_CLASS ) );
		REQUIRES( isEnumRangeOpt( fsmState, FSM_STATE ) && \
				  rangeCheck( fsmState, 0, fsmTableSize - 1 ) );
		REQUIRES( fsmTable[ fsmState ][ 0 ] == fsmState );
		prevState = fsmState;
		fsmState = fsmTable[ fsmState ][ charClass ];
		switch( fsmState )
			{
			case FSM_START:
				/* This is the initial state, we can never get to this as a 
				   successor state */
				retIntError();
				
			case FSM_CONT:
				/* A continuation character acts like an EOL, so we truncate 
				   any trailing whitespace before continuing */
				if( bufPos > 0 && lineBuffer[ bufPos - 1 ] == ' ' )
					bufPos--;

				/* If it's a READTEXT_MULTILINE read and we've started a new 
				   line, make sure that there's some content present */
				if( restartPoint != CRYPT_ERROR && bufPos <= restartPoint )
					{
					return( exitUnderflow( streamPtr, totalChars, 
										   localError ) );
					}
				STDC_FALLTHROUGH;

			case FSM_TEXT:
			case FSM_WS:
				/* If we're over the maximum buffer size this is an error 
				   unless we're reading with READTEXT_TRUNCATE */
				if( bufPos >= lineBufferMaxLen )
					{
					/* If we've been asked to return all input but we've run 
					   out of space, tell the caller */
					if( readOption != READTEXT_TRUNCATE )
						{
						return( exitTextLineError( streamPtr, 
										"Text line too long, more than %d "
										"characters", lineBufferMaxLen, 0, 
										localError, CRYPT_ERROR_OVERFLOW ) );
						}
				
					/* From now on we're in truncate mode */
					fsmState = FSM_TRUNC;
					continue;
					}

				/* Record the character */
				REQUIRES( !checkOverflowInc( bufPos ) );
				lineBuffer[ bufPos++ ] = intToByte( ch );
				ENSURES( bufPos > 0 && bufPos <= totalChars + 1 && \
						 bufPos <= MAX_LINE_LENGTH );
						 /* The 'totalChars + 1' is because totalChars is
							the loop iterator and won't have been 
							incremented yet at this point */
				break;
			
			case FSM_WS_SKIP:
			case FSM_WS_LEAD:
				/* If we've arrived here from a continuation state then the 
				   line has been continued onto the next one, remember where 
				   the continued portion starts so that we can check that 
				   it's nonempty */
				if( prevState == FSM_CONT || prevState == FSM_WS_CONT || \
					prevState == FSM_CR_CONT )
					restartPoint = bufPos;

				/* We're eating repeated whitespace in this state so nothing 
				   to do */
				continue;
			
			case FSM_CR:
			case FSM_WS_CONT:
			case FSM_CR_CONT:
				/* FSM_internal states used only to move to a particular 
				   next state */
				break;
			
			case FSM_DONE:
			case FSM_EOF:
				/* We're done, strip trailing whitespace unless we're reading
				   in raw mode.  This has both been canonicalised so we 
				   don't need to check for anything other than spaces, and 
				   there should only be a single value because we strip 
				   repeated spaces */
				if( readOption != READTEXT_RAW && \
					bufPos > 0 && lineBuffer[ bufPos - 1 ] == ' ' )
					bufPos--;
				
				/* If it's a READTEXT_MULTILINE read and we've started a new 
				   line, make sure that there's some content present */
				if( restartPoint != CRYPT_ERROR && bufPos <= restartPoint )
					{
					return( exitUnderflow( streamPtr, totalChars, 
										   localError ) );
					}
				
				*lineBufferSize = bufPos;

				return( CRYPT_OK );
			
			case FSM_ERROR:
				/* If we ran out of input rather than hitting an invalid 
				   character, for example EOF in the middle of a continued 
				   line, report it as such */
				if( charClass == CHAR_CLASS_EOF )
					{
					return( exitUnderflow( streamPtr, totalChars, 
										   localError ) );
					}
					
				return( exitInvalidChar( streamPtr, ch, totalChars, 
										 localError ) );
			
			case FSM_TRUNC:
				/* We're just consuming input in this state so nothing to 
				   do */
				break;
			
			default:
				retIntError(); 
			}
		}
	ENSURES( LOOP_BOUND_OK );
	if( totalChars >= MAX_LINE_LENGTH )
		{
		return( exitTextLineError( streamPtr, "Text line too long, more "
								   "than %d characters", MAX_LINE_LENGTH, 0, 
								   localError, CRYPT_ERROR_OVERFLOW ) );
		}
	*lineBufferSize = bufPos;

	return( CRYPT_OK );
	}

/* Read a line of text data ending in an EOL, with optional handling of 
   continued lines denoted by the MIME convention of a semicolon as the last 
   character */

CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 4 ) ) \
int readTextLine( INOUT_PTR TYPECAST( STREAM * ) struct ST *streamPtr,
				  OUT_BUFFER( lineBufferMaxLen, *lineBufferSize ) \
						char *lineBuffer,
				  IN_LENGTH_SHORT_MIN( 16 ) const int lineBufferMaxLen, 
				  OUT_RANGE( 0, lineBufferMaxLen ) int *lineBufferSize, 
				  OUT_OPT_BOOL BOOLEAN *localError,
				  IN_ENUM_OPT( READTEXT ) const READTEXT_TYPE options,
				  IN_BOOL const BOOLEAN isNetworkStream )
	{
	/* All of the other parameters are passed directly to fsmParse(), the 
	   only one that we check here is the one that's used locally.  The
	   network-stream version is only ever called from one location,
	   session/ssh2_id.c:readSSHID(), otherwise it's always called with
	   memory streams */
	REQUIRES( isBooleanValue( isNetworkStream ) );
	
	return( fsmParse( streamPtr, lineBuffer, lineBufferMaxLen, 
					  lineBufferSize, textFSM, 
					  FAILSAFE_ARRAYSIZE( textFSM, FSM_TABLE_ENTRY ),
					  isNetworkStream ? networkReadCharFunction : sgetc, 
					  localError, options ) );
	}

/* Read a line of text with HTTP semantics.  This is kept distinct from the
   standard readTextLine() because we need to enforce RFC 7230/9110 
   semantics as much as possible, including all of the things that we really 
   don't care about, in order to prevent various attacks involving 
   manipulating HTTP headers.  What we're trying to do here is to remain as 
   close as possible to what RFC 7230/9110 requires so that an attacker 
   can't take advantage of differences between how we handle a given HTTP 
   line and how the other party handles it.  This isn't bulletproof because 
   we're not a full-blown web server but it does try and close the bigger 
   attack vectors */

#ifdef USE_HTTP 

CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 4, 6 ) ) \
int readHttpLine( INOUT_PTR TYPECAST( STREAM * ) struct ST *streamPtr,
				  OUT_BUFFER( lineBufferMaxLen, *lineBufferSize ) \
						char *lineBuffer,
				  IN_LENGTH_SHORT_MIN( 16 ) const int lineBufferMaxLen, 
				  OUT_RANGE( 0, lineBufferMaxLen ) int *lineBufferSize, 
				  OUT_OPT_BOOL BOOLEAN *localError,
				  IN_PTR READCHAR_FUNCTION readCharFunction )
	{
	return( fsmParse( streamPtr, lineBuffer, lineBufferMaxLen, 
					  lineBufferSize, httpFSM, 
					  FAILSAFE_ARRAYSIZE( httpFSM, FSM_TABLE_ENTRY ),
					  readCharFunction, localError, READTEXT_NONE ) );
	}
#endif /* USE_HTTP */
#endif /* USE_HTTP || USE_BASE64 || USE_SCEP || USE_SSH */

/****************************************************************************
*																			*
*								Self-test Functions							*
*																			*
****************************************************************************/

/* Test code for the above functions */

#ifndef CONFIG_CONSERVE_MEMORY_EXTRA

#if defined( USE_HTTP ) || defined( USE_BASE64 ) || \
	defined( USE_SCEP ) || defined( USE_SSH )

typedef enum {
	TEST_OPTION_NONE,			/* No test option type */
	TEST_OPTION_TRUNCATION,		/* Test truncation of input to fit output */
	TEST_OPTION_LAST			/* Last possible test option */
	} TEST_OPTION_TYPE;
	
CHECK_RETVAL_BOOL STDC_NONNULL_ARG( ( 1, 3 ) ) \
static BOOLEAN testRead( IN_BUFFER( dataInLength ) const char *dataIn,
						 IN_LENGTH_SHORT_MIN( 1 ) const int dataInLength, 
						 IN_BUFFER( dataOutLength ) const char *dataOut,
						 IN_LENGTH_SHORT_MIN( 1 ) const int dataOutLength,
						 IN_ENUM_OPT( READTEXT ) \
							const READTEXT_TYPE options,
						 IN_STATUS const int expectedStatus,
						 IN_ENUM_OPT( TEST_OPTION ) \
							const TEST_OPTION_TYPE testOption,
						 IN_BOOL const BOOLEAN isHttpRead )
	{
	STREAM stream;
	BYTE buffer[ 32 + 8 ];
	int length, status;

	assert( isReadPtrDynamic( dataIn, dataInLength ) );
	assert( isReadPtrDynamic( dataOut, dataOutLength ) );

	REQUIRES_B( isShortIntegerRangeMin( dataInLength, 1 ) );
	REQUIRES_B( ( testOption != TEST_OPTION_TRUNCATION && \
				  rangeCheck( dataOutLength, 1, 32 ) ) || \
				( testOption == TEST_OPTION_TRUNCATION && \
				  rangeCheck( dataOutLength, 16, 32 ) ) );
	REQUIRES_B( isEnumRangeOpt( options, READTEXT ) );
	REQUIRES_B( isEnumRangeOpt( testOption, TEST_OPTION ) );
	REQUIRES_B( isBooleanValue( isHttpRead ) );

	/* The self-test code tests, among other things, truncation of overly 
	   long input lines, in which case we give the buffer size as 
	   'dataOutLength', the potential truncation point, rather than the 
	   actual buffer size */
	memset( buffer, '*', 32 );	/* Pollute the data buffer */
	sMemPseudoConnect( &stream, dataIn, dataInLength );
	if( isHttpRead )
		status = readHttpLine( &stream, buffer, 32, &length, NULL, sgetc );
	else
		{
		status = readTextLine( &stream, buffer, 
							   ( testOption == TEST_OPTION_TRUNCATION ) ? \
							     dataOutLength : 32, &length, NULL, 
							   options, FALSE );
		}
	sMemDisconnect( &stream );
	if( status != expectedStatus )
		{
		DEBUG_DIAG(( "Got %d, expected %d, for '%s' -> '%s'", 
					 status, expectedStatus, dataIn, dataOut ));
		return( FALSE );
		}
	if( cryptStatusError( status ) )
		{
		/* We expected an error return, we're done */
		return( TRUE );
		}
	if( dataOutLength >= 7 && !memcmp( dataOut, "<blank>", 7 ) )
		{
		return( ( length == 0 ) ? TRUE : FALSE );
		}
	if( length != dataOutLength || memcmp( buffer, dataOut, dataOutLength ) )
		{
		DEBUG_DIAG(( "Got %d, expected %d, for '%s' -> '%s'", 
					 status, expectedStatus, dataIn, dataOut ));
		return( FALSE );
		}

	return( TRUE );
	}

CHECK_RETVAL_BOOL STDC_NONNULL_ARG( ( 1, 3 ) ) \
static BOOLEAN testReadLine( IN_BUFFER( dataInLength ) const char *dataIn,
							 IN_LENGTH_SHORT_MIN( 1 ) \
								const int dataInLength, 
							 IN_BUFFER( dataOutLength ) const char *dataOut,
							 IN_LENGTH_SHORT_MIN( 1 ) \
								const int dataOutLength,
							 IN_ENUM_OPT( READTEXT ) \
								const READTEXT_TYPE options,
							 IN_STATUS const int expectedStatus,
							 IN_ENUM_OPT( TEST_OPTION ) \
								const TEST_OPTION_TYPE testOption )
	{
	return( testRead( dataIn, dataInLength, dataOut, dataOutLength, options,
					  expectedStatus, testOption, FALSE ) );
	}
#endif /* USE_HTTP || USE_BASE64 || USE_SCEP || USE_SSH */

#ifdef USE_HTTP 

CHECK_RETVAL_BOOL STDC_NONNULL_ARG( ( 1, 3 ) ) \
static BOOLEAN testReadHttp( IN_BUFFER( dataInLength ) const char *dataIn,
							 IN_LENGTH_SHORT_MIN( 1 ) \
								const int dataInLength, 
							 IN_BUFFER( dataOutLength ) const char *dataOut,
							 IN_LENGTH_SHORT_MIN( 1 ) \
								const int dataOutLength,
							 IN_ENUM_OPT( READTEXT ) \
								const READTEXT_TYPE options,
							 IN_STATUS const int expectedStatus,
							 IN_ENUM_OPT( TEST_OPTION ) \
								const TEST_OPTION_TYPE testOption )
	{
	return( testRead( dataIn, dataInLength, dataOut, dataOutLength, options,
					  expectedStatus, testOption, TRUE ) );
	}
#endif /* USE_HTTP */

#if defined( USE_BASE64 ) 

CHECK_RETVAL_BOOL \
static BOOLEAN testBase64( void )
	{
	const char *base64string = "aaaaaaaaaaaaaaaaaaaaaaaa";
	BYTE buffer[ 20 + 8 ];
	LOOP_INDEX inLength;
	int outLength, decodedOutLength, status;

	LOOP_MED( inLength = 10, inLength < 24, inLength++ )
		{
		ENSURES_B( LOOP_INVARIANT_MED( inLength, 10, 23 ) );

		/* Skip non-decodable lengths */
		if( inLength == 13 || inLength == 17 || inLength == 21 )
			continue;

		/* Verify that the calculated decoded-length value matches the 
		   actual decoded length */
		status = base64decodeLen( base64string, inLength, 
								  &decodedOutLength );
		if( cryptStatusError( status ) )
			return( FALSE );
		status = base64decode( buffer, 20, &outLength, base64string, 
							   inLength, CRYPT_CERTFORMAT_NONE );
		if( cryptStatusError( status ) )
			return( FALSE );
		if( outLength != decodedOutLength )
			return( FALSE );
		}
	ENSURES_B(  LOOP_BOUND_OK );

	return( TRUE );
	}
#endif /* USE_BASE64 */

CHECK_RETVAL_BOOL \
BOOLEAN testIntAPI( void )
	{
	static_assert( MIN_KEYSIZE <= 16,
				   "MIN_KEYSIZE is larger than entropy test vector size" );

	/* Test the non-trivial key check code.  The following values have no
	   special significance but were just generated with:

		od -An -N16 -tx1 < /dev/urandom */
	if( !checkNontrivialKey( "\x2E\x19\x76\x57\xDB\x30\xE6\x26\x83\x76\x6B\xAE\xDA\x5C\x46\x28", 16 ) || \
		!checkNontrivialKey( "\x14\xF3\x3C\x5A\xB8\x63\x13\xFB\x5B\xAF\xC4\xBA\x4F\xC8\x7F\x74", 16 ) || \
		!checkNontrivialKey( "\x7B\xE0\xE4\x14\x5C\x7C\x2C\x07\x02\xD9\x2D\xD7\x83\x5C\x4E\xAD", 16 ) || \
		!checkNontrivialKey( "\xD3\x9C\x16\x37\xAD\x12\x19\xA2\x5E\x8C\xEC\x71\xC3\x7D\xA4\xF8", 16 ) || \
		!checkNontrivialKey( "\x7F\x6B\x30\xAD\x02\x83\x96\xF9\x52\xF6\x81\x84\xF0\x0C\x5D\x83", 16 ) || \
		!checkNontrivialKey( "\x79\x92\xF9\xD1\x75\x43\x56\x87\x65\x61\x8F\x7E\x3A\xC5\x11\x55", 16 ) || \
		!checkNontrivialKey( "\x62\xAF\x14\xCF\x1F\x5F\xA7\xC6\x5B\x45\xAF\x87\x43\x02\x27\xBB", 16 ) || \
		!checkNontrivialKey( "\xAE\x57\xF3\x63\x45\x03\x2E\x6B\x59\xDE\x95\xD9\x0C\xCA\x71\x85", 16 ) )
		return( FALSE );
	if( checkNontrivialKey( "abcdefghijklmnop", 16 ) || \
		checkNontrivialKey( "\xA5\xA5\xA5\xA5\xA5\xA5\xA5\xA5\xA5\xA5\xA5\xA5\xA5\xA5\xA5\xA5", 16 ) || \
		checkNontrivialKey( "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A\x0B\x0C\x0D\x0E\x0F", 16 ) || \
		checkNontrivialKey( "\x2E\x19\x76\x57\xDB\x30\xE6\x26\x83\x76"
							"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0A"
							"\x14\xF3\x3C\x5A\xB8\x63\x13\xFB\x5B\xAF", 30 ) )
		return( FALSE );

	/* Test the entropy-check code, same values as above */
	if( !checkEntropy( "\x2E\x19\x76\x57\xDB\x30\xE6\x26\x83\x76\x6B\xAE\xDA\x5C\x46\x28", 16 ) || \
		!checkEntropy( "\x14\xF3\x3C\x5A\xB8\x63\x13\xFB\x5B\xAF\xC4\xBA\x4F\xC8\x7F\x74", 16 ) || \
		!checkEntropy( "\x7B\xE0\xE4\x14\x5C\x7C\x2C\x07\x02\xD9\x2D\xD7\x83\x5C\x4E\xAD", 16 ) || \
		!checkEntropy( "\xD3\x9C\x16\x37\xAD\x12\x19\xA2\x5E\x8C\xEC\x71\xC3\x7D\xA4\xF8", 16 ) || \
		!checkEntropy( "\x7F\x6B\x30\xAD\x02\x83\x96\xF9\x52\xF6\x81\x84\xF0\x0C\x5D\x83", 16 ) || \
		!checkEntropy( "\x79\x92\xF9\xD1\x75\x43\x56\x87\x65\x61\x8F\x7E\x3A\xC5\x11\x55", 16 ) || \
		!checkEntropy( "\x62\xAF\x14\xCF\x1F\x5F\xA7\xC6\x5B\x45\xAF\x87\x43\x02\x27\xBB", 16 ) || \
		!checkEntropy( "\xAE\x57\xF3\x63\x45\x03\x2E\x6B\x59\xDE\x95\xD9\x0C\xCA\x71\x85", 16 ) )
		return( FALSE );
	if( checkEntropy( "\xA5\x5A\xA5\x5A\xA5\x5A\xA5\x5A\xA5\x5A\x5A\x5A\x5A\x5A\x5A\x5A", 16 ) )
		return( FALSE );

	/* Test the hash algorithm-strength code */
	if( isStrongerHash( CRYPT_ALGO_SHA1, CRYPT_ALGO_SHA2 ) || \
		!isStrongerHash( CRYPT_ALGO_SHA2, CRYPT_ALGO_SHA1 ) || \
		isStrongerHash( CRYPT_ALGO_MD5, CRYPT_ALGO_SHA2 ) || \
		!isStrongerHash( CRYPT_ALGO_SHA2, CRYPT_ALGO_MD5 ) )
		return( FALSE );

	/* Test the checksumming code */
	if( checksumData( "12345678", 8 ) != checksumData( "12345678", 8 ) || \
		checksumData( "12345678", 8 ) == checksumData( "12345778", 8 ) || \
		checksumData( "12345678", 8 ) == checksumData( "12345\xB7" "78", 8 ) || \
		checksumData( "12345678", 8 ) == checksumData( "12345\x00" "78", 8 ) )
		return( FALSE );
	
	/* Test the constant-time mechanisms.  We can't actually test the timing
	   resistance on these without external instrumentation so all this is
	   doing is making sure that it works as expected */
	if( compareDataConstTime( "\x2E\x19\x76\x57\xDB\x30\xE6\x26\x83\x76",
							  "\x2E\x19\x76\x57\xDB\x30\xE6\x26\x83\x76", 10 ) != TRUE || \
		compareDataConstTime( "\x2E\x19\x76\x57\xDB\x30\xE7\x26\x83\x76",
							  "\x2E\x19\x76\x57\xDB\x30\xE6\x26\x83\x76", 10 ) != FALSE || \
		!checkZeroConstTime( "\x00\x00\x00\x00\x00\x00\x00\x00", 8 ) || \
		checkZeroConstTime( "\x00\x00\x00\x00\x00\x01\x00\x00", 8 ) )
		return( FALSE );

	/* Test the base64 code */
#if defined( USE_BASE64 ) 
	if( !testBase64() )
		return( FALSE );
#endif /* USE_BASE64 */

	/* Test the text-line read code */
#if defined( USE_HTTP ) || defined( USE_BASE64 ) || \
	defined( USE_SCEP ) || defined( USE_SSH )

	/* Whitespace handling */
	if( !testReadLine( "abcdefgh\n", 9, "abcdefgh", 8, READTEXT_NONE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( " abcdefgh\n", 10, "abcdefgh", 8, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) || \
		!testReadLine( "abcdefgh \n", 10, "abcdefgh", 8, READTEXT_NONE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( "ab cdefgh \n", 11, "ab cdefgh", 9, READTEXT_NONE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( "ab\tcdefgh\t\n", 11, "ab cdefgh", 9, READTEXT_NONE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( "ab   cdefgh   \n", 15, "ab cdefgh", 9, 
					   READTEXT_NONE, CRYPT_OK, TEST_OPTION_NONE ) )
		return( FALSE );

	/* Hard EOL */
	if( !testReadLine( "abcdefgh", 8, "abcdefgh", 8, READTEXT_NONE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( " abcdefgh", 9, "abcdefgh", 8, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) || \
		!testReadLine( "abcdefgh ", 9, "abcdefgh", 8, READTEXT_NONE, 
					   CRYPT_OK, TEST_OPTION_NONE ) )
		return( FALSE );

	/* CR / LF handling */
	if( !testReadLine( "abcdefgh\r\n", 10, "abcdefgh", 8, READTEXT_NONE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( "abcdefgh\rijk\n", 13, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) || \
		!testReadLine( "abcdefgh\r\r\n", 11, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) )
		return( FALSE );

	/* Error handling */
	if( !testReadLine( "   \t   \n", 8, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) || \
		!testReadLine( "abc\x12" "efgh\n", 9, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) || \
		!testReadLine( "abc\x12" "efgh\n", 9, "<error>", 7, READTEXT_RAW, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) || \
		!testReadLine( "  ", 2, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) || \
		!testReadLine( "    ", 4, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) )
		return( FALSE );

	/* Multi-line read */
	if( !testReadLine( "abcdefgh;\nabc\n", 14, 
					   "abcdefgh;", 9, READTEXT_NONE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( "abcdefgh;\nabc\n", 14, 
					   "abcdefgh;abc", 12, READTEXT_MULTILINE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( "abcdefgh;abc\nabc\n", 17,
					   "abcdefgh;abc", 12, READTEXT_MULTILINE,
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( "abcdefgh; \n abc\n", 16, 
					   "abcdefgh;abc", 12, READTEXT_MULTILINE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( "abcdefgh ; \n abc\n", 17, 
					   "abcdefgh;abc", 12, READTEXT_MULTILINE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( "a;;b\n", 5, "a;;b", 4, READTEXT_MULTILINE, 
					   CRYPT_OK, TEST_OPTION_NONE ) )
		return( FALSE );

	/* Raw text read */
	if( !testReadLine( "abcdefgh", 8, "abcdefgh", 8, READTEXT_RAW, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( " abcdefgh", 9, " abcdefgh", 9, READTEXT_RAW, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( "abcdefgh ", 9, "abcdefgh ", 9, READTEXT_RAW, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadLine( "   ab   cdefgh   ", 17, "   ab   cdefgh   ", 17, 
					   READTEXT_RAW, CRYPT_OK, TEST_OPTION_NONE ) )
		return( FALSE );

	/* Over-long input line */
	if( !testReadLine( "abcdefghijklmnopq\n", 18, 
					   "abcdefghijklmnop", 16, READTEXT_NONE, 
					   CRYPT_ERROR_OVERFLOW, TEST_OPTION_TRUNCATION ) )
		return( FALSE );

	/* Multi-line read error handling */
	if( !testReadLine( "abcdefgh;\n", 10, "<error>", 7, READTEXT_MULTILINE, 
					   CRYPT_ERROR_UNDERFLOW, TEST_OPTION_NONE ) || \
		!testReadLine( "abcdefgh;\n\n", 11, "<error>", 7, READTEXT_MULTILINE, 
					   CRYPT_ERROR_UNDERFLOW, TEST_OPTION_NONE ) || \
		!testReadLine( "abcdefgh;\n \n", 12, "<error>", 7, READTEXT_MULTILINE, 
					   CRYPT_ERROR_UNDERFLOW, TEST_OPTION_NONE ) || \
		!testReadLine( "abcdefgh;\nijkl;\n  \n", 19, "<error>", 7, READTEXT_MULTILINE, 
					   CRYPT_ERROR_UNDERFLOW, TEST_OPTION_NONE ) )
		return( FALSE );
#endif /* USE_HTTP || USE_BASE64 || USE_SCEP || USE_SSH */

	/* Test the HTTP-line read code */
#if defined( USE_HTTP ) 
	if( !testReadHttp( "http/1.0\r\n", 10, "http/1.0", 8, READTEXT_NONE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadHttp( " http/1.0\r\n", 11, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) || \
		!testReadHttp( "  http/1.0\r\n", 12, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) )
		return( FALSE );

	/* Malformed line terminators */
	if( !testReadHttp( "http/1.0\r", 9, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_UNDERFLOW, TEST_OPTION_NONE ) || 
					   /* Underflow rather than bad-data because we ran out
					      of input before getting the LF */
		!testReadHttp( "http/1.0\n", 9, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) || \
		!testReadHttp( "\r http/1.0\r\n", 12, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) || \
		!testReadHttp( "a\rb\r\n", 5, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) || \
		!testReadHttp( " \r\n", 3, "<error>", 7, READTEXT_NONE, 
					   CRYPT_ERROR_BADDATA, TEST_OPTION_NONE ) )
		return( FALSE );

		/* Odds and ends: Blank lines, no special handling for ';' as in 
		   readTextLine() */
	if( !testReadHttp( "\r\n", 2, "<blank>", 7, READTEXT_NONE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadHttp( "a;b\r\n", 5, "a;b", 3, READTEXT_NONE, 
					   CRYPT_OK, TEST_OPTION_NONE ) || \
		!testReadHttp( "a;\r\nb\r\n", 7, "a;", 2, READTEXT_NONE, 
					   CRYPT_OK, TEST_OPTION_NONE ) )
		return( FALSE );
#endif /* USE_HTTP */

	return( TRUE );
	}
#endif /* !CONFIG_CONSERVE_MEMORY_EXTRA */
