/* -*- mode: c++; c-file-style: raknet; tab-always-indent: nil; -*- */
/**
 * @file 
 * @brief RakPeer Implementation 
 *
 * This file is part of RakNet Copyright 2003, 2004 Rakkarsoft LLC and
 * Kevin Jenkins.
 *
 * Usage of Raknet is subject to the appropriate licence agreement.
 * "Shareware" Licensees with Rakkarsoft LLC are subject to the
 * shareware license found at
 * http://www.rakkarsoft.com/shareWareLicense.html which you agreed to
 * upon purchase of a "Shareware license" "Commercial" Licensees with
 * Rakkarsoft LLC are subject to the commercial license found at
 * http://www.rakkarsoft.com/sourceCodeLicense.html which you agreed
 * to upon purchase of a "Commercial license" All other users are
 * subject to the GNU General Public License as published by the Free
 * Software Foundation; either version 2 of the License, or (at your
 * option) any later version.
 *
 * Refer to the appropriate license agreement for distribution,
 * modification, and warranty rights.
 */
#include "main.h"
#include "RakPeer.h"

#ifdef __USE_IO_COMPLETION_PORTS
#include "AsynchronousFileIO.h"
#endif

#ifdef _WIN32 
//#include <Shlwapi.h>
#include <process.h>
#else
#define closesocket close
#include <unistd.h>
#include <pthread.h>
#endif
#include <ctype.h> // toupper

#include "GetTime.h"
#include "PacketEnumerations.h"
#include "HuffmanEncodingTree.h"
#include "PacketPool.h"
#include "Rand.h"

// alloca
#ifdef _WIN32
#include <malloc.h>
#else
#include <stdlib.h>
#endif

static const unsigned long SYN_COOKIE_OLD_RANDOM_NUMBER_DURATION = 5000;

// UPDATE_THREAD_POLL_TIME is how often the update thread will poll to see
// if receive wasn't called within UPDATE_THREAD_UPDATE_TIME.  If it wasn't called within that time,
// the updating thread will activate and take over network communication until Receive is called again.
//static const unsigned long UPDATE_THREAD_UPDATE_TIME=30;
//static const unsigned long UPDATE_THREAD_POLL_TIME=30;

//#define _TEST_AES

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Constructor
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
RakPeer::RakPeer()
{
	usingSecurity = false;
	memset( frequencyTable, 0, sizeof( unsigned long ) * 256 );
	rawBytesSent = rawBytesReceived = compressedBytesSent = compressedBytesReceived = 0;
	outputTree = inputTree = 0;
	connectionSocket = INVALID_SOCKET;
	MTUSize = DEFAULT_MTU_SIZE;
	trackFrequencyTable = false;
	maximumIncomingConnections = 0;
	maximumNumberOfPeers = 0;
	remoteSystemList = 0;
	bytesSentPerSecond = bytesReceivedPerSecond = 0;
	endThreads = true;
	isMainLoopThreadActive = false;
	// isRecvfromThreadActive=false;
	occasionalPing = false;
	connectionSocket = INVALID_SOCKET;
	myPlayerId = UNASSIGNED_PLAYER_ID;
	allowConnectionResponseIPMigration = false;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Destructor
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
RakPeer::~RakPeer()
{
	unsigned i;
	
	Disconnect( 0L );
	
	// Clear out the lists:
	
	for ( i = 0; i < requestedConnectionsList.size(); i++ )
		delete requestedConnectionsList[ i ];
		
	requestedConnectionsList.clear();
	
	// Free the ban list.
	ClearBanList();
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Starts the network threads, opens the listen port
// You must call this before calling SetMaximumIncomingConnections or Connect
// Multiple calls while already active are ignored.  To call this function again with different settings, you must first call Disconnect()
//
// Parameters:
// MaximumNumberOfPeers:  Required so the network can preallocate and for thread safety.
// - A pure client would set this to 1.  A pure server would set it to the number of allowed clients.
// - A hybrid would set it to the sum of both types of connections
// localPort: The port to listen for connections on.
// _threadSleepTimer: >=0 for how many ms to Sleep each internal update cycle (recommended 30 for low performance, 0 for regular)
//
// Returns:
// False on failure (can't create socket or thread), true on success.
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
bool RakPeer::Initialize( unsigned short MaximumNumberOfPeers, unsigned short localPort, int _threadSleepTimer )
{
	unsigned i;
	
	assert( MaximumNumberOfPeers > 0 );
	
	if ( MaximumNumberOfPeers <= 0 )
		return false;
		
	if ( connectionSocket == INVALID_SOCKET )
	{
		connectionSocket = SocketLayer::Instance() ->CreateBoundSocket( localPort, true );
		
		if ( connectionSocket == INVALID_SOCKET )
			return false;
	}
	
	if ( _threadSleepTimer < 0 )
		return false;
		
	if ( maximumNumberOfPeers == 0 )
	{
		rakPeerMutexes[ RakPeer::remoteSystemList_Mutex ].Lock();
		remoteSystemList = new RemoteSystemStruct[ MaximumNumberOfPeers ];
		
		for ( i = 0; i < MaximumNumberOfPeers; i++ )
		{
			remoteSystemList[ i ].playerId = UNASSIGNED_PLAYER_ID;
		}
		
		rakPeerMutexes[ RakPeer::remoteSystemList_Mutex ].Unlock();
		
		// Don't allow more incoming connections than we have peers.
		
		if ( maximumIncomingConnections > MaximumNumberOfPeers )
			maximumIncomingConnections = MaximumNumberOfPeers;
			
		maximumNumberOfPeers = MaximumNumberOfPeers;
	}
	
	// For histogram statistics
	// nextReadBytesTime=0;
	// lastSentBytes=lastReceivedBytes=0;
	
	if ( endThreads )
	{
		lastUserUpdateCycle = 0;
		
		// Reset the frequency table that we use to save outgoing data
		memset( frequencyTable, 0, sizeof( unsigned long ) * 256 );
		
		// Reset the statistical data
		rawBytesSent = rawBytesReceived = compressedBytesSent = compressedBytesReceived = 0;
		
		updateCycleIsRunning = false;
		endThreads = false;
		// Create the threads
		threadSleepTimer = _threadSleepTimer;
		
		char ipList[ 10 ][ 16 ];
		SocketLayer::Instance() ->GetMyIP( ipList );
		myPlayerId.port = localPort;
		myPlayerId.binaryAddress = inet_addr( ipList[ 0 ] );
		
		{
#ifdef _WIN32
		
			if ( isMainLoopThreadActive == false )
			{
				unsigned ProcessPacketsThreadID = 0;
				processPacketsThreadHandle = ( HANDLE ) _beginthreadex( NULL, 0, UpdateNetworkLoop, this, 0, &ProcessPacketsThreadID );
				
				if ( processPacketsThreadHandle == 0 )
				{
					Disconnect( 0L );
					return false;
				}
				
				// SetThreadPriority(processPacketsThreadHandle, THREAD_PRIORITY_HIGHEST);
				
				CloseHandle( processPacketsThreadHandle );
				
				processPacketsThreadHandle = 0;
				
			}
			
#else
			pthread_attr_t attr;
			
			pthread_attr_init( &attr );
			
			pthread_attr_setdetachstate( &attr, PTHREAD_CREATE_DETACHED );
			
			//  sched_param sp;
			//  sp.sched_priority = sched_get_priority_max(SCHED_OTHER);
			//  pthread_attr_setschedparam(&attr, &sp);
			
			int error;
			
			if ( isMainLoopThreadActive == false )
			{
				error = pthread_create( &processPacketsThreadHandle, &attr, &UpdateNetworkLoop, this );
			
				if ( error )
				{
					Disconnect( 0L );
					return false;
				}
			}
			
			processPacketsThreadHandle = 0;
#endif
			
			
			// Wait for the threads to activate.  When they are active they will set these variables to true
			
			while (  /*isRecvfromThreadActive==false || */isMainLoopThreadActive == false )
#ifdef _WIN32
			
				Sleep( 10 );
				
#else
				
				usleep( 10 * 1000 );
				
#endif
				
		}
		
		/* else
		 {
		 #ifdef __USE_IO_COMPLETION_PORTS
		 AsynchronousFileIO::Instance()->IncreaseUserCount();
		 #endif
		 }*/
	}
	
	return true;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Must be called while offline
// Secures connections though a combination of SHA1, AES128, SYN Cookies, and RSA to prevent
// connection spoofing, replay attacks, data eavesdropping, packet tampering, and MitM attacks.
// There is a significant amount of processing and a slight amount of bandwidth
// overhead for this feature.
//
// If you accept connections, you must call this or else secure connections will not be enabled
// for incoming connections.
// If you are connecting to another system, you can call this with values for the
// (e and p,q) public keys before connecting to prevent MitM
//
// Parameters:
// pubKeyP, pubKeyQ - Public keys generated from the RSACrypt class.  See the Encryption sample
// privKeyE, privKeyN - A pointer to the private keys from the RSACrypt class. See the Encryption sample
// If the private keys are 0, then a new key will be generated when this function is called
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::InitializeSecurity( char *pubKeyP, char *pubKeyQ, char *privKeyE, char *privKeyN )
{
	if ( endThreads == false )
		return ;
		
	// Setting the client key is e,n,
	// Setting the server key is p,q
	// These are mutually exclusive
	if ( ( pubKeyP && pubKeyQ && ( privKeyE || privKeyN ) ) ||
		( privKeyE && privKeyN && ( pubKeyP || pubKeyQ ) ) ||
		( pubKeyP && pubKeyQ == 0 ) ||
		( pubKeyQ && pubKeyP == 0 ) ||
		( privKeyE && privKeyN == 0 ) ||
		( privKeyN && privKeyE == 0 ) )
	{
		// Invalid parameters
		assert( 0 );
	}
	
	seedMT( RakNet::GetTime() );
	
	GenerateSYNCookieRandomNumber();
	
	usingSecurity = true;
	
	if ( pubKeyP == 0 && pubKeyQ == 0 && privKeyE == 0 && privKeyN == 0 )
	{
		keysLocallyGenerated = true;
		rsacrypt.generateKeys();
	}
	
	else
	{
		if ( pubKeyP && pubKeyQ )
		{
			// Save public keys
			memcpy( ( char* ) & publicKeyP, pubKeyP, sizeof( publicKeyP ) );
			memcpy( publicKeyQ, pubKeyQ, sizeof( publicKeyQ ) );
		}
		
		else
			if ( privKeyE && privKeyN )
			{
				BIGHALFSIZE( RSA_BIT_SIZE, p );
				BIGHALFSIZE( RSA_BIT_SIZE, q );
				memcpy( p, privKeyE, sizeof( p ) );
				memcpy( q, privKeyN, sizeof( q ) );
				// Save private keys
				rsacrypt.setPrivateKey( p, q );
			}
			
		keysLocallyGenerated = false;
	}
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description
// Must be called while offline
// Disables all security.
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::DisableSecurity( void )
{
	if ( endThreads == false )
		return ;
		
	usingSecurity = false;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Sets how many incoming connections are allowed.  If this is less than the number of players currently connected, no
// more players will be allowed to connect.  If this is greater than the maximum number of peers allowed, it will be reduced
// to the maximum number of peers allowed.
//
// Parameters:
// numberAllowed - Maximum number of incoming connections allowed.
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::SetMaximumIncomingConnections( unsigned short numberAllowed )
{
	maximumIncomingConnections = numberAllowed;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Returns the maximum number of incoming connections, which is always <= MaximumNumberOfPeers
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
unsigned short RakPeer::GetMaximumIncomingConnections( void ) const
{
	return maximumIncomingConnections;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Sets the password incoming connections must match in the call to Connect (defaults to none)
// Pass 0 to passwordData to specify no password
//
// Parameters:
// passwordData: A data block that incoming connections must match.  This can be just a password, or can be a stream of data.
// - Specify 0 for no password data
// passwordDataLength: The length in bytes of passwordData
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::SetIncomingPassword( char* passwordData, int passwordDataLength )
{
	// Set the incoming password data
	rakPeerMutexes[ incomingPasswordBitStream_Mutex ].Lock();
	incomingPasswordBitStream.Reset();
	
	if ( passwordData && passwordDataLength > 0 )
		incomingPasswordBitStream.Write( passwordData, passwordDataLength );
		
	rakPeerMutexes[ incomingPasswordBitStream_Mutex ].Unlock();
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Returns the password set by SetIncomingPassword in a BitStream
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
RakNet::BitStream *RakPeer::GetIncomingPassword( void )
{
	return & incomingPasswordBitStream;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Call this to connect to the specified host (ip or domain name) and server port.
// Calling Connect and not calling SetMaximumIncomingConnections acts as a dedicated client.  Calling both acts as a true peer.
// This is a non-blocking connection.  You know the connection is successful when IsConnected() returns true
// or receive gets a packet with the type identifier ID_CONNECTION_ACCEPTED.  If the connection is not
// successful, such as rejected connection or no response then neither of these things will happen.
// Requires that you first call Initialize
//
// Parameters:
// host: Either a dotted IP address or a domain name
// remotePort: Which port to connect to on the remote machine.
// passwordData: A data block that must match the data block on the server.  This can be just a password, or can be a stream of data
// passwordDataLength: The length in bytes of passwordData
//
// Returns:
// True on successful initiation. False on incorrect parameters, internal error, or too many existing peers
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
bool RakPeer::Connect( char* host, unsigned short remotePort, char* passwordData, int passwordDataLength )
{
	// If endThreads is true here you didn't call Initialize() first.
	
	if ( host == 0 || connectionSocket == INVALID_SOCKET || endThreads )
		return false;
		
	unsigned i, numberOfFreeSlots;
	
	numberOfFreeSlots = 0;
	
	for ( i = 0; i < maximumNumberOfPeers; i++ )
	{
		if ( remoteSystemList[ i ].playerId == UNASSIGNED_PLAYER_ID )
			numberOfFreeSlots++;
	}
	
	if ( numberOfFreeSlots == 0 )
		return false;
		
	// Set the incoming password data
	rakPeerMutexes[ outgoingPasswordBitStream_Mutex ].Lock();
	
	outgoingPasswordBitStream.Reset();
	
	if ( passwordData && passwordDataLength > 0 )
		outgoingPasswordBitStream.Write( passwordData, passwordDataLength );
		
	rakPeerMutexes[ outgoingPasswordBitStream_Mutex ].Unlock();
	
	// If the host starts with something other than 0, 1, or 2 it's (probably) a domain name.
	if ( host[ 0 ] < '0' || host[ 0 ] > '2' )
	{
		host = ( char* ) SocketLayer::Instance() ->DomainNameToIP( host );
	}
	
	// Connecting to ourselves in the same instance of the program?
	if ( ( strcmp( host, "127.0.0.1" ) == 0 || strcmp( host, "0.0.0.0" ) == 0 ) && remotePort == myPlayerId.port )
	{
		// Feedback loop.
		
		if ( GetNumberOfIncomingConnections() + 1 > maximumIncomingConnections )
		{
			// Tell the game that this person has connected
			Packet * p;
			p = PacketPool::Instance() ->GetPointer();
			
			p->data = new unsigned char [ 1 ];
			p->data[ 0 ] = ( unsigned char ) ID_NO_FREE_INCOMING_CONNECTIONS;
			p->playerId = myPlayerId;
			p->playerIndex = ( PlayerIndex ) GetIndexFromPlayerID( myPlayerId );
			p->length = 1;
			
#ifdef _DEBUG
			
			assert( p->data );
#endif
			
			incomingQueueMutex.Lock();
			incomingPacketQueue.push( p );
			incomingQueueMutex.Unlock();
		}
		
		else
		{
			// Just assume we are connected.  This is really just for testing.
			RemoteSystemStruct* remoteSystem = AssignPlayerIDToRemoteSystemList( myPlayerId, 0, false );
			
			if ( remoteSystem != 0 )
			{
				ResetRemoteSystemData( remoteSystem, true );
				
				/*
				// Send the connection request complete to the game
				Packet *packet = PacketPool::Instance()->GetPointer();
				packet->data = new char[1];
				packet->data[0]=ID_NEW_INCOMING_CONNECTION;
				packet->length=sizeof(char);
				packet->bitSize=sizeof(char)*8;
				packet->playerId=myPlayerId;
				incomingQueueMutex.Lock();
				incomingPacketQueue.push(packet);
				incomingQueueMutex.Unlock();
				*/
				
				// Tell the remote system via the reliability layer that we connected
				NewIncomingConnectionStruct newIncomingConnectionStruct;
				newIncomingConnectionStruct.typeId = ID_NEW_INCOMING_CONNECTION;
				newIncomingConnectionStruct.externalID = myPlayerId;
				Send( ( char* ) & newIncomingConnectionStruct, sizeof( newIncomingConnectionStruct ), SYSTEM_PRIORITY, RELIABLE, 0, myPlayerId, false );
				
				return true;
			}
			
			else
				return false;
		}
	}
	
	RecordConnectionAttempt( host, remotePort );
	
	return SendConnectionRequest( host, remotePort );
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Stops the network threads and close all connections.  Multiple calls are ok.
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::Disconnect( unsigned long blockDuration , unsigned char orderingChannel )
{
	unsigned i;
	unsigned short maxPeers = maximumNumberOfPeers; // This is done for threading reasons
	
	// Call close connection in a loop for all open connections.
	
	for ( i = 0; i < maxPeers; i++ )
	{
		// CloseConnection uses maximumNumberOfPeers
		CloseConnection( remoteSystemList[ i ].playerId, true, blockDuration );
		
	}
	
	// Setting this to 0 allows remoteSystemList to be reallocated in Initialize and prevents threads from accessing the reliability layer
	maximumNumberOfPeers = 0;
	
	if ( endThreads == false )
	{
		// Stop the threads
		endThreads = true;
		
		// Normally the thread will call DecreaseUserCount on termination but if we aren't using threads just do it
		// manually
#ifdef __USE_IO_COMPLETION_PORTS
		
		AsynchronousFileIO::Instance() ->DecreaseUserCount();
#endif
		
	}
	
	while ( isMainLoopThreadActive )
#ifdef _WIN32
	
		Sleep( 10 );
		
#else
		
		usleep( 10 * 1000 );
		
#endif
		
	if ( connectionSocket != INVALID_SOCKET )
	{
		closesocket( connectionSocket );
		connectionSocket = INVALID_SOCKET;
	}
	
	// Write to ourselves to unblock if necessary
	// if (isSocketLayerBlocking==true)
	// {
	//  char c=255;
	//  SocketLayer::Instance()->SendTo(connectionSocket, &c, 1, "127.0.0.1", myPlayerId.port);
	// }
	
	// while(isRecvfromThreadActive)
	//#ifdef _WIN32
	//  Sleep(10);
	//#else
	//  usleep(10 * 1000);
	//#endif
	
	// isSocketLayerBlocking=false;
	
	// if (connectionSocket != INVALID_SOCKET)
	// {
	//  closesocket(connectionSocket);
	//  connectionSocket = INVALID_SOCKET;
	// }
	
	// Clear out the queues
	while ( incomingPacketQueue.size() )
		PacketPool::Instance() ->ReleasePointer( incomingPacketQueue.pop() );
		
	/*
	  synchronizedMemoryQueueMutex.Lock();
	  while (synchronizedMemoryPacketQueue.size())
	  PacketPool::Instance()->ReleasePointer(synchronizedMemoryPacketQueue.pop());
	  synchronizedMemoryQueueMutex.Unlock();
	*/
	
	bytesSentPerSecond = bytesReceivedPerSecond = 0;
	
	rakPeerMutexes[ RakPeer::requestedConnections_MUTEX ].Lock();
	
	for ( i = 0; i < requestedConnectionsList.size(); i++ )
		delete requestedConnectionsList[ i ];
		
	requestedConnectionsList.clear();
	
	rakPeerMutexes[ RakPeer::requestedConnections_MUTEX ].Unlock();
	
	
	// Clear out the reliabilty layer list in case we want to reallocate it in a successive call to Init.
	RemoteSystemStruct * temp = remoteSystemList;
	
	remoteSystemList = 0;
	
	delete [] temp;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Returns true if the network threads are running
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
bool RakPeer::IsActive( void ) const
{
	return endThreads == false;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Fills the array remoteSystems with the playerID of all the systems we are connected to
//
// Parameters:
// remoteSystems (out): An array of PlayerID structures to be filled with the PlayerIDs of the systems we are connected to
// - pass 0 to remoteSystems to only get the number of systems we are connected to
// numberOfSystems (int, out): As input, the size of remoteSystems array.  As output, the number of elements put into the array
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
bool RakPeer::GetConnectionList( PlayerID *remoteSystems, unsigned short *numberOfSystems ) const
{
	int count, index;
	
	if ( remoteSystemList == 0 || endThreads == true )
	{
		*numberOfSystems = 0;
		return false;
	}
	
	// This is called a lot so unroll the loop
	if ( remoteSystems )
	{
		for ( count = 0, index = 0; index < maximumNumberOfPeers; ++index )
			if ( remoteSystemList[ index ].playerId != UNASSIGNED_PLAYER_ID )
			{
				if ( count < *numberOfSystems )
					remoteSystems[ count ] = remoteSystemList[ index ].playerId;
					
				++count;
			}
			
	}
	
	else
	{
		for ( count = 0, index = 0; index < maximumNumberOfPeers; ++index )
			if ( remoteSystemList[ index ].playerId != UNASSIGNED_PLAYER_ID )
				++count;
	}
	
	*numberOfSystems = ( unsigned short ) count;
	
	return 0;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Sends a block of data to the specified system that you are connected to.
// This function only works while the client is connected (Use the Connect function).
//
// Parameters:
// data: The block of data to send
// length: The size in bytes of the data to send
// bitStream: The bitstream to send
// priority: What priority level to send on.
// reliability: How reliability to send this data
// orderingChannel: When using ordered or sequenced packets, what channel to order these on.
// - Packets are only ordered relative to other packets on the same stream
// playerId: Who to send this packet to, or in the case of broadcasting who not to send it to. Use UNASSIGNED_PLAYER_ID to specify none
// broadcast: True to send this packet to all connected systems.  If true, then playerId specifies who not to send the packet to.
// Returns:
// False if we are not connected to the specified recipient.  True otherwise
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
bool RakPeer::Send( char *data, const long length, PacketPriority priority, PacketReliability reliability, unsigned orderingChannel, PlayerID playerId, bool broadcast )
{
#ifdef _DEBUG
	assert( data && length > 0 );
#endif
	
	if ( data == 0 || length < 0 )
		return false;
		
	RakNet::BitStream temp( data, length, false );
	
	return Send( &temp, priority, reliability, orderingChannel, playerId, broadcast );
	
}

bool RakPeer::Send( RakNet::BitStream * bitStream, PacketPriority priority, PacketReliability reliability, unsigned orderingChannel, PlayerID playerId, bool broadcast )
{
#ifdef _DEBUG
	assert( bitStream->GetNumberOfBytesUsed() > 0 );
#endif
	
	if ( bitStream->GetNumberOfBytesUsed() == 0 )
		return false;
		
	if ( remoteSystemList == 0 || endThreads == true )
		return false;
		
	if ( broadcast == false && playerId == UNASSIGNED_PLAYER_ID )
		return false;
		
	unsigned remoteSystemIndex;
	
	for ( remoteSystemIndex = 0; remoteSystemIndex < maximumNumberOfPeers; remoteSystemIndex++ )
		if ( remoteSystemList[ remoteSystemIndex ].playerId != UNASSIGNED_PLAYER_ID &&
			( ( broadcast == false && remoteSystemList[ remoteSystemIndex ].playerId == playerId ) ||
			  ( broadcast == true && remoteSystemList[ remoteSystemIndex ].playerId != playerId ) )
		   )
		{
		
			if ( trackFrequencyTable )
			{
				unsigned numberOfBytesUsed = bitStream->GetNumberOfBytesUsed();
				
				// Store output frequency
				
				for ( unsigned i = 0; i < numberOfBytesUsed; i++ )
				{
					frequencyTable[ bitStream->GetData() [ i ] ] ++;
				}
				
				rawBytesSent += numberOfBytesUsed;
			}
			
			if ( outputTree )
			{
				RakNet::BitStream bitStreamCopy( bitStream->GetNumberOfBytesUsed() );
				outputTree->EncodeArray( bitStream->GetData(), bitStream->GetNumberOfBytesUsed(), &bitStreamCopy );
				compressedBytesSent += bitStreamCopy.GetNumberOfBytesUsed();
				remoteSystemList[ remoteSystemIndex ].reliabilityLayer.Send( &bitStreamCopy, priority, reliability, orderingChannel, true, MTUSize );
			}
			
			else
				remoteSystemList[ remoteSystemIndex ].reliabilityLayer.Send( bitStream, priority, reliability, orderingChannel, true, MTUSize );
				
			if ( broadcast == false )
				return true;
		}
		
	return true;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Gets a packet from the incoming packet queue. Use DeallocatePacket to deallocate the packet after you are done with it.
// Check the Packet struct at the top of CoreNetworkStructures.h for the format of the struct
//
// Returns:
// 0 if no packets are waiting to be handled, otherwise an allocated packet
// If the client is not active this will also return 0, as all waiting packets are flushed when the client is Disconnected
// This also updates all memory blocks associated with synchronized memory and distributed objects
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Packet* RakPeer::Receive( void )
{
	if ( !( IsActive() ) )
		return 0;
		
	// Only one thread should call RunUpdateCycle at a time.  We don't need to delay calls so
	// a mutex on the function is not necessary - only on the variable that indicates if the function is
	// running
	// lastUserUpdateCycle=RakNet::GetTime();
	// RunMutexedUpdateCycle();
	
	
	// Prepare to write out a bitstream containing all the synchronization data
	// RakNet::BitStream *bitStream=0;
	/*
	  automaticVariableSynchronizationMutex.Lock();
	 
	  for (UniqueIDType i=0; i < automaticVariableSynchronizationList.size(); i++)
	  {
	  if (automaticVariableSynchronizationList[i])
	  {
	  #ifdef _DEBUG
	  assert(automaticVariableSynchronizationList[i]->size()>0);
	  #endif
	  for (unsigned j=0; j < automaticVariableSynchronizationList[i]->size(); j++)
	  {
	  // Just copy the data to memoryBlock so it's easier to access
	  MemoryBlock memoryBlock = (*(automaticVariableSynchronizationList[i]))[j];
	  automaticVariableSynchronizationMutex.Unlock();
	 
	  if (memoryBlock.isAuthority) // If this is not the authoritative block then ignore it
	  {
	  bool doSynchronization;
	  if (memoryBlock.synchronizationRules) // If the user defined synchronization rules then use them
	  doSynchronization=memoryBlock.synchronizationRules(memoryBlock.original, memoryBlock.copy);
	  else
	  // If the user did not define synchronization rules then just synchronize them whenever the memory is different
	  doSynchronization = (memcmp(memoryBlock.original, memoryBlock.copy, memoryBlock.size)!=0);
	 
	  if (doSynchronization)
	  {
	  if (bitStream==0)
	  {
	  bitStream=new BitStream(memoryBlock.size + 1 + 2 + 2);
	  // Stream header, use WriteBits instead of Write so the BitStream class does not use the TYPE_CHECKING
	  // define and add an extra identifier byte at the front of the stream.  This way
	  // the first byte of the stream will correctly be ID_SYNCHRONIZE_MEMORY
	  unsigned char ch=ID_SYNCHRONIZE_MEMORY;
	  bitStream->WriteBits((unsigned char*)&ch, sizeof(unsigned char)*8, false);
	  }
	  bitStream->Write(i); // First write the unique ID
	  // If there is a secondary ID, write 1 and then it.  Otherwise write 0
	  if (memoryBlock.secondaryID!=UNASSIGNED_OBJECT_ID)
	  {
	  bitStream->Write(true);
	  bitStream->WriteCompressed(memoryBlock.secondaryID);
	  }
	  else
	  {
	  bitStream->Write(false);
	  }
	  // Write the length of the memory block
	  bitStream->WriteCompressed(memoryBlock.size);
	  // Write the new memory block
	  bitStream->Write(memoryBlock.original, memoryBlock.size);
	  // Save the updated memory
	  memcpy(memoryBlock.copy, memoryBlock.original, memoryBlock.size);
	  }
	  }
	 
	  automaticVariableSynchronizationMutex.Lock();
	  }
	  }
	  }
	 
	  automaticVariableSynchronizationMutex.Unlock();
	 
	  if (bitStream)
	  {
	  // Send out this data
	  Send(bitStream, HIGH_PRIORITY, RELIABLE_ORDERED, 0, UNASSIGNED_PLAYER_ID, true, false);
	  delete bitStream;
	  }
	 
	  synchronizedMemoryQueueMutex.Lock();
	  while (synchronizedMemoryPacketQueue.size())
	  {
	  Packet *pack = synchronizedMemoryPacketQueue.pop();
	  #ifdef _DEBUG
	  assert(data[0]==ID_SYNCHRONIZE_MEMORY);
	  assert(length > 2);
	  #endif
	 
	  // Push the data into a bitstream for easy parsing
	  RakNet::BitStream bitStream(data+1, length-1, false);
	  UniqueIDType uniqueID;
	  bool hasSecondaryID;
	  ObjectID secondaryID;
	  unsigned short memoryBlockSize;
	  char *externalMemoryBlock;
	 
	  while (bitStream.GetNumberOfUnreadBits()>0) // Just read until we can't read anymore
	  {
	  if (bitStream.Read(uniqueID)==false)
	  break;
	  if (bitStream.Read(hasSecondaryID)==false)
	  break;
	  if (hasSecondaryID)
	  {
	  if (bitStream.ReadCompressed(secondaryID)==false)
	  break;
	  }
	  if (bitStream.ReadCompressed(memoryBlockSize)==false)
	  break;
	 
	  automaticVariableSynchronizationMutex.Lock();
	  if (uniqueID >= automaticVariableSynchronizationList.size() ||
	  automaticVariableSynchronizationList[uniqueID]==0 ||
	  (hasSecondaryID==false && automaticVariableSynchronizationList[uniqueID]->size()>1))
	  {
	  automaticVariableSynchronizationMutex.Unlock();
	  return; // Unknown identifier
	  }
	 
	  if (hasSecondaryID)
	  {
	  externalMemoryBlock=0;
	  // One or more elements in this list uniquely identified.  Find it to get the outside data pointer
	  for (unsigned i=0; i < automaticVariableSynchronizationList[uniqueID]->size(); i++)
	  {
	  if ( (*(automaticVariableSynchronizationList[uniqueID]))[i].secondaryID==secondaryID)
	  {
	  externalMemoryBlock=(*(automaticVariableSynchronizationList[uniqueID]))[i].original;
	  break;
	  }
	  }
	  }
	  else
	  // If no secondary identifier then the list only contains one element so the data we are looking for is at index 0
	  externalMemoryBlock=(*(automaticVariableSynchronizationList[uniqueID]))[0].original;
	 
	  automaticVariableSynchronizationMutex.Unlock();
	 
	  if (externalMemoryBlock==0)
	  {
	  // Couldn't find the specified data
	  bitStream.IgnoreBits(memoryBlockSize*8);
	  }
	  else
	  {
	  // Found the specified data, read the new data into it
	  if (bitStream.Read(externalMemoryBlock, memoryBlockSize)==false)
	  break;
	  }
	  }
	  PacketPool::Instance()->ReleasePointer(pack);
	  }
	  synchronizedMemoryQueueMutex.Unlock();
	*/
	
	Packet *val;
	
	int offset;
	
	while ( 1 )
	{
		incomingQueueMutex.Lock();
		
		if ( incomingPacketQueue.size() > 0 )
		{
			val = incomingPacketQueue.pop();
		}
		
		else
		{
			incomingQueueMutex.Unlock();
			return 0;
		}
		
		incomingQueueMutex.Unlock();
		
		// Do RPC calls from the user thread, not the network update thread
		
		if ( val->data[ 0 ] == ID_RPC || val->data[ 0 ] == ID_TIMESTAMP ) //fake
		{
			HandleRPCPacket( ( char* ) val->data, val->length, val->playerId );
			DeallocatePacket( val );
		}
		
		else
			break; // Send the packet to the user
	}
	
	
#ifdef _DEBUG
	assert( val->data );
	
#endif
	
	if ( ( val->length >= sizeof( unsigned char ) + sizeof( long ) ) &&
		( ( unsigned char ) val->data[ 0 ] == ID_TIMESTAMP ) )
	{
		offset = sizeof( unsigned char );
		ShiftIncomingTimestamp( ( char* ) val->data + offset, val->playerId );
	}
	
	return val;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Call this to deallocate a packet returned by Receive when you are done handling it.
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::DeallocatePacket( Packet *packet )
{
	if ( packet == 0 )
		return ;
		
	PacketPool::Instance() ->ReleasePointer( packet );
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Return the total number of connections we are allowed
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
unsigned short RakPeer::GetMaximumNumberOfPeers( void ) const
{
	return maximumNumberOfPeers;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Register a C function as available for calling as a remote procedure call
//
// Parameters:
// uniqueID: A null terminated non-case senstive string of only letters to identify this procedure
// functionName(...): The name of the C function or C++ singleton to be used as a function pointer
// This can be called whether the client is active or not, and registered functions stay registered unless unregistered with
// UnregisterAsRemoteProcedureCall
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::RegisterAsRemoteProcedureCall( char* uniqueID, void ( *functionName ) ( char *input, int numberOfBitsOfData, PlayerID sender ) )
{
	if ( uniqueID == 0 || uniqueID[ 0 ] == 0 || functionName == 0 )
		return ;
		
#ifdef _DEBUG
		
	assert( strlen( uniqueID ) < 256 );
	
#endif
	
	char uppercaseUniqueID[ 256 ];
	
	int counter = 0;
	
	while ( uniqueID[ counter ] )
	{
		uppercaseUniqueID[ counter ] = ( char ) toupper( uniqueID[ counter ] );
		counter++;
	}
	
	uppercaseUniqueID[ counter ] = 0;
	
	// Each id must be unique
#ifdef _DEBUG
	
	assert( rpcTree.is_in( RPCNode( uppercaseUniqueID, functionName ) ) == false );
#endif
	
	rpcTree.add( RPCNode( uppercaseUniqueID, functionName ) );
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Unregisters a C function as available for calling as a remote procedure call that was formerly registered
// with RegisterAsRemoteProcedureCall
//
// Parameters:
// uniqueID: A null terminated non-case senstive string of only letters to identify this procedure.  Must match the parameter
// passed to RegisterAsRemoteProcedureCall
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::UnregisterAsRemoteProcedureCall( char* uniqueID )
{
	if ( uniqueID == 0 || uniqueID[ 0 ] == 0 )
		return ;
		
#ifdef _DEBUG
		
	assert( strlen( uniqueID ) < 256 );
	
#endif
	
	char uppercaseUniqueID[ 256 ];
	
	strcpy( uppercaseUniqueID, uniqueID );
	
	int counter = 0;
	
	while ( uniqueID[ counter ] )
	{
		uppercaseUniqueID[ counter ] = ( char ) toupper( uniqueID[ counter ] );
		counter++;
	}
	
	uppercaseUniqueID[ counter ] = 0;
	
	// Unique ID must exist
#ifdef _DEBUG
	
	assert( rpcTree.is_in( RPCNode( uppercaseUniqueID, 0 ) ) == true );
#endif
	
	rpcTree.del( RPCNode( uppercaseUniqueID, 0 ) );
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Calls a C function on the server that the server already registered using RegisterAsRemoteProcedureCall
// If you want that function to return data you should call RPC from that system in the same way
// Returns true on a successful packet send (this does not indicate the recipient performed the call), false on failure
//
// Parameters:
// uniqueID: A null terminated non-case senstive string of only letters to identify this procedure.  Must match the parameter
// data: The block of data to send
// length: The size in BITS of the data to send
// bitStream: The bitstream to send
// priority: What priority level to send on.
// reliability: How reliability to send this data
// orderingChannel: When using ordered or sequenced packets, what channel to order these on.
// broadcast - Send this packet to everyone.
// playerId: Who to send this packet to, or in the case of broadcasting who not to send it to. Use UNASSIGNED_PLAYER_ID to specify none
// broadcast: True to send this packet to all connected systems.  If true, then playerId specifies who not to send the packet to.
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
bool RakPeer::RPC( int* uniqueID, char *data, unsigned long bitLength, PacketPriority priority, PacketReliability reliability, unsigned orderingChannel, PlayerID playerId, bool broadcast, bool shiftTimestamp )
{
	RakNet::BitStream temp( data, BITS_TO_BYTES( bitLength ), false );
	
	if ( data )
		return RPC( uniqueID, &temp, priority, reliability, orderingChannel, playerId, broadcast, shiftTimestamp );
	else
		return RPC( uniqueID, 0, priority, reliability, orderingChannel, playerId, broadcast, shiftTimestamp );
}

bool RakPeer::RPC( int* uniqueID, RakNet::BitStream *bitStream, PacketPriority priority, PacketReliability reliability, unsigned orderingChannel, PlayerID playerId, bool broadcast, bool shiftTimestamp )
{
#ifdef _DEBUG
	assert( uniqueID && uniqueID[ 0 ] );
#endif
	
	if ( uniqueID == 0 )
		return false;
		
	if ( *uniqueID > 256 )
	{
#ifdef _DEBUG
		assert( 0 );
#endif
		
		return false; // Unique ID is too long
	}
	
	if ( shiftTimestamp && bitStream && ( bitStream->GetNumberOfBytesUsed() < sizeof( unsigned long ) ) )
	{
		assert( 0 ); // Not enough bits to shift!
		return false;
	}
	/*
	RakNet::BitStream outgoingBitStream;
	unsigned char uniqueIDLength, ch;
	uniqueIDLength = ( unsigned char ) strlen( uniqueID );
	
	// First write the ID, then write the size of the unique ID in characters, then the unique ID, then write the length of the data in bits, then write the data
	
	if ( shiftTimestamp )
		outgoingBitStream.Write( ( unsigned char ) ID_RPC_WITH_TIMESTAMP );
	else
		outgoingBitStream.Write( ( unsigned char ) ID_RPC );
		
	outgoingBitStream.WriteCompressed( uniqueIDLength );
	
	for ( int counter = 0; uniqueID[ counter ]; counter++ )
	{
		ch = ( unsigned char ) toupper( uniqueID[ counter ] );
		// Dev-C++ doesn't support toupper.  How lame.
		//  if (uniqueID[counter] > 'Z')
		// uniqueID[counter]-='a'-'A';
		
		if ( ch < 'A' || ch > 'Z' )
		{
#ifdef _DEBUG
			assert( 0 );
#endif
			
			return false; // Only letters allowed
		}
		
		// Make the range of the char from 0 to 32
		ch -= 'A';
		
		outgoingBitStream.WriteBits( ( unsigned char* ) & ch, 5 ); // Write the char with 5 bits
	}
	
	if ( bitStream )
		outgoingBitStream.WriteCompressed( bitStream->GetNumberOfBitsUsed() );
	else
		outgoingBitStream.WriteCompressed( ( int ) 0 );
		
	// False to write the raw data from another bitstream, rather than shifting from user data
	if ( bitStream && bitStream->GetNumberOfBitsUsed() > 0 )
		outgoingBitStream.WriteBits( bitStream->GetData(), bitStream->GetNumberOfBitsUsed(), false );
		
	// For testing
	// HandleRPCPacket((char*)outgoingBitStream.GetData(), outgoingBitStream.GetNumberOfBytesUsed(), UNASSIGNED_PLAYER_ID);
	*/

	return TRUE;
	//return Send( &outgoingBitStream, priority, reliability, orderingChannel, playerId, broadcast );
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Close the connection to another host (if we initiated the connection it will disconnect, if they did it will kick them out).
//
// Parameters:
// target: Which connection to close
// sendDisconnectionNotification: True to send ID_DISCONNECTION_NOTIFICATION to the recipient. False to close it silently.
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::CloseConnection( PlayerID target, bool sendDisconnectionNotification, unsigned long blockDuration )
{
	unsigned i, stopWaitingTime;
	
	if ( remoteSystemList == 0 || endThreads == true )
		return ;
		
	if ( sendDisconnectionNotification )
	{
		unsigned char c = ID_DISCONNECTION_NOTIFICATION;
		Send( ( char* ) & c, sizeof( c ), SYSTEM_PRIORITY, RELIABLE, 0, target, false );
		lastUserUpdateCycle = RakNet::GetTime();
		//  RunMutexedUpdateCycle();
	}
	
	i = 0;
	rakPeerMutexes[ RakPeer::remoteSystemList_Mutex ].Lock();
	
	for ( ; i < maximumNumberOfPeers; i++ )
		if ( remoteSystemList[ i ].playerId == target )
		{
			// Send out any last packets
			// Update isn't thread safe to call outside of the internal thread
			// remoteSystemList[i].reliabilityLayer.Update(connectionSocket, remoteSystemList[i].playerId, MTUSize);
			
			if ( blockDuration >= 0 )
			{
				stopWaitingTime = RakNet::GetTime() + blockDuration;
				
				while ( RakNet::GetTime() < stopWaitingTime )
				{
					// If this system is out of packets to send, then stop waiting
					
					if ( remoteSystemList[ i ].reliabilityLayer.GetStatistics() ->messageSendBuffer[ SYSTEM_PRIORITY ] == 0 )
						break;
						
					// This will probably cause the update thread to run which will probably
					// send the disconnection notification
#ifdef _WIN32
					
					Sleep( 0 );
					
#else
					
					usleep( 0 * 1000 );
					
#endif
					//     lastUserUpdateCycle=RakNet::GetTime();
					//     RunMutexedUpdateCycle();
				}
			}
			
			// Reserve this reliability layer for ourselves
			remoteSystemList[ i ].playerId = UNASSIGNED_PLAYER_ID; // This one line causes future incoming packets to go through the reliability layer
			
			// Remove any remaining packets
			remoteSystemList[ i ].reliabilityLayer.Reset();
			
			break;
		}
		
	rakPeerMutexes[ remoteSystemList_Mutex ].Unlock();
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Given a playerID, returns an index from 0 to the maximum number of players allowed - 1.
//
// Parameters
// playerId - The playerID to search for
//
// Returns
// An integer from 0 to the maximum number of peers -1, or -1 if that player is not found
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
int RakPeer::GetIndexFromPlayerID( PlayerID playerId )
{
	unsigned i;
	
	if ( playerId == UNASSIGNED_PLAYER_ID )
		return -1;
		
	for ( i = 0; i < maximumNumberOfPeers; i++ )
		if ( remoteSystemList[ i ].playerId == playerId )
			return i;
			
	return -1;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// This function is only useful for looping through all players.
//
// Parameters
// index - an integer between 0 and the maximum number of players allowed - 1.
//
// Returns
// A valid playerID or UNASSIGNED_PLAYER_ID if no such player at that index
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
PlayerID RakPeer::GetPlayerIDFromIndex( int index )
{
	if ( index >= 0 && index < maximumNumberOfPeers )
		return remoteSystemList[ index ].playerId;
		
	return UNASSIGNED_PLAYER_ID;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Bans an IP from connecting. Banned IPs persist between connections.
//
// Parameters
// IP - Dotted IP address.  Can use * as a wildcard, such as 128.0.0.* will ban
// All IP addresses starting with 128.0.0
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::AddToBanList( const char *IP )
{
	unsigned index;
	char *IPCopy;
	
	if ( IP == 0 || IP[ 0 ] == 0 || strlen( IP ) > 15 )
		return ;
		
	// If this guy is already in the ban list, do nothing
	index = 0;
	
	banListMutex.Lock();
	
	for ( ; index < banList.size(); index++ )
	{
		if ( strcmp( IP, banList[ index ] ) == 0 )
		{
			banListMutex.Unlock();
			return ;
		}
	}
	
	banListMutex.Unlock();
	
	IPCopy = new char [ 16 ];
	strcpy( IPCopy, IP );
	banListMutex.Lock();
	banList.insert( IPCopy );
	banListMutex.Unlock();
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Allows a previously banned IP to connect.
//
// Parameters
// IP - Dotted IP address.  Can use * as a wildcard, such as 128.0.0.* will ban
// All IP addresses starting with 128.0.0
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::RemoveFromBanList( const char *IP )
{
	unsigned index;
	char *temp;
	
	if ( IP == 0 || IP[ 0 ] == 0 || strlen( IP ) > 15 )
		return ;
		
	index = 0;
	
	temp = 0;
	
	banListMutex.Lock();
	
	for ( ; index < banList.size(); index++ )
	{
		if ( strcmp( IP, banList[ index ] ) == 0 )
		{
			temp = banList[ index ];
			banList[ index ] = banList[ banList.size() - 1 ];
			banList.del( banList.size() - 1 );
			break;
		}
	}
	
	banListMutex.Unlock();
	
	if ( temp )
		delete [] temp;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Allows all previously banned IPs to connect.
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::ClearBanList( void )
{
	unsigned index;
	index = 0;
	banListMutex.Lock();
	
	for ( ; index < banList.size(); index++ )
		delete [] banList[ index ];
		
	banList.clear();
	
	banListMutex.Unlock();
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Determines if a particular IP is banned.
//
// Parameters
// IP - Complete dotted IP address
//
// Returns
// True if IP matches any IPs in the ban list, accounting for any wildcards.
// False otherwise.
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
bool RakPeer::IsBanned( const char *IP )
{
	unsigned banListIndex, characterIndex;
	
	if ( IP == 0 || IP[ 0 ] == 0 || strlen( IP ) > 15 )
		return false;
		
	banListIndex = 0;
	
	if ( banList.size() == 0 )
		return false; // Skip the mutex if possible
		
	banListMutex.Lock();
	
	for ( ; banListIndex < banList.size(); banListIndex++ )
	{
		characterIndex = 0;
		
		while ( true )
		{
			if ( banList[ banListIndex ][ characterIndex ] == IP[ characterIndex ] )
			{
				// Equal characters
				
				if ( IP[ characterIndex ] == 0 )
				{
					banListMutex.Unlock();
					
					// End of the string and the strings match
					return true;
				}
				
				characterIndex++;
			}
			
			else
			{
				if ( banList[ banListIndex ][ characterIndex ] == 0 || IP[ characterIndex ] == 0 )
				{
					// End of one of the strings
					break;
				}
				
				// Characters do not match
				if ( banList[ banListIndex ][ characterIndex ] == '*' )
				{
					banListMutex.Unlock();
					
					// Domain is banned.
					return true;
				}
				
				// Characters do not match and it is not a *
				break;
			}
		}
	}
	
	banListMutex.Unlock();
	
	// No match found.
	return false;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Send a ping to the specified connected system.
//
// Parameters:
// target - who to ping
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::Ping( PlayerID target )
{
	if ( IsActive() == false )
		return ;
		
	PingStruct ping;
	
	ping.typeId = ID_PING;
	
	ping.sendPingTime = RakNet::GetTime();
	
	Send( ( char* ) & ping, sizeof( PingStruct ), SYSTEM_PRIORITY, UNRELIABLE, 0, target, false );
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Send a ping to the specified unconnected system.
// The remote system, if it is Initialized, will respond with ID_PONG.
// The final ping time will be encoded in the following 4 bytes (2-5) as an unsigned long
//
// Requires:
// The sender and recipient must already be started via a successful call to Initialize
//
// Parameters:
// host: Either a dotted IP address or a domain name.  Can be 255.255.255.255 for LAN broadcast.
// remotePort: Which port to connect to on the remote machine.
// onlyReplyOnAcceptingConnections: Only request a reply if the remote system has open connections
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::Ping( char* host, unsigned short remotePort, bool onlyReplyOnAcceptingConnections )
{
	if ( host == 0 )
		return ;
		
	// If the host starts with something other than 0, 1, or 2 it's (probably) a domain name.
	if ( host[ 0 ] < '0' || host[ 0 ] > '2' )
	{
		host = ( char* ) SocketLayer::Instance() ->DomainNameToIP( host );
	}
	
	UnconnectedPingStruct s;
	
	if ( onlyReplyOnAcceptingConnections )
		s.typeId = ID_PING_OPEN_CONNECTIONS;
	else
		s.typeId = ID_PING;
		
	s.sendPingTime = RakNet::GetTime();
	
	SocketLayer::Instance() ->SendTo( connectionSocket, ( char* ) & s, sizeof( UnconnectedPingStruct ), ( char* ) host, remotePort );
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Returns the average of all ping times read for a specified target
//
// Parameters:
// target - whose time to read
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
int RakPeer::GetAveragePing( PlayerID target )
{
	int sum, quantity;
	RemoteSystemStruct *remoteSystem = GetRemoteSystemFromPlayerID( target );
	
	if ( remoteSystem == 0 )
		return -1;
		
	for ( sum = 0, quantity = 0; quantity < PING_TIMES_ARRAY_SIZE; quantity++ )
	{
		if ( remoteSystem->pingAndClockDifferential[ quantity ].pingTime == -1 )
			break;
		else
			sum += remoteSystem->pingAndClockDifferential[ quantity ].pingTime;
	}
	
	if ( quantity > 0 )
		return sum / quantity;
	else
		return -1;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Returns the last ping time read for the specific player or -1 if none read yet
//
// Parameters:
// target - whose time to read
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
int RakPeer::GetLastPing( PlayerID target ) const
{
	RemoteSystemStruct * remoteSystem = GetRemoteSystemFromPlayerID( target );
	
	if ( remoteSystem == 0 )
		return -1;
		
	if ( remoteSystem->pingAndClockDifferentialWriteIndex == 0 )
		return remoteSystem->pingAndClockDifferential[ PING_TIMES_ARRAY_SIZE - 1 ].pingTime;
	else
		return remoteSystem->pingAndClockDifferential[ remoteSystem->pingAndClockDifferentialWriteIndex - 1 ].pingTime;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Returns the lowest ping time read or -1 if none read yet
//
// Parameters:
// target - whose time to read
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
int RakPeer::GetLowestPing( PlayerID target ) const
{
	RemoteSystemStruct * remoteSystem = GetRemoteSystemFromPlayerID( target );
	
	if ( remoteSystem == 0 )
		return -1;
		
	return remoteSystem->lowestPing;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Ping the remote systems every so often.  This is off by default
// This will work anytime
//
// Parameters:
// doPing - True to start occasional pings.  False to stop them.
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::SetOccasionalPing( bool doPing )
{
	occasionalPing = doPing;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Automatically synchronizes a block of memory between systems.
// Can be called anytime.  Calling it before a connection is initiated will cause the data to be synchronized on connection
//
// Parameters:
// uniqueIdentifier: an integer (enum) corresponding to the same variable between clients and the server.  Start the indexing at 0
// memoryBlock: Pointer to the data you want to read from or write to
// size: Size of memoryBlock in bytes
// isAuthority: True to tell all connected systems to match their data to yours.  Data changes are relayed to the authoritative
// - client which broadcasts the change
// synchronizationRules: Optional function pointer that decides whether or not to update changed memory.  It should
// - return true if the two passed memory blocks are sufficiently different to synchronize them.  This is an optimization so
// - data that changes rapidly, such as per-frame, can be made to not update every frame
// - The first parameter to synchronizationRules is the new data, the second is the internal copy of the old data
// secondaryUniqueIdentifier:  Optional and used when you have the same unique identifier and is intended for multiple instances of a class
// - that derives from NetworkObject.
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
/*
  void RakPeer::SynchronizeMemory(UniqueIDType uniqueIdentifier, char *memoryBlock, unsigned short size, bool isAuthority, bool (*synchronizationRules) (char*,char*),ObjectID secondaryUniqueIdentifier)
  {
  automaticVariableSynchronizationMutex.Lock();
  if (uniqueIdentifier >= automaticVariableSynchronizationList.size() || automaticVariableSynchronizationList[uniqueIdentifier]==0)
  {
  automaticVariableSynchronizationList.replace(new BasicDataStructures::List<MemoryBlock>, 0, uniqueIdentifier);
  }
  else
  {
  // If we are using a secondary identifier, make sure that is unique
  #ifdef _DEBUG
  assert(secondaryUniqueIdentifier!=UNASSIGNED_OBJECT_ID);
  #endif
  if (secondaryUniqueIdentifier==UNASSIGNED_OBJECT_ID)
  {
  automaticVariableSynchronizationMutex.Unlock();
  return; // Cannot add to an existing list without a secondary identifier
  }
 
  for (unsigned i=0; i < automaticVariableSynchronizationList[uniqueIdentifier]->size(); i++)
  {
  #ifdef _DEBUG
  assert ((*(automaticVariableSynchronizationList[uniqueIdentifier]))[i].secondaryID != secondaryUniqueIdentifier);
  #endif
  if ((*(automaticVariableSynchronizationList[uniqueIdentifier]))[i].secondaryID == secondaryUniqueIdentifier)
  {
  automaticVariableSynchronizationMutex.Unlock();
  return; // Already used
  }
  }
  }
  automaticVariableSynchronizationMutex.Unlock();
 
  MemoryBlock newBlock;
  newBlock.original=memoryBlock;
  if (isAuthority)
  {
  newBlock.copy = new char[size];
  #ifdef _DEBUG
  assert(sizeof(char)==1);
  #endif
  memset(newBlock.copy, 0, size);
  }
  else
  newBlock.copy = 0; // no need to keep a copy if we are only receiving changes
  newBlock.size=size;
  newBlock.secondaryID=secondaryUniqueIdentifier;
  newBlock.isAuthority=isAuthority;
  newBlock.synchronizationRules=synchronizationRules;
 
  automaticVariableSynchronizationMutex.Lock();
  automaticVariableSynchronizationList[uniqueIdentifier]->insert(newBlock);
  automaticVariableSynchronizationMutex.Unlock();
  }
 
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Description:
// Stops synchronization of a block of memory previously defined by uniqueIdentifier and secondaryUniqueIdentifier
// by the call to SynchronizeMemory
// CALL THIS BEFORE SYNCHRONIZED MEMORY IS DEALLOCATED!
// It is not necessary to call this before disconnecting, as all synchronized states will be released then.
// Parameters:
// uniqueIdentifier: an integer (enum) corresponding to the same variable between clients and the server.  Start the indexing at 0
// secondaryUniqueIdentifier:  Optional and used when you have the same unique identifier and is intended for multiple instances of a class
// - that derives from NetworkObject.
// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
void RakPeer::DesynchronizeMemory(UniqueIDType uniqueIdentifier, ObjectID secondaryUniqueIdentifier)
{
automaticVariableSynchronizationMutex.Lock();
#ifdef _DEBUG
assert(uniqueIdentifier < automaticVariableSynchronizationList.size());
#endif
if (uniqueIdentifier >= automaticVariableSynchronizationList.size())
{
    automaticVariableSynchronizationMutex.Unlock();
    return;
}
#ifdef _DEBUG
 assert(automaticVariableSynchronizationList[uniqueIdentifier]!=0);
#endif
 if (automaticVariableSynchronizationList[uniqueIdentifier]==0)
 {
     automaticVariableSynchronizationMutex.Unlock();
     return;
 }
 
 // If we don't specify a secondary identifier, then the list jú<4zù_ÔºÑ±õ¤×©¥g:Åô«Iø‚ğg ;]•õöT«m=¿(ğã×wO´w ÿÿe;¥­ÖÅ9>xûƒ:«3šo¡¥—,”t¸gğbû‹‹ÿîÂ <ö‹K…@¢°  Y S!    ¯!
ÿÿÿÿüš„a¸`*B` `(	„‚b ‹ÜûfuãÏçãÅÎ}·®üõJºj¯¸jºY§_9÷¯¡ü^¹?ºï7=ßQ/Ññ^wîæøÊ$Ë‰vQó·Ÿ´Y…'£wè5§jKë]çî¾5·z6ú¨3jÏ­×ß8_Šr“óV‹MÑrKc"bš,Ä˜±U.N`õ€R ‡`À˜PJ	‚¡A(P$1	B& ¹R¼æõ*gg35Í•%qå2èMíÒÓÕÎÿÜÿfÍyú“ÒŸÏ§«ş“kıù1ÙÛ [Kf×}½/óZ*'zşeF(SüO€2áËŞ’İKgÿß¶;Îì·PÒã;æÈùM¤ˆß¦V…s×õ+rátİ,¡dœ¼©E3ÅT¶l¾Í&ôíûƒ®U÷ %ÂÀšR3Åà˜².  ^	 ü!    '     ó5"¿AÉ$ş}m]Øé–k‰&F€¿şiª¹%%„„ÌÖ€®öçD<t†ï‰½­K¨_D—M‚}¹kº¬Û,rÚâÜÜ§:¬{pŸğá¸tÒ¶u£ã VÃsqSZUŸëí:›kßY‚@yË¼2²D“’), Í.8,^lí•8T—Éù:K‹ ÑqWÊÆhÖ!k]¬&oßnõ?—˜ÅåìÖı¬M_Àx]bÕÑ‡ƒø‚ÿÕ™è]r|š³¸€Ú¬QÿÌ*_üÏ¢Ã$e"mT0}VÈ
ÔsUúVÔü“»>'İDØÿIGüÅ‹ct+¸æÄ«„"7yšXUÇ„ÊFª6î‚ ÑqY„çƒ2Î!
ó.†œvê…Ø§²W˜ƒ8®½-KlÆ Ü*‰Ïèß7İÇ½1{eÏÿùüÛœø…sftA¦Ã‘!œª´[íáMvá“)ÍLÛí³“5“;®ÊØ|ê	”ÊïÁmU'Tl¯öéşÆœÙ’1oïñÀ	L@ğœ4ÇKçûÕ\´jÛäd_ÿZÛÛ©2ÜôäÕ90Ÿ£œ,qµ~â3¤ê@WVyK×81¹‹Øê¼×ÊA,‰­aæÿ£ˆ*pè*XØçã0ØŞn~%ŞËÓõ§€íó„õ   N!+    ¯!
ïÿÿÿü›¡0`HDá ¨D½[ënºşv¾~7ç×µ÷çrê"éYr4»±)éÂN‰øÇR=ŸUıª—á€t+OtşZ`JŞãà·ÍŸƒıŒİ]rSáïèÈ5áNógÒAîÎäÜé•Áhúöe‘šqı½èÊ¤(¥­Hë¢öÒÄà½tXF%kA>2xRPJ)±Ä€°`,g	¡`¸P*a ‰L"5ç·®-—¹ª¿<÷ÖæUå“êTçUÀ÷~ÿnÿ·í>ìíu=Ÿìß‡öû¢É53úæ¯Ù\¾³RûÀŸ7¡ıü	ûĞ¼
ÁGëí}Íxq²³?ªéÙ×Ó"().öæ-ßş×dŞ¥»¥Ê˜§Ï¢û?FÙĞÛ|º©M;‘kĞ
€OÊÌ,D#´  Y	 	!>    '  ~  	Aš$úÑ0¦_Wçà½J¤¾h–{¡NÇ'r²Òı·c±CFˆ‡¶®]3ğ|(QÉ’:èÄ%J‘1Ã²ï Ó–=ú²gŒöÔ¶ŒöC_Şl™0H»Ğ%Í¬j—¿6¹æ¼¯%ké÷¹)%r AøŒ€â×äPõ ,Ò³Š'²~öìp
¯nf*Í×·şp‚Ó¶Çşjä(ËI_
]k’X¼ ø"«X;«¬Ú‘õÕ‚Ã{ÅşŞ¼³¢˜½úŸÃ7|pqá÷ÍË¯7–¡?ã:At-ĞQÕ“ù‡C‚¨ä3~RĞÿMÜmì)8ãÏ·œ0(Øéöˆ…Ğ}IˆMM„@õ*?àü•|É¨Hq–©X°nåsZQkª,ºÓˆÎVşuÿ™7Ø^¸hÓÒhï‡jÒkÂ‹üCÛ¥¦÷ÀÊƒÄ‘ÕNòŸ(êq¢ÆPÄd©G¤übú6İ“&âŞèPÇ -¡f®´,Kşx˜:Û EQfÊôSu
à*"Ï®õPÕEÈ¢½9`À‚ö¾C;tL‡X‹ı¿!L±X X§†cçuEW\3]{Ö_3./÷Ö•½µ˜Ø”Õ÷š~ÉeE¤»ª×lÿ·)8Î ıpòÆaîPDs'Lé!,/²îòuÖ“®~&ò-•Y í•º3dÍÿ¸æ8Áx´k^lÑ˜¾c=±µí”<Øí;?¨¯²ŒÏ—$’îì±œ!(	q£Ñ%oŸñ/B£Äûâ•CÒeAğwErŠË5¼bôši’!-ÛĞ¸pm tˆøT±ÒL‰m²$ñ.E\O±¿åT0Z¦ÖoşÂ2òç|©PÔ	°Lß××=‚‘›8›§´.6dæ–z·_à¡Ë	¢a1\GË}ŠÚv¾c
wËŸˆ•„•öİ‡ëÄ…‰Rÿÿ:­¼„ŞBíhüV#ĞNr÷Xt¯8{@-ÈÃ¹ÈÜÀjI§h…ÁY5ı: CJgSG3{'f ™«*ø[=¹Agı`C6ã„Î3¾•(`*àæ÷Aä¦öQ"„Í Qá;üêIHİ‡ª$åyDÀ~Gà
ü•ô -¿ÜÏYë5Ã7gwCµ]„$¤wŞH@ËgÆC|+†¡ËUvß/±‰Ç†ÈbÍØô3›C¯”D‰Q¸öÊ
7 %¾>P"öHt˜k¤áb\5©Á¥i|³ÅräµÛ$²_ÌgTWÌ	ãdıüWfÖáŞçÃ©¹ÂşÅªÊ`‘ÛO×1i*l·"íÃØğqåĞß³=Â‰åÛÜë…¾®eİmú÷®®!ù]ş~˜ÑĞnÍ?%ß42äéüÖk=ÿ™Ï*4¿Ov>ºÌkx;¸!ê#¯°À=lf0cKfwA~ñ`b<—Št9Ë$Yaê¬U-MBYÅ§ú\êğ[H\æê'ÂëƒL³U#ßPì){¨T¯È†bù/&52Ğ^š&Æ–{£1_ã\	5](dÛY¥xrPDA	%Ï“*<×„ó~¯< P  ÆXåÎ`¢>Ãò÷Ü|•ì‚d:Â_Wôíêà´	”>[ÁF¼³HõÔ Ã_?¥ÚÊı«[å‰ºÀ-q|õW¿…âpW~½Â÷]àuÍƒ	D_ÒÁª™º‚oèPûmg¾ƒĞnÌy£óF‰1 ªz±îÁŸ³ÇEš¹‚ ¶ı}}ˆ„'u¤	IyYz BîM©BJ‰9%LŞÚ9ÔŞ‚SJÒ‰qÉö‡bÑ¦dCÊü<L¼ş`'CT¸J)i¢¸[¤gì>î—\z3š(ÂÙD†ÁËµŸÀº*Ñûa¢”x«ÂdÇI4ÍDvo*?V`(ÄNCË6è,…Å9ˆ¤?ÏÑú_ğpÙTªÂˆ!EBMâxµŸ”Œí®ì¨FjÁxØ@ãÔ¨y+;^ÛÓ4_ÛH+ÑßYgÒ="cœÖ¶pş$ï^¸µ“²|II_¡ À“HK7GˆùÒêÉü‹o§Kè¶@…!º ip }Ş¶‡Ö..êå
$‹|õ@ğH\¸ î}ßë_´Ã9FZ‚t
¸n©“K0#6&w,}’º©ç°Ô„Œ¹ìC©ådµUÌ÷KğÚ$9/É„Ğ·@ò´Ÿ•;é05¼dç¯ÊS£ÏÏ¸ûCıÀQcSwñÃ=o8	«‚¿ç'úUãX<˜ØúAãŞé}'n<µÙI'dŸØÆP(V·„CõáúÏíòÚ8;l7Ô‡ºıMÇ…m
_£ä9ÒÊ0%Ì²úï‡œª.¾KúŠ‹ÁÔeÆkİoz>ØénÓ‘uUe†GÉ¾'¦¿ÿ<™SÀ;£ÎËĞcZÛLñF`ñ[ø³_¿N ."r.GÜñ1 ã5f˜ëèû”şR5ö¨ ¤ÊfÊ¢mÅ‹pj‡éÆ Ï1p@Û!²nïíjÃ'bZ±­'×:dÖÙ%ûìñ[±Á2hŸ§ñ'…Óq©|?†H‹Ãrk>§ÑéÙ·ñ«g°rîğóá}ÆV¿”Û=mmÕÖ ë HÌÔá)•…2-AÏek¨ë…3Eş †nTk×ùJsd‰Ô˜‚×TÃ0{5U)eÚYğÛ>õq«C V–ıWøÇ\æ–MŞåG´Â÷ú­o†ŞñµÆñëïDé?>7²`½ÎK™Èé»ç=‹Wö"³  ¼µr:n­©ø.ğ„óLVóåY< µVº.Ô‹eïîaÊºF³F¬?sç†‹ìî× €7ÁÏO„ÎS¢§®!”å˜¸5Éˆ‚ac[g’ÂƒÕµı
 ˜óM¶kux’kr>÷½˜°)MJ¤¸E(Œ¨ÌZĞı§åcjjSÈ›Ò|„å0·:$ò¨ø¦×H3fß´•¯2é‘ë²ë¼¼¿İNî”´ÿçZ¦T²ÛIÒÃ…ò{r|†¦ğ÷©şÖŠÅª4–¶´—ğs!ÉlOv
Åı²Øóå®¼’è)Æ$yæò×ÏAáÂ‰‚öA  	  S!@    ¯!
ÿÿÿÿüÃ	Á@¨`,	!@°T2
BA@D$røİë}~ŞÜÍwíÎ»úW[ã$Ş¨›]¯Ø_×«éÿÆĞß¤›åÇŒxô0?A`ş]x~âw¶qG­»ø#‡ú{§¥íİÔÎä³ÙÒ«¢2ùÆ¿RãhÆ2º—œs'¹K»BUYv¡BüSKb?”Ñé‚ğY$Q
Ø¸ÅA0ŒH…
C0‰Ùuu8ñ¤ªÕí­oÛšÂ*W]åK	vŞCW:ßóëû/vÊŸx4wh®Ÿkä¶~»eÙŸşA?ÕºğßÆnÎ©S™üò/üª\óÿ ^}o šı)µ÷€%§B7ÅY·¦È6ïœyªÚà×ú{óÑSAìÅDã-¤¿ŸÌõHcµw¶o½±Ò?öø‚ÒˆN5&‰j& $P-€  ^ h!U    ¯!
¿ÿÿÿü¢…Á@°PP&‚Á ¨XP„Â¡!‰H"‚ê¯_Ç¶ê÷íÎ»ûÕyåt*—Qs\ÓúŸAúİú?ûüp®ãÖê¿ìTF¢p¸tgMÈ¥Å?BßWĞy£¼½ĞÀ½Â
ø’½"?
¯Â‹k´[Èßu¥NÔ†ï¦-$U¯ÛŠ>´È üóÊ.½ïÚµ1¢0¦–ÂÈäºWª5¶pÁ[ğL	‰D4À%0‹° ,HÁA(ĞJ)Ba˜D@İs$ªëiÅ÷|n|=oc%_Mê	Yº\O×ÿÿ5ç±òìôK«Í`PƒUHû°İáÂI9N‹öˆtÖ¿=>‘€áÏ@ğÀ“³åôŞáŠ» 45µh f¾]a ?)œg«u…«S¼ª®Ş˜»Ãë_ô¦-µĞÆ<”S/Ã•¹2W>¤‰ñdbüæ|z $@Oãà	ÄV8  s	 ÷!h    '     î7"¿a²9ş‹¨œ¶ü4Ó·
ËÉyGşÉLÂ+Ú·4ßîºØoùËØÀ/*ln©*•Ÿ~ƒä¢©àÔy!ãõ)8·çLP¥z¿Feà/‘X½Y‡&2OVøšmŒY¬"ˆC-Z›md0.÷~s;3<öShÕ&‘GçëØÑ‰ëÎ†8E‹A?ÂÂ²*\:g¡?rvïvÄ$3¥l¶+;¸óÕ÷áUÂ»)`Õôî(ü!¾Ï¾´BéRÊV˜ğ="Ìbbœ¬(Ù…Ë¯GÓ‰J)]ı`¾láK¥Ñw4=^õiU*öØĞË¢ˆÊLû+[V™°™¨R®!õ©(…¬³(ixùlqŠaD/Ì¦dÏÎôDeL@ö~Á ®¥êeÌr@ã*DÒÅéw7P01]/\¶cŞ‹f6…§ uéÏÉË¨¬± Of†–µ‚D™ûu³çj€÷dÊtÿ<½/¡¦ı»»åSm‰^Üæ1]îÀ’{"u—XÙPîù$„öåËûøø<3)§Í/¨H'ôWå-N\«Wy Râ°#ˆ=‹”Á§“úH*#ãtÙÌXJÕš/­KTì2¥ëoË9öÏP'Zjg2¢ôÛ{I]nìP:^€   p!k    ¯!
Ÿÿÿÿü›ÅHX.…¡@P$5	VÉ/o?n*¦qZïá¾…J¤‹úwwqò7Ì~3ñoª]»§ŞxiæZŒÕ‡£ ±ı’$û’×UÛ¸Q~óõH—÷L«ôá?ĞÚŸæÜÍ·Å÷µBõ•?lKs?&–£Vâ•x¤ÏĞ€µ”ÊXÖğ¥iá¾h™|[+á[ã–'|s*-IeŸÈ^+¬PYfy¬®p6‡c¨Ü,$B„Ä!Pˆ€*ãŸ;«ººe¦j÷õó(*óW}wĞQÜËîtõß_—»»·&´<½ü·Í×¢¤'Îş¾:¤{‡Ç°ı·…€º0=Õ7{°¨/éÿJx¹vûKîï€“™½O @Hì{_©ëáRx?}4«~ƒoœ?–ıÎ  V?p}Wz.]ô{M-¾I·!f¦o^ÎôŸÕuõŒã-¬ßËEÕÿÓ‚vëä %É'  { h!€    ¯!
ÿÿÿÿü³Â@° .…BÂ ”$%
†+0¬¯>'>Ş¿'>Ó¿5ªªÕ	‘iğ7g&Ş“ü§âZ=k÷^î‹ÅŞÿµèÁvâ~¤Ï÷œÆ›ÄİçâØ7÷ã~O…ËíÚÆÕ«NŸœsS¥Û-æÕ<y™aè£#8P;æ¶”>É_Rğ-n{”RÂ‘\›XÂ“ É¥0wŠBR  Æ“`ÀXJB„0 HJ„Â#0ˆ‰(ºK¬»ëÄoX—~.¸ªã}H?ÿıÎÖ¿Ş×ÇºëÙ~İòíÕıÙÛ:!*%œ­™ËÉ¬û2yı;ÔÛúû­Ÿ—P]ÑÏèøë–ıõx"yŸWŸ¡ºj	QiOÊ×ã–‚çf]µfÈ?'‘¾Şú(®*ëã˜<×ª!z=	\xğ—_ñxs’¯–lÓğ ˆ¹UAÀ  s	 à!’    '     ×·"¿ÃÎ°<é~ÌMy¿º­å‡üAó°ÿŞ"	ü_ô²è­Ä§YTG*ÛŞÖ(õÙÈoE NNòYCwE4ÉôFNÙ8¤á~@R%˜ŞŸoU
Adfe KÓlÁvKÅ|ºZK§POO¢!×{¯›²>fg‹óˆ«ìZv‡¬W‚çÙ§¶ïDÁeêã<FOoUPSì`U-o0ÇlG)gÔ7x­ÓGDŒ6Å`O
zHmÏVÑÍ!Ì‰=ó§”œ}CÛT±cp_êf©£Ç®lpäo'¹ãjÌ·&9;²ho‘ôr—SØ‰ó{›ímíNÍ"r—5óP.>Ì"H«Vµ!ªß~ôü.ª‹^EO™µI}ĞÃÏˆÜ\¨—^g5nÆ…v
ò³^Û&?ÇÊ¢mb=&{ë
÷ì­Ö@WˆE7’§Õ’BÚ>PR|yÍEs‡úkÇ;´f¤¹¢®:îi³ñŸŒ= ‘h­k¤„Ğc™ VÛ<ö «‰Â¨»±ƒ½Şiß{3¯óÏËñÂãĞ°İHÙ€c©«°şoO`¬F†"ÍX)–ó™ÈnîÕ&ä'a0œõSÂì~#N5¸È÷&ñ4òÃ‚  ë g!•    ¯!
ÿÿÿÿü›Á@±0…ÁP¸PN„„!!
ÜêUgßó×i¿j¾ü«I(µ\¡§hêŸ¡êBîøÏ³³çÀ´y>åM—à]î9±ÿzeÒ•îäuÔ:ŠŞ#:µ¸ìEy¶ïas&`Ö³Øa!2tÑ%@Ó¢ Wğ8NÛÂmS€B³Ê°ÒS ²æÜ@|M@°,Å{D®p&DŠ¡aPJ$
„Ä‚QT&„D®7¬F·2óZŞ¦ŞÕŞªbI—+‹Ğákmµı|ş[µmëîú~°›oK°n\ÉxWÙ«Â6lõ–Ï6Š¾4qsÏ·¾ÖÛ8¥ş?½×:C–}cà ><{ .µôĞW.Ô²CÛ_oøØæv»â£7ıßÜ!<<Nã(ù>\ËŒåzÓUÒz×5¬^øŸÁ/:Å@_kş‰<+'¾Æ	ZŸÊÂÿ& #jÉà  r c!«    ¯!
ÿÿÿÿü±…‚¡@°P.ƒÀh*
Âa@¨PD1qw¹__×ÎÌøËñ÷Î}·iV©(\Gæ÷›ïá¹‡í›¯Tk±şˆßŸÃH? ëà\_½Ùí»Õ÷£°ı6•OïXw}Ñ%å‘b;[ÙÉmnÃ ø¼†6ƒPháŸæÇ]rx¹Óy&$0“ZEÑöDV*!„(¬¶@‰2 l4£BPB„H¥ÍŞíy&õ
óÍÅe¤Î8æjK~Î«óğË}½¯üîõ÷y¬íıI›x8	Ã{?D5®µêÕÊç·~ZK[$/°ûˆŸù}Ÿß~{ñm*K¿Eñ­[ôÊşZ_«€z†öwytÙ²ò¹û^¨ï‘ağü)Ÿ|8?†Ó÷:&
ò°_ö¾Ó^úlù×Ò·ÛwŸÚc¬ ‹ışX0…Á£ássz¨föÄ Œ¤¹‚E à  n	 !¼    '  }  Aš¥úÖL)ÿ_kÙğƒìÒˆÑT²ÌÖƒêá*hÛKÂ‚²«˜µšˆ‘%‘%Ö‹uM)EÏäTÕï`Wo%í¥Cï3ÏEá¡&Ä“Ãé]œ°q#™²§¬d½IF*ßØD7)U¼ÅÌ%Èç¨”åöÊùŞØ%xQ¥/è)'l^AíĞ­f LZ}¿ŠŠlb•L/Ù\¨8Øê–!š»…ór)'2Á©—«B¢9bIİ?ÎN¡/üªzõ.u1œãZJ·ÒU’†¡÷¸İš°	Xnî9»İH¿3…+jD­Hd¼äÌÎ’Ÿxõñ8‘‹!àœù.sœ4¥ŠTûØNej‹Fıoáá§o~&ÑÔ¦Ú‚Ï	³wÈõ!ÀRƒVÔÊ[¥ËaIY8î»H/šCÀ‘İRØ,mĞÁÈL~%Œ'gë‚şË’òƒ qòrZI“À¶­’öWCçéÜæ8h®¼¿(‡é±V±Næ oİÆ{6ĞY(|({°RÌ;nœÊê’wÁÓ‘]:¨g"V¾Îœ5äUïH¿Ë¿ë71ãUÆª¯._¶°ò£¢ä0Ï ›€ˆFM218‹õ–¡÷YÚ¢6æR³½¾øØ> U=ePŒÃ/Jÿëœ	9;!¬\»lö¢#İƒyCDòGÄÊğuO]&.‰7uĞ‚Lñƒll//Uœ(ƒï˜$cdğ©°ñ‰ÂĞÆ]bœ‰7”ée•–»+ÓlÈˆsj¿<pZ|'¯éÔ­ÙÊàˆ'g¹üùÌH?^¼l7½XÖ”dò›“ú×Ø›0?œŸ–´Â,‚Cx‚Fka<v£HÕ‘ó¦T5´ìqÆÍ…h|´gÕQŸœÓ—’Kİv‘Õ¡<ÇH“ŞNµåƒwEà0³.ëÀÔWå½¦*ïÌÀ
öê†±âèÜô ÷hÁĞwê¾QBÛßéØ˜ºüx˜Åôê—ÚPéÉuI´òÊA/”Õ4/_õ¡øS«-fõá^zã[7È°·ä»3²˜Ö¤ƒÇF‰²Ë¿B0N³/N×›ı5;†6C wãÖˆøÕÏSˆaÊH>¶ÿaE…ğ½>Ö¦‚!twÍ›Ç “¬ü‘ıÈO…»ß"ï@Şê[c9/07•]¡V&¹¤=·¹‚n½—¡ÎÒQYª‹ñŞù«’ròF±zÂøÇªç›BDş_…ŸÅÚr0aÏ¨ò`b-ÃúP
1x~²‚R®š²<—¦6GRë~Ğb±ÇáïÚ“×à~OÛØœİÿ	
”Ôo}ëû»Ğğ‹—¡hø£Å1÷v İæ½C«l) (˜HDhÌ• a¿µi}ƒÜKBœNDE_©ŞÌµdd†©?=•ºy¬97‡µà^/ğûxšOşÔoâ…Óa6Ñùj˜ùÓ¡2Ñ ‹ø6ÇV2·èd>5ä÷˜¿ŒşñÛÔ ıÿ»*Öè«ô/Ìõ©HQEá»„Ûlh)Eh3IpçlÍÊm/¼¥/P¥û!ó­¡•³Ìb±ªp,Ø²@DÉ1Âáx9 Øó(v×
<OÁ/æ­‹o¥‘‹‰+¸biU¶:ÚG§(Óä^GÆzôAk†{«€Ì±0®adj@Ë×Väôaÿ3Nš¼@1ıÌŸš‚År#ác«ãÑîÂôÁ¦ê1‡vbÕÀOì;VÓÏ‘ñ	„%¼)>öşàê!µ4‹3à/;{9 wÃ\¾ØY¿·HÌˆÉ$Gui(ñ:µ¿ˆæ¿Ïh·Q£ÓŞcHÑ…ö•PıjtáæÑ0H;OÈdˆÈ!'«o`†Å¶-ğ*EdS­aô«º·Ğˆ8Ìîyµ7êÔï)ˆ_¶Òüg×EœÿÿQ–¶:'u¯7Ê¾„š…G%FB›éQ gÿf_ÅÎ§èB|+:íôË“ v÷fq¶†\ÛÚÀû$_o›ÛÌCõ{ƒÑòÿÖ
¥a÷l3­Äsë}Ï±¬Po~çÇ¡Ã—ô‚g6!O »@Ù¶£îhCpÍRA§”ô¸Ù{m/’aûâ0‹	qöÍŸ¸k¹d%k	ßïÕn@)@‡]®Æ'%»˜GĞãº1w1É¦‹v¾–Ip, <İÚGqŞmU²÷WTq†îMÜIçªJ¼ûâ¸øµıÿ´=À‚Ÿı¹/ÔAËm‰–~îMÉ5¼À}+ÖGÊÙ¬æ°•0„Á°*°‹R4.%»×y1h½Î;W0ºßßúBâ…uŸéĞdU{Ÿ)µÄŸNÄ|^™¨ˆ‚tŒÕ¡¤Êî•‡†L~CZe›îø®ÚU Kkµ”^2zWfmÍŸ)L‚zÆe•\aoıQdŸüß¢Ìoóû;İjKÜn•¯[íLw°É`ÇâÁ›öMfNBÁ´Mµ¨íü7ŒtHº:QG†ØAÓ`ù”ÊyF¹
æØ‹¼r‡©àa	FƒW"."ÎnÇ¶êïåˆuAAGã‚ş¬SÎZh%#)—ÃÕbfƒKºRk…î)«lî…C <8‹ÙTœ<wöölcŒ¸Î™*kœ¹šà¬óå[XdÂi·–Œ•ùï¦¡­a¼xÚ¹¤Ï)ŸúÇwİÊc¡ÚÏS_ªÊsõé¬©ºxœ¬“T½ï2u¯Ñ`|}ŒlZF
Ê¥Œõí%}ø}”™å…ËÏg{+¾úšƒöÄit†©œÑıÄe°ËÁK  ' q!À    ¯!
ÿÿÿÿü«Á@°T,8…ƒ!P°T.
‰A@D$Z¯\ş?O×úuµïã›ß”Öåß6©&äµ}Ç8úwÖWôRú}.Zª=Å×Ğ¦ÿö©ì–eù6™ÒøwwøÍúÇ”|m¼s_XüÕ2åDjI¸Šæ¥sA«!Îã=JÕš§ÊH„GC•BjP­»#¸œI¯V²YBq«Šˆ@½æÀ¤Â.Á@À˜0&BÂ¡` TH%
	D!0ˆL" 
òóŒÅÊº’¥Ô•r·"šÕ+¨4š*?†Ù|?ı¸èÏ›¸ºØ±ˆĞ[òá%¾Üä~6úê±{-¨ö*Íœm’~{¸òiŞe|\‘ÛR3ªµíæ½JÿÌU‘Ÿbë vrèWïè~é á[Í9¢ø.ÌéÅr> m™Ø–Îœ1@î¸¹pÖ6çã%Æ¶ı3€—#¿ğŒyôÏ?Ñ‰…DQà  | k!Õ    ¯!
ÿÿÿÿü³Á@°P0á X(
…¡ ¨H*zKßãô¾úæqãÚ¼ı¾õœf£%äŠ™u¼‹ñş¿Ô?ş4&¦ë=áVæHòú±guÉıQ}àiÒ#‡˜wÕÁfŸæ]¦ªø;úSYœ32“º¾±&ñ7ÑæÔR«Míœµ)+Cš¬¥MVf@SÀBÊ‚‚U¨H‘@š*@`Á…†‚0 L(BBb˜Dhk•Ô“#Xã~wšËªU§Záb?/•S¿ì}ŒİŸj-‰İ]¿íÿ>^[z¨w–½¿àİg^hsøgx~M}ù|ª+ÀZÎå~›ë_^ù?ÔOõCü¯­ÿÀßŸ‰ëûÒ{?ûÖëá=0M¿à’=aXŠ «LëÓİ%è»Ó´WÈö)œººmtÅõÕñ{^¿ v¿¢’ÚUïöåjÒx€§ÂÑ€8  v	 !å    '     ÿ·"¿ÃÎ°<ï4t]´Vaxvç.®ÕQÇw×úmÀM[<([>÷“ÃåÍËO=úøh•*.ÿK?ı€'¡ŒZp3lêä|€¬@{í‘'ŠØ,Ø}şŒˆ´œ ÙÜ3H¨@|‚ñb»‡>¯+?w4•²ÿ´†öI·Ê>"Q~•nÓÓQÃ±°ÔrÅ_­3õ
yNÆÏ]ÀÅ½ñïÇñÂKkRÕ¥¦ş¦så`o„c€?bÕÛtMãiK©×Åçä)°ñ~8}W½ÆõŒ‰=C´GºxZÑÉ	ÇeÓfÃ1mo ×Cçôˆ‹àúïÇéõCÿ8øÛÉQll)FYP²|§›"ÃqYÍ‹›Cà9" «ËQwàÖ‰…hÑyƒ¹ä5k‰r«:•A&yàf{h‚µ°ÅØ-² û˜Ş‘YigÌ‘_v0R×SmáûÓ×¹¾úv0¦Tê#Œ,{å€Dä¯œ÷”À®C ¾`*?şsº@tªX¢©/{2ª˜ŒÒ•ÔıÑĞ5eËkD5•u˜ôÁ¹õø‰¶N£€7EñËë *«sõÁëz— Ï,w¶Ü¶ó;‡ëH¥æÀ]<Y^¯¡Ÿ”Èø˜\‰í>ñÈÁ+ÛUÆŸ¼¸íLĞÓmªNtø~+0Æ%;sK1÷nö¾,v…áğ   ]!ë    ¯!
÷ÿÿÿü‹Ã0 Xt‚á` h(#	A@EÎjü÷_Û®æ·ªëÇÕ÷¤¥Ç2+"Oó ~–Y¿Mß ÿ»>ï.­µu5áËñ÷¦,ı§ÀıÜ£ãî£ÑÀÌmPsPsĞ¬¨kİ×ş²y÷å2ävFòÌfwWº1½[7×](¾U_d-æFmÇåà %-	éˆ’¹$n†j€µ.€-´´@ŠaÀ˜0&B„¢C(PD	„NË¬}úç­ë'ÇŠÔ¬Ô¢/\¼ÛCşÿÜôù'wøX¿£…D}}ºïêÛW¡¹à÷ñºy<,òÏ,¼B'ï¾}½­X†'wáíà<oN¶€ø«‡‰öò«l?Ü¶7„Ç*çˆb¯¬KNÉ»µB»™ä:*U{U_¶´¾lO2ÌOœ(şÎô[ê”|ó÷ "ë6±oÌº“KöL*J0p  h O!     ¯!
¿ÿÿÿüœ	„ƒ`ÀX0&Á@ÀP¦"µ•æºõÇ¼•­ûo¯_yŞ³DJ—¹7:gèl0Ûì-»ı{Â®HôôëèÜU‚ûôĞoûÑàm|[KÊ›C¼¬w"QX6îªD?IVy\ÎÈpê¯óW­ÉõCŠ(R6­£ª.ÇyìpÒxÂÙ+l§"‘TªPX¦äX
‚r¥`MÏò
Pá
”ÒÆƒc¡X(•Ä'I¯~«®úİj¥[Zä™$Âë¬Iv:üø±÷k8~>~ÿQú5>©«ü'…o&ˆüßÿ½×LñNïêÛïà»ÕJø	ÿê¢FÿÅñ¬¥¸î‰]àŸ*`9û/öS\	.•E»hLÖ}67ìè+:±…Åuq•o>ÄØz€x JóÏû|é{«-÷/(Çü&»ÛÅâÓÀÕ¸  Z	 Š!    '     7"¿–œy¤!ò¶Tö3Jo©Î‹ÌnNP-•­ä—¦mÜ ¡Cs•åQË>îŠWÃ5€nh³±áµRŠğçM²ÀŸz½>ó.(LƒÒb;APkM1ÖP¦¡*§'*ù 3Êçr™Læõ¯lO(<›AV­ŸçM!Cè"Ï"‹„Û%}A\'¹Ob ·õG.©Øpoïª_K‰Ê`.1p<Öf~ÙÔŠä˜b{1BİÛ13ü7IŠªø7[ùíN‡)j¡1¶Á&d¤+¹*/³YyüÃ’ŸUÔîyH|Æ™ú|Mg4zü—¼^O_o$Ó?Tí)ãyÏ@Ûº{w ¾ØSsŒv¸Äà\®kFğáÎšÂœ2@9c‹ƒÏimlÑ+¸Òh4ÈÑ°¶B8”§Ï;ÃÉ¤mëıníj†Z-ğ¾—«—J@ş¶qñ…¾'¡&Æu ePU5å!ce™É>ÉVåPÉÀ¢ßÜŠ€  • o!    ¯!
ÿÿûÿü›
Â@° T€°`(b0¨«œxøüêUïŒöõñYª’òª\ËÄO#³=İ]0g³¿_Ñoô¿ÓI;V	™ò!†·ì‚ÌC†§µ­wÂ¼ıf’ñO×²uòü*’MSõ¦Ö>]ÿÙ×ßP°Ù‚¹v"¼Ì—÷,öššIà±&È7¬€êK'(ühB°‰¦Åğ²¬×œ»-6JÜR²›˜ÅuĞ- "0V2†`¡T,…a@D&*²÷ªŠã8çTš¤“Æ‚TÖL×´¾İq^óÚO‡ìµŞKïèËGšºªİ¡$êÍöï‡ëÃø•;ûÓ“ká°ºü'(WÌ5rM:×äùÎ^Óã`¯vóÍi°L0ßÂrô?Ã×í2Ìvšèeç¤Eo¯9âí‚§”Q—¥š;Ä²=˜‡³ÛÎéü	$)…L`W›ó1%üŒŒ\wÿ=Á…ş2¥â  z q!+    ¯!*ÿÿÿÿüƒ
ÅĞX0&£@¨PDQK7Õyõ}Â×œwõ‹Ş«[¨©y¦±ì:Ç}Ü(wöuÇ«-šª4r´wj@^T³k·¬:ğŒñÕû¯5ÃîÂÕ|¹¥ôÕxò÷kF¢dÏ˜G,¤±iÏ_UkìIÚ«êßò¡ZL<¹˜,ª ¤*oÔJ}`˜d©;Ób£ã¬Ã˜¨²x¡^Åq„c˜SŞ±ÛóH
¤Hç >àA°`ŒDƒ` TD
‚‚P˜DF!æ¦’L•ÇuÌë¿m{ÕJ…\úÍ¦´>ÿÆÆÇIäçh5µÖz¸wúR­Ò©Ë´ÛÍt´>¯Ñ:{F5wõ¯í_mòp@Öƒ·ß×iŸÃ~<„=èYŸWG[ÿº…sÊrÊ¾ş¢èQ.Æ·'Ö6î ?ä¼¹>{y¶¹Æ‰×[À#@^ ³¿¾«Ú ˜v9Q½÷Ç—hÀÎ€ş!PøÖÓ/è/òÄ
N à  |	 „!9    '  }  {Aš%úÖL)ÿ.O0ø	îw{5!³mûŠø.>ĞÄnÂè-µvò<æ)dò˜ Mêâ“TáëL’K~Õš–ğ¸ˆÉÆ İLNHe˜æfëım<ÔCÚyW‰4fhi¢>Q>ºÉwÊe¢Şãœ²c+Z•¥&)¯Ù{µØWlWr§¢»²ÒÅ=y¸Èpm$Xè’~ Bõ×õ`®~½H1Öp'EÈVMÒşX 0@;ÙSô°›–v€9äˆŞ@£R!É³4òøôTòJÄ¾Cx¹D¶m]0˜9%0áÜÃ;vAO;ğŠ»©d¥I±³5xcû^å´ôÂèmı1äLÑÑb_pJGÒŸX­=ÄZ*6À`Û3í4âCÍLªÛ¬rPL$©NRÀÖ€ŒÑïL©ÃJÌ¸­ì¤§@-°…ĞºÎd–ğpz¬µWÛ?Ó:É$6†ô†˜Ÿg&	—2ÓEô/ch±d«˜w»CuH*‚Ò,K:_o<°Fv¯ÒıCc9³7ã‚]ŞŞŸşká¤¬˜˜tÿ™I>¹¤Î‘+*‹xH(Õ€À…¾»m¥’Œ…¼æjn`’(¯óR™¹ÜH4²—)Ü¦í‘Ï`‘B:}4Mû9ÖüIçğmByÅˆF’ÊæIÓ Í
1î©õ}"Ê6Y„¨¨×áu$7i=Õ¹Èà?¢¯ihÂ%ÙH48Ïã'`Îõ–[ÉŸ|ê„Ö]şIdh'zA#±Â‹½@ñL]’¬P{«Ïã“ML¿Ç´Óş¡PU…âü–7p«Ó¾*ïÁENqõ‡Rì}P:âş5.GÿTı’L½C“.c%©‡Öî‘ü!_e+ZU µ>5HÚb¹ÀBÇqÿ†Q»JsbœŸ9¬Ü¨*šhúè¨lb>pì$ùÙ|½ä¹v9Û„ï7"»±Ÿ¶-Odõş	Xêh‡Cƒ§‰ìyÙ«Áá&?›¶gnŠ×¾Ü‡ÔFuí?ÄV
èğóRóè.ÑJ‹ÖP™lıÂ­†ØòLaç©ì®Fˆ Å­_Õ¦.š›®†Ñ¿mgÇ7Ú%…ä{Ù&#°@÷§”‚Èû•?,UtGê-ŒGİ¼{K—¯OÛl)Qdº7Üj]+à•Æ»5ˆŞ‘ás‡%Q ä+F²Õ+BGd2:+ù7¨!¸/õjôJß	j”Kó« ­µµe¸Í© _W¦Eã.riq'èo°æ×ÀœĞrwm]Q½8åÌğı–§Å&n¸¡kñĞÇÓĞº°Cİ¬v4|Ğı¶ğTpLÕ›Ó
ä=,zAıi=àÕòˆíQä×í}˜Å±à³¢d í7G«›éS?øxWŸ¢YkKg!Yk9-„"¬fÊJh`N„;üy5¸'÷!Õ9å+ÒCş(ÂkoıScfpæÍ_ÓDVúCè- ÊlÄS'”vì
ƒøØ¾²TïûÍËµß§]6¡ĞÉ,¾´—ë:‘ûdº­“PM6áb’İ&ÄŸ ®|¶¯JŸÈüÄ„ÓV¦\˜,2­FÊŒ·*²ó‘\ÎÂ=¼LŸóÖ„ÍƒTpwêï‡!İå¥ÎÆŸ.¥v,¨Y¨;±COO™k„øU¬¦CÎ?•8  *Tş%Pû( £
XâU¾t¾:•ˆ2(×cI½oàØ3ŠæÌ
ÅÆxËÛ°ÂÖ§iÀ¶ê©?ªæÔ‘—"Z7LmQQ”Gu¦=šö,1 ˜ßö«€´|¾V·2’û¸Í´óQ–1@ØÌùY…>úL¬Ã‰ŠJi²ßîÅ¸{ÏİÎ 	X}^´Õ+üÊd­–«-0{ËÚ=rùÿE]ş¹Nj„ÙƒéÄ±b|Bö#‡†*ÇğUgÅªûE>†Úoq;;¥÷^I€ôĞ@¨+/ yù?¦é²İ'õOÂ«@Ø¿ùOHbÎFÈÍ†Â Ìˆ£ØãØK76¦/,´]à	·œ§$ˆÁ¾Pù®¢Ô˜å–ªÁ¯e¤‰/x!Û»È˜š´'àf #À­¬<`¢Ó_j‡(¶A¸ -+fX¿æV'}ÛQ[šV_ÏşËƒB¼ë+SHO%‹´öQ±ÉeÑ4È·Ö‡÷/ŸÔãÑYw”ã–:¡K¬||”i}f ¨bOÂz#ŠÓDOhÿwXı3ËNëÙŸº:~‹“98.¼]©ß„ )Ó¦ªºUÉ›v1u€Ã%_Å}÷{•Îı]˜ú’ŞºŞP-çÈšƒû(ùæmHth#ÈMBÔ×ºØ2aº§£S2.MM\?>— òo¹Ö¸+XÄv‘_pv(ÔÕ«NÈµ{‹%¸0ïÀ#şìÛF sÃL¹=TÔwÈQ0D%ı{»Hø•T3Ÿ`‡ÕƒNo[¡,q¬™)|Øúï ¤(†{n úÔ$£N§õÜµkÑñÊGM°ßP–
Øuœ»°İ
²WX¦ l•*Ÿëü·š)™e¬=‘fİ^ÀšÄ¿áë@®¹£Í3‰bºALtã—ò ?\oÂ|=†ÈÙ=®°º×ÀìºÆı+İ8“Áşœ‡a)ÔÊ¸ç$ãŸRÖfÉÎåhüú©/;Ö,¾z­5ÒÒ=2fšÅ2­ÂçÌìGuFö=otA_oîá'%Ñû?‹·£¯TëcŞ"3ß§~iŠ€Œxîo¿àÚƒÉt—}•YW5T¸míX÷†¬¿2û"í¹ÄfÈŒeN±ÖŞ/ÄÙV¹7>¶a© Ü¥İÏefcO‡BÙFP§¾;5ıCOÍ³å&ı-Õ±&M   …!@    ¯!Lşÿü](LÑ
2ËÂGÀ0ñÉ_²;H¥®^—!m“®¾cv}{ôz=—â¹Á3«¦_µ;<yÅöÕù]³|÷(vŠğÇ@õ€å‹Êw­”#ˆ<àô99¨…õ)ÊùiÀlê¤³&¡ê¡è!¥¸	PJÔ–˜ç”¨gçoàe‚á&7*İ„]pÕ/.(Ù¢™ì‰é>J‘ğÕ6m0|ı®O’ŞTĞ¦#Kå_]œ'Kş(wÚ«TGt@w1@(,T´2	¤ëi]ßD’axîİÔh£Ã×ìS3³Ğ=‚IÃt€ä÷!/éeš`¯Á¡ÍÚ4ZµÏìà<É"ÿàøû>KêŞ=/Ú4ò¯µÙ|»ë|1—&»v«ßM2Û3Å\%¢I$ÛsªôÇšŒ$¨7µ Ä:fÓ!û,/…HƒBTŠEŸpWfÓ±±v6ëĞ@>`ÈœY®5ŠÊ/‰’xkB PÓøÜ1}ÑÿöPp   h!U    ¯!jÿÿÿßü³Â@Àè0ƒ` ”(2±×fë^3GS½oãsWR/kËŸßGªŸûŸÔ9=»>{©MQñİ{¤±õÈ%ñ^¿ÒAË:Ûş~ À`—‚ºh'ŞÕUr/Òâ?¬­dNéên/†‚C“â¾©=œ‹öd2ÙSÎiçµd˜CÁ€µîf¤a’„çà)8’Vê2"…â#jÖäouÃuá™ÈX± †aAXŠ	ˆŠ!(D$ »ÚÕ¬JuXöÊ¤ÍUR'UN ûIäş:èõ'‘ş÷uº°şÓßóãÛú_ÿT}Éü7Õ,İ½™Ç@K
z†šı¾¹*ü;ÈàQûçÃí×”w~¥Ô:µœ ³ø£ĞúHúŒä&cLÔ’ƒ<\;:ÿ‘i$«9ŞÔ´?¢S¬/í¢7M‹NsPÄÃÇlŸs&ø|+œ9@y±£ô¦%´7°¥:›,H|  s	 µ!b    '     ¬7"¿r4tø´SÈàDXN%öC
ˆŒz&PÈfg•-æ¶d‡ÄÉÙ÷ˆ‘à¡,5³Ñºğj(
¤{ÁÑO$kO ÷ö¹ˆPîÇW¬—º3¹ê¿	óé[ğsi­7·:	‡€³„ '¹ çP	HúB®©qú­± yÂ
4.¿‡-
§R¼ÏËñıŠ2Ø¢¤SÆÛ9"6@¡æçãMëüñ3U‚× ¡eå.*s£6¼xé<®úê¤ƒ"-“r@Iïø ı·4_ÂÓ.:¬lÓùc,»‰Q(§9û¨Y|ã.d×P¶ÂqÎFhÆ¤ÏrÃ‹'‰§-UM>ûĞT÷^Q#ûO`îĞ‚í~R#ICL°ÍòØÈœ)\…PGw‘Í!Ò+¶¤ï³×Ï8J%©-1t¢¥Ï•&%Òñ ínYåc´T6ş.cE*…¬æ!ĞV[VâI¢fw„J^ZóÕ›e­f	qæùà†¸ÿúÁèYßÂ^M÷åBªı'¯­uptâî$4±Ò9\µAÇè‰Ş0  À K!k    ¯!
ßÿÿÿü›Ä Àd0B  HbÖyœÍÌïƒŠŞÓ3X¬…k<‡û|AıXF½÷ïdË=qºíç?ÈÉ´Ú×~‚¿»¹äÑÔ‰o¬j¿HÌ†di‚öéR°•›{9àïî76òNğ`<S{€ıQ|¿+¿ğó•ë&Ê ¶Z$‚(–‰Jôq@OxŠµ•*HC!ZÀ"ØTRÄ†  Hf!	„J­êIvëWı~dİÜ«¿o
ã€Ÿíä“ŠUÓÏûçşÉ/“ı“İÒjÓo$¼éÑ<œÏáÿı‡ä¶ÏÉpoeú*ŸèZTR_‚Ñ5Škü¼GM8Ãõ1ô ë¬aä·#mEi}ßæ´T–Š‘!–Ï‰Ó[İ º0û<öáŞùà
X;ô–Q4Ï*Ñ))Ñ©¶ F M à  V `!€    ¯!
¿ÿÿÿü›0°`4…a TH2„„,_^¼óÍê®³ªãuI¬¢WT+ç«Ñè£ÒøQ=ïÒõ~öş´!§}Úsù­¯Oímü¾”
ƒÃà4ı<GOşËößKhç¦¼Uğhó%ÎX^‰²ùŸ‰;
o/^?…5ı¨]D‡\aé¦‰HbØ«SÄä‰{Y¡eÃ5ˆ„¬l˜¥Ê¨L<…§©p‹ Á˜n¡@°”('
‚b@˜Hb3®zç[º²Ks¯ßo5µf»_Õ9šĞ@î?TÜÛºZ~z àÏÃE»;<'óñ&´”w¯Úi]kÚ|ô?Í=Ô¡Ù.¦P2
û~ÑR¿À¯¿ñ )Ä–ò4ë<\Íÿ{ZOÅnp¿5Œ[ûÑ©îfe»‘çL°ÿœ»#ƒ ñê¾áê³	À[¥€$´å{–¯4ÀÆFi‹”s²s€8  k	 ×!Œ    '     Î·"¿<š4üè£&Ş aS4›)­Â¼¨°$Ú£ıË2ØQæÈ‡x´âÂ?[ü€3—G€ëñÑQo§R4÷qBD™T6˜`óúÛI[¸CÇ½°„»‘ŒÊüÀYBlM¸I©¢dCëšÅÏÊÃ6÷b!fÍ5Ww¤h—ıŸû-3Ö»ºæVˆŸ'İ¨¶Æà/“]Ø–G]€EógšÅÀD
!œº?KR¾àÊÀ\9ï¤?HY÷ÄÈ(=]ŞJµ'×ÛÎ"³×5ÎPÜ¶1I¸ìi—4ˆ`/Øí5N¬ê>kh-špú+;®üÓÖkê‹Á¦†ß³Ö}Ê`n	D•³•X Tqò%  S&_ŸÉÚQzÊı^*p/Ğ:‰ùø;2Õú)Ò ÔíB7ñÁ˜¹å£u›Ôù2‘¼Ä•©ñã’«òaåî™ ¸Á:‹ş©[k-sŠ¤jğ;èÕ×¿  å	Á…b,÷ŸmáÜ¿¡o¹ x+Ô;-özt)7M[ğÍ{º¿Ì“*ˆÀÏ…ƒâÑáú.gtSÓy†Ñ¨q]¦š¬ì¶SãÒÎš[àTJ·  â ~!•    ¯!
ÿÿ÷ü›ÂÁ0°`r……A¨H("
„+^Eg«WRšš´ÍU)Rê"4õõ_»~nÏ>ÁÓß®¥z½€Jî]cÃ
ÿyıƒGĞWÊCFàI9Ü¤¡ñœ×)<»»7Z¿eôvÌbß	\©³©…ÇgQw'OÓ•CÂ/ù£Z×Œ“¾ SU$â9j¾x|ÒÁ0³{ Z&ş E Šµ®õÂ*Á€° ,H
ÁA0J
…¡B0T$2nMe\Æ”JI‰˜8¯Š—Pl+|{õÔ¿çgßã˜Ç–o×‡¿ú"éñÊørë’píS¨zûêß³û
ÿ*koä`5FŒ³‹Vï~ôcŸ"îkñèÆ¶ß•u7àc°qp¢%;Æ]øuµ¦£zaİ~<>ŠÛñÿÀwŞ6×oäŞ/ÿjè…OØ–nTƒKf“¸È’^½ßCù|³·Vn€vFD†6ïˆ„¿€7á*©jØM:²Ü  ‰ ~!«    ¯!
ÿÿÿü³¡a@hp&Bƒ0Pb¥­ë­îv‘pœV‰Fîd*8úKß×¨÷rèŸSm^m^b" '- ş”IûŠ±Ï¡
Hı/»å3ñ=-ğ"ğôİ´şçCûºrKù@z¤ÿ©Ÿ—xÒğòš;F®¡Šï÷J¢ó;qÚ-zªÁPÅ3$ºêëÆî†õ3vIÙ6ÛÀv![%ÖäÒ:¨^]N T…Š¥<%²`ÀXHC…Á@°Pl
…‚ƒ1‰R®n>;•œs<¹Öæ¹‹İÑ©®±,cnsqŸÜübg¿_?ğ5Ñ^é+òIgt~‹×ÕMşªlíí|û=DœWíU¼ß¬ÿ%á Ù÷jn¢.ëÒ!gô(ÿ?Ó˜Ê¹ŸD­³~’#Ê7Sïúcãì»Î´“Ó]©áÑÛ#’Hø«ªå`¿ĞGÏ¾¼#ã +Be¢•e65¨áİy<#ÛD–-ŸIİ q±+["±A"4)Ü  ‰	 
 !¶    '  }  	÷Aš¥úÖL)ÿ/S¶ƒ€r=h}®@ş¯Àö%W~jí<ÈI1ÿyZ;×f†l„BÿD¬£jüfà¬ŞrQ°Ø.iˆFÊ‹Ç‘p)i¡Eô–­ıOEG[ØlAµ°âN$yîoT<n†À½?ZÊ’òp?Éïç³«@Ú…QF$×"4¨Æ4ÓÄÂõQ\Ò¡à{Tkc¼Ûû+àëwZPÇìc{ÒªôÁØ¶»+lŞ4.I>äŠûúr?pâÊ§:”hÖ%vÈmôL¬(/ØãmoÔ#…»âYª*Á¡P,%m!jFìœ‘ÒÄr…kyJæ™Ï7‚Ì#èfˆãÒ-L;G³©U_èÇ¡ƒ¡FôÜ¼z–Ü-ÜO…æõ_^•ÖËöÔƒ™/aƒ;LÔ›üLÍ¼ñG†:tÂÃOSw'X]*­‘ßëÛªC+¾.ˆö×ö¬‘Ÿ:²hY±ĞjpêîV¶ßDÿÉ(72Â±­ŸŠ2¡Ó¿ÏáDÑğÇŒLŸ’‘w½LÊ¬¦Â-C=³·&I€Y™ÌêÂ0’(¿,¯ èısËŠŒ¼ˆñÿƒKæG@R’±kÑÏ"j<Lyp&‡OO·#I€:è|'‹Ö7İYJeà<ƒo	[Ëò@WÂ¥[†Ş®ÙN®ƒäŠ÷šV•5Uíƒ¶Š­Ù»JrÉA§LÛ=tB8æÔ¶PÜ‹ÈÅk†|Ì‚Ø¼ù;Æ~ë²Àvü@ú`/Ôô™q£ä°[Æø)Äí¹1²o|şıÑ°®ÿ3{™HËWñDxSÖÍÚĞ#8§5{™S÷øœ®CÃ¾\¾®lŒ¾õã‹ÇL@¯à@a_"am	ELÅ¥$Éò][]Ù  ßLÊmM`XQ_.ÍÒ-ñæ“/6¢İ®Òu“Å“'-ëÆC™«º2g¸dœ1HóˆzòG.f!ò5ˆ
&/Œó¸Ax÷A_‘%µKÃ&¦§ÌDÓ•á_@£¹ÆKÁ¡<8=¨s¡şüú÷LÚCoÏ€nŒL"K"îìÍõ	\äÚÉ²‘ZøÔP¹`ÅCFë1#õS>zNºYWô%>om*ıÁµdHf¥ø°ëğÿ "I¬–bğĞ…eò\˜ªYMä4Påv*Kˆù)'²nJ~üN{Y‡ıåç=gp“D‚"¼ÿôØ\p:=%ú£W42ìäŠ‰İåDiÈ°ÿÏöì`Ôøáÿû}ÿİŸÈÈİ©Ï‹ûqĞ„'ƒL/æ|¬`ÁŒÿBñeiÄ¦ªĞaÓ\šÈ“ÄB›ph!¿ü{b÷°QQµ¶ìÈ ÷Ÿ¤"nX'¯'°ù\MÌC$Ş¦×,ÛŒtiÙµõg)„Æ®ÌŞàú'jêá€±²v~ë˜¦T“ÇéÏ=VÖgeIÄ•yŸOİ»áÍ‘ß^o¿¥váÁå?<fhˆ¥Øâ›xIŠcçyn8“T“'Ó2ª­_1æ•Ô6¦6†Òº¹[<î°¥ªÒ™§‘ízÁ	ÍQÊ}!­ÜNbÄë¾I/Ì€‡ïr¬á†ğHRˆàÎ½Æ)*¯òÆ UD¾YîÇf¾zW0¢NÊµœÇáEµ€/htûN.ßÂ”$€İuÖx@nÜƒ\æiı³wc,Í¤cVõF³ÚbÁ>¤Q±ñ<ƒÜ?w®æÁLWÇ€:	;aÌd>åKß%ŞóÀ‰Éƒ„0úu¹@qWçO8DÉøİ/Şíß$fÇI69MşÛö!w!à
,p9O\KG©éù]ÒÒ¡m×+VwÕòÏLî5g’Hsy£2’hmŞ¾™)`–²ÕNN0±(?i\Óg$øšşÇ+@ÎôÁÆ%-_Vî¾ğ _4ä:g?c…*Ú®oÊJ;¬&Ò'îÄi´‡¿âfdjÃÑ“A Í´•¿¼ErZ}˜¬	7dNóå¹dƒŠàëD{Å[|Xˆ¨KÇ\Î:{÷cúı1TŠİ>HıƒòB’jü¶&‡™£¥ÓT2*ÏİH‰O/*6–~«ğ˜HAV– ©yXR`‚®İñ½S$l¾¢ü¼ÂS]cÙ’ª0EHrŞÏiïÙ7BR“xáİR“'À:ŒÑÇ]áÄU‰=—œ™'è,c›š’óÕµ:WˆIÜ_ JÔ¹	J5(ìJwÕV—Öğ’máÄ˜ïşè¼ÁtÖTé!8û”HyÛ5x}(ŞÖÕ¬’£¸h90[b°Â+¿bWt´¾®*æ)B4Ùÿ Ã_hü!ºc½<W¨ULŠ$ÉŸ‘4ˆ(î1ƒÙßµTÿEd¤jÊ5FËÔ‘rà÷Ôx+¨ìN\ÓX‰ßgrT\ı‘à-BQ8+óZ×‘Y–ò°¥6«ÉRP§¬©¹p7%C.tv
cåw¸hóSH_Ö¶³V*Ş$æˆJ;vİ0dÚÅQüz¯aì*Ü½?#›Ÿ€ãfCõ©¦PäºUôŒt_Ò8>”Š÷ÅíwÀ!1#â«Í~Mq‹ô8^ø3TMª5GB{j6³İ†ñfŒzJ¼@
¬	uÃ ˆ›‹-¤ıÑù},˜ø?@Ÿ0¬Åj%—âÎšÓëã–#?NDò.Jmv“);qGÃ 6VÓØ+Ğf®@ÌYY7	W8Ü.”¾2š'æÔËPŞÕ‘¯:G?b1–Ÿ8ƒî¹R@ÍÍ—©Js£9º4D1Å}Ü]Á—B	ågÒÛí)H£¶¢8ïçˆâ—Ç£ÿ¤±z¥Ê%¬†ÜÜª`è$ ~ält1j¿
èñr:´áã Èùğ"‘^§„›9¸Záâˆ¡p?>µYâß•ØËæ÷ÃÖ§Œx‘*\W¤tdU®F©Œ8åø0,ŒútçÕä5OšÇN6Õµşø«J†Py÷KnÑéW6K4Â¾VÓïn›¶­ÈYib‡Eö8İ¾?‘~¤Èv&³âU¸í!v$V­ïäuN«® /hè|>fÅKv§rŠG™l8>f°$µÕB¦°jheô­ë+ÄzêŞK`¨ğ	ç¯İê
”9öÆ9>76^‡å.5¹>oì`N=gĞèÓºp.“ ŸÃLî¹Yd› L¿™[.QbüY6«¹&>q5å¾"­CÀì{<†}J„uËÏIŒ‡0ı|Œ¾o‹RWlÁ]<“s#ü;ÇşZp¶­øğÎ.ŸÙòQuYÁ¾eÏfõ½{qm˜‡Oè¯Š¾d¬X{qìéW9Å	Çœ²à]”ÂÅi  
 ^!À    ¯!
ÿÿÿÿü£Á€°`2ÂÁB‘EŒ·æ»ÍV¦-í’ê^VZ/.e¼‚öO»-“rü!øFzµr?QÁ½¯ÉüĞÑé†ŸÅ­S9
¿MÏ†/<—¦~OK=šgà–A¨¼Í²ùŒ%J6çµáÏá>8«)×bÌ`~ÙOÍş¦R6|Ôt*Æ:@€KÇºJ nDcR2(R7_`€nocÀX(&B…` X(AC»JCT½Ş³UJET‡Òê¥Xßøû/ÈÅ_CÄOÚoœ¼ÿ<;±,¶éMztè””Òç%¿rş/é~(…g¢ñNÍ+ÿ|Ñ9péø¾ıòóêºW7Ãì[ÏŞ¾é¹[¤}ŸOÏ»f1˜ÕÜ §m|‹şo?ÊÖ‘ÉÜõc[ÑmïïT³Øï³ü.ÿóİOÉíBÄıt]ù¡¬(H¸¢H¢@±<ôN`º  i m!Õ    ¯!
ÿÿÿÿì‹Á@°àV†¡a T(%„„-w/Ïõøùİ¯®Z¯3/m‘RL…Şƒøp·k|§L!o†çôÓŸzÒD½'–ûK2¿DÖ­	û0bvúµÁ§%t8üz"lÒëòNii4ˆâRŸ[='J¦©“Ôƒ%~Ÿ7ÔbØ™^¾$µ&´Â¬¢€Ií{ŠÊE‘«(@,^ê) Ğ.Â€°`,H¡@°PjAP‰T(
!“[‹Tj¬ªµQö•;çğ0Ÿ‡‘û~½ŸïI~^4½¼·lÑ§f¤Ú2©n½eîûíºû+Ê³2ïã02ı,rù§æÒûJç×ºÿ–)€êO’‰"M/ªfæ¤¾©ŞàS§Ï¢õ¼®CŠ!9·ÏiXPN'®DŸ¥„f;à…ÿzÍÖ>+$ú~=Z¢İ;ŞÖû³ÇoÜ•Á- ¼V¨ùà÷ûÂ¡g6øD8  x	 )!à    '      ·"¿’R2É%š[l *`yâ•M%éÚğË5Êüw×IV ƒmïµKØbƒR¤lkéø5Û]\
Ó1ÔüZÕid‚×fA¤hÙN/ğÚ¾ÃıÒœ;g÷I¸bŠrñÊêõZ˜;iå
¥x~ØüÂ"¨–½Ğ‹È‹¡°Šu¼.”V>é^¥¸pÓÎ$@¢MsÔ·”¦Q…?œ™ÉéÅ&	74G±I”DAÔ"Ÿ£’Y‚uÔñfk
şrF3çv³ï÷2¤Gº!oy/7”¯°™6w¥¡vïf¾„–†NĞ0m·iPhŒ„	ï'—%ÉŠgµƒıOúŠ8ìn§ß23¨ƒ
(ø$,ö\ĞTx~N&İš€Å=§”ÊY ¹G{ë„}åvÔÏ2ŸÒâ[Èµ3aT½Go›õ¹šÒˆ"øÓOQ8Î
\_ÂğT~4«0ôcë’ËÇªÉ/|Ø«H¡¿<"$†¨`
Öœ…ÂUØg&Jeêõh¯D€‡!:-Q¤¦u¬l£]îgÊ9=.ç<‡·³G1k×%ç<¤L&ê«^Ÿõ€ßÈ±¸øš¤nÃhè[ËFÕÙ¨’é×ß¤9EÒ%·.ù·Ùî‰ßìªİ°ÜO&¹fÆ9Ğ¬©nD¥³ †@bŞbŠ¥“Ó¼şcğE7b`
"\iØ_19!Nu!fÍ0  4 E!ë    ¯!
ÿÿÿü’	‚‚bÀd06ÂA@L$	VÆª³ÏÍJ½UÌêUÜÈİ¸ÜL‹öAù];ÿ‡ô­…Êš;|Õÿ–~0áióö%ÿLİ%ˆ‡©õ>{÷kÚÜ%y%]}ùÎÁÿğ^ÏMj´a¶4ÇËóĞJØêäóÉNö%(ššAÓRõ%¥Yv¦!ÚØ‹’Bv€›`(¶U	’¦rvÌ‹
ƒ@°Ğ*…„ƒP¡(„„* ¶uw/*&¸ñÅ]UZ•i¯f»¡·üÿŞş ‘Óş7`¯Oğ‡ÑäZ„ÔñçÍ>Z
ßÔô*†î@+—¦}h) l}.0q~Øu¸ğX²3rõMìhL0şùû]«!–8ãŠÇ—,	ğû§×ñ±™¾&j¡Š*t Ë‚Ñ ±K\À„C€  P i!     ¯!
oÿïÿü£Âa@ä0…£@L(
‚,No\ë^².äfµM2ñ$ŒÖDşFİ{9ñåå«õ_ÿmáÆ]J=	ôĞGû‚¹Q÷æíqÑûùm9³>÷“ü'ô:©Å´cÙÃĞº3sZï»ñGıÑŞ’vVv~ÔVw5z&1:$¯Ï°+ÛM%3çK«õJ¨RŒæuƒâi=¤Õš“ !M%(Ö°èa XH
Â0¨P,	ÂAQT"ŒÂ" ¹á\w©•n2:Íesç|ws5¾«ëç^yw]×O[°õÿ?Şş^nƒş›÷[¹òËúÖ»eÓ¯@Q‡çu£?süÑ±ãZ/›Ê?¥{+ç¬ìñ1½wêZoŸíIûÅ£=İ7´øDùµ÷æàË®·µ^I[Ô>Ó7,ğŠ°¥dÇ¾íµgwOPø%#oœ5ı `Ûp  t	 İ!	    '     Ô7"¿„ğÔ¦è+h,ÏPÌZ¡å¤1WÖ}‘¸#8k¢‡×dâa™Ğí+ë '‘  JXÓÜÉÃö«ÿi!é6Qs[)bam¼Èg/ù «½ø¼oã9Óyş®æ4V+•ƒï¨	ÇQÀ‚–zv4-Sw8Ï§šÁ>ÿ¯SßñQ1m|q	ZÙ½Ês2ĞíÁ³c‚-¸ò¼€áòRœ1Ò,G-ÕØÀÊÙÍ•“\$‘öıŠv98òÔuQç
mO_ÆBŠÎágÕ$˜EÍ­ïÁSgCøã“>ÂLü÷š8…Kj­ÁÙiVpÊŒõ¾]0,ÂºHkÎœP¢Óly¨:è¬·`†>F´;U]£Oö¼‰e‰Í9kÙ'^Dj›µC¨ò!ß_ÀSĞ†¦±‰vb9R‰gJúÃÎ?Ä^Ï7nˆ¹s¯îTíÅåA6ÊµLª3È´½u©–2Cwš%c§v*¶‚âğ0(eÌ’ã±\ÍbAq×åC£Œ;	Û,^f÷4Ò©­âq¨Øñ©Üá|		æİhndìŒ˜$è&jh óáØs´DQ$—®³A~%î·éu³ËeW€g¥ÀÄG  è f!    ¯!
ÿÿÿü£Â€ÈX0…‚âCĞ"¶·#ÇóúQwÇ¯;âê]TÄ^D«?ÀöuQ¿ÒßRi3pGëõùı~%`Éºÿˆİøğ5Kşís{Mw
»Zñ|ÿ…QÃBnßğ×ÿ@„ìŞØôŞVœº{šCÜÊ0åGG³ #Ÿ.G8 ·<•MóĞÉS32Å‚iZsšš–Š	–’QeÙ4†R6è"\#`ŒDÂA(P&
Â0 ˆF1ˆí8×}su¬Õ^]uÍÖ¹óë[jµ×^{†¶y—+ğåÖmŸ”zçMÒwË^Uø%é×öïå7E¶XœL÷<ƒå“òášùwwø.¸P/ÉÙÜ@um§àø}ÂÂ{øÎMø“m"Y¿ÿ¼«BÕ'ÆÎ›¾k‚¡W…_/ªÍ­)[àÏl,)Ê˜@?Q	Œ!äş1 íU³o»Ç  q ^!+    ¯!
ÿÿÿÿü£ác@h2Â€ ”(
‚!H"‘­ëÇ×}Ä×º®"µT¤¨•çê5ëşIáláÛ^‹vïÛËß¯œ–ŒSü=|ÿ¬Ë¼õ·…äßåöÈ…Á6³-äu|³„'-Ü—Jüa”dâ³>ìÓÙöç>Ü•åF<íî~&¢”ÜÛªeÁz"ïç¥&“2·­&·™c.°1Wƒs¼l.Ó¥42¸+Y*µÆ(Bûå!;½H„ãJ
¸	”„`¡Œ*
„Æ%0ˆœïÎj·zª¨âê‹_2Tj{/s{ø	ê;Í«î~Š|*á›úÓ«]Iö¹öuWıäómK´ÏÖK~KtÍiMƒEBÌ£ñ@ºcS/™bµA£ÏûÇÆ[î²~{¬WÓŠÈn^„ó‹€/jÏÍğIó3uĞêı^`ü×_ "*¸ lĞ
Gâ Ó!pp  i	 	R!3    '  }  	IAš
%úÖL)ÿo· "8³Ó'¸Å‘ùÀ—4ŠBúgZu¸™T?­öÓçëÿ×·*$;šœzÀÓ…ëJ­çëÓ	}õÓıÜ,Z°R°pyQª´ú½L%¨½=ÅyÙ§¨2l ²Q·Ö»Fvıı½ô…N"x¤„ZÔó €Õò7ÍêÓKç²¼ue[07Ó“
c)‚ÖĞw"ùF F ŒÉ
.LF6`\kg•hÕªFe1¥Î!ÎÔnÒED¾1¦qÓ ë«,€(â`/«Yìãô«°-Í™şC'(«{*ìHHJlceâT4„ê7i9ùÏâ;ï¾w<¦ÈËß1%*&CXT'ˆG³AµL¥±ØßiDmß-}âM­æHjœx~iØĞÒ1o¾èÉ½ñ‹z×C3¢†JR­{•-±áTd¨øe[ˆP"òÜl¯1ØC¿ñ †˜qÍ™®îânbÍòz>.'¾Ê;ˆë¥ePÃÒ)E-J±(<h/­.”¼¥Õ—wz™]9tP¥¨pÆŞw¤%xc…G
Ir°Û dR¿àï¢rç^0E´›š¼øbÃJ1ARİ›ºé[ÂyÅµ\ª2ûº2^PÍcã[ñRnÆÚmŞ"İ’},¨)wr–l»I7ôv¹[—æ×,Bîsd“À^ )ˆÍjR·k±è«À¦<½h…2ª­;é}ÁËÎ@Pß–ê)EG–TÒLòÂkTŠ+
ø”ø‚Wòª6 4… ±©²p²oÂİƒË¬i“Œ½WÜö/jr½Ğ$Yz§øz¨‹ÿ1³±Â§A® ku“1Ù“Â³³r³S;ĞâÜşDúÜ59K«K¹Ï¤§'ĞpÄ>o¤¾[àc¾,©¨rÿ¾ã$èfÀwjeli|9Bë& *6Ïî·€¿@¬EP/éÌ‚“š‡qx½³øô¦-¾µ}U8—ÈŒ¬`[BĞİë…
öWuÙz9Pç‚ĞWÈKIÃ“»zÏ®ªP<ŸN$òï)Îû¼ù¢š/Ğ@ŠàÇB<Ä*Øj³¼ƒÌSIúS6×öºÌ&ï–lH7iGbv-Î*Æ6ç˜qƒ5óQ1­{ï4;b?ÁÈEõÜq	ìx¶ĞM=÷¬~?Ê¨!”(„UwjÙV¨.SŸİÂÚCûğFîxı¦0–s1aë!Ìpz³«¬jßn¾†G¦fXR#1ÀÆ²î;š/jíTuÓZ–\ª9D,İ›’®ÚìÉM8¹ï(Í‘—sh™²lûešNføíËg%`µ“º('QÕ´=ˆš9rÎJ’ß!ò²f<2‹—’U¢=÷AÅ”î7ŞÄxFÎÕG×fc® ˜@	.c˜Éõ`*k(é}“ÉˆQØ4‰ß $>:ñÈÓKrĞîwÔ’Ç*"2Jt…ÀFÜ;8sfï‹äö}Ê^}µZl<Éiúæır9xW›ÕUÕâNÀPááˆÛOoMÙàìY"ÀjÕ®ÏÓ>&4HzP{tjn×÷è?‚X§â òPÂîä‰ Zö³À‡00uèÓ8qëPKˆèì’ÛZˆk`t S²Ùøú0³¬ÑŠY}Î,]†_Ù¿EøBŞUWM¦Ñ¶ã§+½Y«-Ów]ø—.*½j<)>Šº!Vş\A£®ø.İŞ×òn’ÑÊb¤ÎÿãÈ[Ë±ôƒL5Ú!'¢%VZ™7îíµ›Ù@n?F¡r¾µ3OÜCÁ§@±±o—y°zCÅÃ—ë¬%ßÌ0¿»SF7‰~šxŸòªxÙ-¾£Ú¯œ8Ó‚¾¾£éY&EF‘†àg`Ë½¦(+¨%éQ÷±ÆŞ\ñgœ‡à2‹«<C¤?V1IKÔ˜7iğ=DRÒ‰”2‘0lSYµu5«$Í®‡½E$Ã'x!¼5ùleáä­§’KL-	b ¬ò¦Œ¥z¬ŠÀM>¾\.9 Ê8`’ ‰3bš+Ì„	æåşŞÜš=Ï›úÇ"væ£E¿ø˜
‚ï/Øª£ëHª1ƒ!=çéÍK™^W±05¿¾ê|y®—à@WAra]	û+ÊÑ†6—Ø|÷:Q{°Ï ºà21’Á_:Š¦ô 
S¥İÀııŞÜ¤~VQ6ÍRyW¾Şu®e–ÕeGÓ	D`-ş‡ºAW!ñCuØ>]¡B)±¼í_2Eü‰úMË±Ô=útc!#ˆÜ¯L¶ÃJî?Nmwñ¡Êù[&!ªÑ37øJ¨’tÌ±Bªy»İB[Æ÷ÆªR"×=­wOBwº¶	wåT­¢c&ŠS
¬ì¨ÄêÁ#ŞŠëøt‹€šÉÈÅ„3)–Oş	…ó‹ŸşGN>JV(::ˆaV­ldÉ!·ü  ]§ız@¿_g¡Ë¼}¦ìkÔãŒgıNx›rågã'`Q|d{ËÕ¨ÄÏŒº(Ó)T/ì/xQË`£5pM(á&½¾Ââë}÷äŸùÍÛp8S:#÷Ä§#ü}Ü1'~	§¾M/=|‹	7`9¶•(–ğrøeàğ]	µr¨D¼Œ»Ä9î#WÍëpæ'0B„éĞ®•f“§ö*“0g¯¬q+­eu?r1<›.†(Î)şŒ„ÈU•ÛH¿ Ë´Fôl&%i7/;ss4pN´ ¸î–Û™m€{ÊôÚÎ¿]*%~Ğ)JÔÌÙ`î^ÄÙ'3ñĞÄäøHµÌ›Ûã5@­¤ª;zzğÈÃÙP¸suqº(]ù/»¡k²‡ÿn™^«Í‰E¡“3 «š1Íü¨(Ç«kßoÈkrÑ97Šé[}g¹?	*$ÚÁô¿ÑÔ¨™üš,Œ©Æ|AHş3YƒŸ<™sıC•ZÒ>Ö÷Â"‚>E8è~à]~4¿¯nˆÉV½ÊØ«µ˜»¿+ğt|íƒŸW+.Jä½ÈÌAbòıÒ6İúkÍáéû
¶Û½Ü·OÛ’NÉJ}R›C§Só,©
}g­ştâ*Ée•PQåËV<Ãé°ïş3Bñ4¤ï«©úïF„i!œZu¬ˆ  	] f!@    ¯!
ßÿÿÿü›@°ä4†ÂD(Hb¥núúşŸ^+®ú©ç*éReÕEEÜşFé·ËøÛ&ÿC|Ä_äi÷ş¥ú//f«ùøGq$ª¶2Ê>WæÊf!‚»ÏÿœF•L??ÿlK6¾‹ñG»Ú*uD««º=`}½\Õ<[¦E¥Bd­†€¥T†Ú"A6;<q®.4¤Ii!N0¦FÉ®Ö¥]†ûĞØ·ÜyÇ¼`Ğ`,8…Œ¡CTH5	„Hb¢¯?¶.T­Tšİ©.mN¾)Ïas¹ğfn‰×¤=o¶âíß×•^¥7¦gö©vÇ[âÚËÏÿ–EñˆJt¤–ûı­iaíw»!Òø°õôf~m¥â;ß$×ÿ–ú·¢B¤´ûâOûÓ[Í¬ÄÚgÕåıÆcÜ]uğ£B;pOõp=@D•ë~í9àò¯áD  q }!U    ¯!
ßÿÿÿü³Å@°`2
BÄ ¨H(B	…B+k5õœÊ¹“Uí„”Ëº2.Iú…ñşµW‰jŒ;7}?ï>‚8|àá¼ øKá»AêuüZ?¡í=}· ÿ·ëÕÂê\"s÷†ÕCüİkpÎŞ„SË¥Sy3Öj,‘Ó©ª¼}ö´rf-–Æ~½RÒô¡ÚSºj"í ¤|;"ß–äN‘›@#¾åMğ°¶Â1 L5¡`¨P†„‚¢(D&5½ñ®x¬«nâ“"V¹¹øÍøÕ}FÏQ/éV›Üê­:Iì¶9ní]Îˆ˜5ì‹FyÒ›½kR+éª÷ˆjøÖÊì÷öÉ¶¡ĞˆŞ³}ğ?Âÿ_£?[ßz8§ãî±¶é^Bç_¦nV1R¸Ë«‹té†¿\†Fr¹ÆÂ“ôèğmYÍÂW¿œ¾s¹•°,, Çİü¢?ÄÃ¤ÀÛäÃ´  8  ˆ	 ?!]    '     6	7"¿ 6ç	@Q:‡áà	·^ï/š»t–©Ïx²s'fÏ@©áÓÿ`³—:°‰·U7ÃşÜ@0ï[!û ã'¹ sM?–ßƒñœ–)‘Ì=ĞÉÎ#v#Ù¯‰hTÙS®®;¯}Å“„½Y„'¢.–Â)lVì¹ŠÒYŠğ\L?èíÕ÷'á­İ$<ÿHK‘9ªDÔ4³ÓÎ›ìaFúITÔ–If¹]³õ4Mu"Œñ£½vyŒF×—‘^öÒ1p:-F+	2	L¬½:õ*ïb:‘\Sp›ÁPy‰ìûÍ~¶°æ=;]"Úáß™xŞÈäVö7ƒ' nê+€Ö÷>,l#ÒDî·*`é”›ü]U©)ì$àØSB‹Ê"Ì³8G{ë4@L:ÁîŠ !·ÆUƒ :›ŸÆ8˜^”i-s.ã›8
1ª¼¼,µ/häß5tHÇãe"ìûjQA%¢§j‚¬’¥¹ öèª™ÿ–ê²xŠyan±‹^ë/nÕ;Ş&bùV_§­¬u¤6z„¾Ä`'²e¸Èÿ4Ë±'uo?¾¤ObÓóGZºùáô‰öoØ½®`%Ç¢EL² ÊÍ5Şq3_Ä9¦ÚÂVwÍÒÓÂ]5«
œšÃ¹–ÿP·õµÄ4ó¥Gcï‘Ñ˜àiá½^‚¡è4×^|‚†5Ë  J o!k    ¯!
¿ÿÿÿü›ÅpÈX°
‚"
Ñ»¾ı¼TÍI½:™¬%")jšûÖ;¹ÏÙáÃú‹wô×Eß?|>×øk_ıø??F¯ûsğ
ş­"ô(úõoqØ|?ÙøıÚÈ‡Í¹…{ub×şö44AßÁ€K?/4şefJ‰_èRĞ(O$‘ü)‚ºcû–M]kK
²±°+çZğ_“ö¨e*ØšÁ•iÜøØğ¶Á@°œ,$…Á@˜Pª	ˆ‚¡ ˆŒ"…Í{{ı÷Jë&õ×7¬LÖí¹_«øÏ¸Ëöùùw{î¢ú®azmş¯¶Ï»øKªM!İ5úí|çÿmâÆ9V€üÌÕ/ïİo¾Ÿê¸·/õ õØÖ¥ò÷’µb«æ†VµûÍ„>¦ø|tØ] ²±ş¸T¤ıMàp~€dÙÃÆ±µnıbÏqfªQ3Ñ·Ej ½À˜ æ¿ŒGğÀ'ó!~ãÁØ  z j!€    ¯!
ÿÿÿÿü›¡0à.	ÁP H(	DA²µ+Ÿo[âµ1ªé%²UÌE_?Wùªé7¬zî.¡ûTê¿×_nF{¾€|¸ªÿ*”›ZÔ–¯È}`b•Ÿ¯åıI­´‹9ÑøoO×s|8õáŞœ×œõˆ>—o:Q|H3¥R~éï…tf>I‚Bª%ï5ÉQ‰k[$ËGHÁ8(Ê¦¢"%¤3@¨†a@XpB‚p ”(
	B(fi{óÏäH—ZÈÉZÜ¹ì¤÷°»èMªî·g]¼{ºÜ?D=i×©aÁËıòÏøİPöÑèÅlìx=ëáÛYÏ“ëÎen‰ûa­=½bµ˜}='²jAóÎmEu3ÃV
óyıw±€|ùÎñò-0ÆëÌ‰tĞ÷¬À9K„¾rù?–Yª¦m\5Ë·È'™p
Âjƒ¹YL@°š—1í†ßğ  u	 G!†    '     >	·"¿ÔÅ`~_k-«	@40eøOU·=§R¶x.¾«ïûÕ¤ıö~HÁ¬å¥PÁIFÂf»Š…ñú£³iØ\3ÎmiÃ:óşÃå5§Í”+]û÷!½šé±(é7$s‡ÒvIÊÜÎóŞÏÑ[ÖÂï¦>ŞéŠ¤,?ÏD¼§EøêÓ8=À,Lyßs4=OÃIO'Nİ!¿ªE8µ
=B@¸Á(" G®J4«™XÔ:o)$".ÙM	~Z–üxË.¹JÚ1;më„>éŞ.j¦_FIòøUì–·óF»À¨óaëŞĞTQdç-<õr,l>€ËàÒmXÃd‰ÎY­-æñÆ±İ‡w]ÙDT@½.İø=ñıºAfe?˜vôïXs•êQ9Ä%soã/HÌHóÃzPljËì%-¬Ó ‚NÄ‹ÙzÑŒegÑ®©wÊm»çUŠ’_ñ­	äõLãÜØ}Ø¼–r¡–öùº¾TÑ×	=ÖÚp¾Áœ ¤¿F÷óÓŞdL²N´#ÒŞ–®û-(¡üÏ³òå¨=â¤_#ŒjBETÊM1kï¹r(õç÷)Î†»eG:nBL±ş€aÚÆ–gèº›‡½O†Ü5 wô‘›Í¼I€Uÿÿ·!DR¶8á:åO¸æD†ş ¼‘‘f…ÊƒÅï©5+¥/Š¾­:lƒùşÛ*ÿ‘‹¶úN9;¹6­z¥È+íU  R m!•    ¯!
ÿÿÿÿü«&A€°œ(
…ÂÁAP&„‚*ksNüûæ¤¼iÔÉZMÈ«ª…×ÀÛ•šºS¾äÕ'e>}_·uG&½z¿H°:xêúÚoÑ'Ÿ	¿í÷ÿªÀUw¬½Q‰&Q^oFÂ“M‡å=]äÚWOG®§šÙ+>ÌŞZ¿ùĞd%´cZ×w4ë‰Ã—¬+v+(¯HĞÛOAi¡((­¬,¯«Ah!< ‡ ! ¬4	á@¨XH
Â¡BP$…a˜_§Ç7>8ı5¬ß—ÄİQ®o8æüùªz±¿ş™ÏØk˜½ãôïõIÚ~V¢ûéé]÷}HöNæ?»ü×ù0-°l‰øì]¿YGóQ^Î˜şÕõ_¶ùPZ
k½ÒE[¸ñz‘4‚ĞÉÈİÃ³Ğ:~/›°z^Ã}üîtLY½µÿ™Í0?›¤k©qú/’ø€8)R¤Â!`ii¦o—­À  x r!«    ¯!
ÿÿÿÿü£Ã‚0`N…„P H&„T«^oŠñz­_}g™ß[¼©­Ìˆºàsêëª6n›õÿXûGëÛ}oÆDŸ¸gûGâĞ¦İİV€y|ÀajİµšÁG;ØÎ±¸IŞï?‹¡ğ"çıadÇ‚¢ğÙñZ04öš>|%x¢}Àæ#œÆíı¡·’÷#Kè€¹r]¯c‰ø:!ER
s¥È$•*,Ë(Ñ”4.Ã€±&
Bƒ0 È&Â%0µãã¹—¬­$ë{á‰WLë»ÉçƒÅPÔÛäòõûİNŠ*}4ÉÿoÖï,'?›[°3ï£;íÛıª‡¯€ÿˆ 5ù½¾6±dqéõíß!É¯h1¬µÖ ?ø<·şÜR[ú}ù®§½´ooín–¥ê9½½š‚9¶Ïáj½\|ÛŸ¨u 8Î?©ãÛ¡:Nrç÷á¾š ‚s/ZAQ[|å|ÿ?¹Ìó~çÂ  }	 
=!°    '  }  
4Aš¥úÖL)ÿ{l˜ùşPş IªH?­œ‰–ÈÿIƒ©0=K5z–
{—šì…™[³_[©	½ÓR‚ì/®Ó Šª>¦e÷ÌtÛS‹¶æËËgøÀ¢“HÌÅJùzzaÿóhÎŸ—ÉNS³ ãfBÓZ‚u,á˜”å	Xá_T·Ù|ğzÇgöjß?ñH®÷Z5°ê#G1â8ˆj§“vıIôòÙ†k‘ÑŒ}IÄpÂû"ÄO
üßÍ('_öÓï£ÆFŠ«eRİû­§{’æS+ò$$»x šW§
l{Pş½Í¶M}f•=N4ı]Uî¶æë»eÚ—? °k(ˆJxXêoÛ$0ºàx‡e2]*hyP™eŸ€;Ö~"é:½Š‚Õôn¾µL¯Ü>\ê?½V»û	p÷*”FÏW_£ßÒB*â°X®µ¨¾p¼ÉøI–üé’ £áó«
ŸõĞh5y°sÏæH†Åü
Ú¬x|Úk/ğeÏ82§#çnÎÏßÂ±W ğÌşÌø‡ŸŸÉØ‚¹Èº‚¸y·Æ8‘ÀwÃ¶};¯³DâÿÎÖG<òêi!‹*—t:­G¢~ò»Å˜Ûµ·Wü4²qmÖ)@ğˆ…­]d†Ç¦äL|1…^İ¢9Èûo™¨“X‘	â©¶²é™È$ÅÌ6¼8f^¤™>m.Ö`8·¥NÕ-ª¸€#ØâGÇØúŠ¶4Æ{×LÛ:}à«ŒLş‡W	C==}yñ?ª¡Æ°†º‚"û|ÜÈG‹viš[Y¦óôIìPjGZÔšúşå«O˜[Ôˆ»/K‘ƒXÙW0ÿ™ªÃ3ÎLa] °J¸ÜcÒ£",J‘½ı8¡˜@©€£ÒôHâÚ»#ÿè}}üoŒ®€P,àÑ:'ı…ÿ©vÑİ#ìCnb¥YÁ•³S)•°l,w¨&øyù·¿oV_ÄŠ•û:é´/³oØ­¹ö€¾)‡”!Û¢bLŒÎbù³¹é±Øì»u•rşp&¢VG‘8"Y¿¶på®ÿ}ª1äô7Å¼&ˆ\á¯ôÀ·¢°>¡§8ÆMÖQZñÌŒ:0ò1ÒòÌª'€Ğ8§}A±Å
Ròª êµı½Grkq¬ô¸!F±É!¼PÁb‹‡qã:Tß£“æ(©~lÒ—½e[›NâLœ¶á2û¼·ò›j"*|œ“cÎeZ|LÀ3FÜõY`y>ÏŒ%ºMÛ÷‹ÊY)´l° ÖIèºGN—Î©ÚQ¡ZsáyÔË!“‘
¯íÀ“>NÒåòS{gUœ¢Ïõ„/â4jvÑÙõLØ·æP_öï±µE–èÕwÙæH •è(°,1Şç£¾¶’eœ¯iiaÙ¢lÉ£°ïÅã¼{ß¼^K)[~ül¸l‰ı•ZOqìÏi}íöXpO¦iö«Ğ¸MG=Ü/°Öğ7“?¬ıûìÀX à{£myæªúéPXĞyDw›\,¡şÜÎÌÌk•8Şå^uh‹htêt2LatîògfèèÍxS ¹—øÀ{ ã×Ç|²ïÒ°¿òˆÊÔ­é–s±JQĞ“¬˜O­ÅµN˜1ıF0—íÀ
îó>_‹Ğ~¡¶€k *ÂXæ{K>	9›f6d–½ ’ª#õšk$d^åã©ñwç³,ÉmÈÀÿ§:ß|íó{tóÇz”YˆäN#p±hG²¼‚p­ù‹òj;o¦—û&l¡ÉÂ]Éˆ±šÙ­xâ+|”Ú³}
ØÄë‡ F°ß–…J €Œ2’ørb¼‚÷m?cÜİÒ£,Ä\´•¢"æçRCa4””/RìëÃŠO*é|›×šú¢=¥ cqİÇyÒSt³¿œÊƒ¿ Üd&<‹9ßªq\FûvÀ’ë¼£¸ªç‰‘8~-à€hƒº„·Š‹[zœÄ²o1Ú^[Iaôâ&¬Z¡ ¢w¬»§ıv›´–ª{¦dåñö8jŠcu8]ƒRÊğã™£1i„íë´â|¸<’mæNÔÏ³ÃXõ—°» >ò‡ Õ·µİ{QJ†\9^bipÕE±Z’Ó»‘o‘ÓëJ”†Şâ³U‹r>³=£ç =Dc[ˆW|MÔÒ78k¿-ÊîtéIZ>’¤™†ÿ™÷ˆ}Êphİş{@±“‚ú681
9KÀq$æE
áÒ¤œ(GçÎéx{IòYh-½±z˜§¡Â¾"3p§øDÎrwí ”½0*)ç©1fÊ8ñÑşTt(_hf÷%Ãh)@‡Ò3G;<ái©¡ÊyÿRÜ4ı^	$Å}Œùík»/œ‘{Û8t«óç´»Î9åè¸ıÉ¨œ7İ^p·å¨3@T|mÚû›œÔ??‹ah,'"ª3“¢Ry”Y@ÿF\ˆŠ0Ëu6Ÿ˜àŸÒ R>‰DúT$G_”u^r†Fşú‡iJfX›Ó"éõ}ê<¶Ó°f*½É‘{G™Õ‹Fİ2¤.Ï„ù¹CJÅ¤³N_—\°ÿO"ò;œƒ³ÇåpxE»ÚòR>+WÆ¹vÜ²i‘Iz˜¸Äs¼3d_oZÊØs«³¾¬²\P{`k“€–¿Œ§$Q
1R4ñ[Ó	~o9®E9Zl¾´|7ï®½—¯WÉ3b£‘fC‚*ÎœŸU}ıûv%wQ5[t‹˜®­G°¯š]üëNÀoû–‡%kúMjmèÂT¬@a…©EHŞ(¿ _ÃY¢ÑÓ&¹@

RuÕœHŸŸ&¬Š¾ÔÎ“>ÕôlX=Øª6=ñœ@²Xã¢™j}n>¼vÌùf]ú:£eRøCÄSß8†AÉ¤#…”H*X}‡{®öUÇ±I¹ˆ[İW!ùM
ş³<½wì­ˆJÖV"À~£ê>~_ÃÜqG‘A8Mág8Hofc¨{Ì+y’/¼è•eó3cOÍåÜ*N—ÖÚß$àsĞ‡Şœju‡cÉä{¸ô¯ôjĞ×’u¿Á
Z(¹¡ğÓËI}H ­ü>#x|¶üˆŞ€* Å§wø`cú'qeÿà/0òtGÈñS´ ãú•ôIuGÌç±1u·´DõC¥Õé`¤«rÍV6Huó”›çï¡fÖÆ0¨aòü&½İ³Äé6F4g„íßÔÜ™ÚˆxJj÷…wC‚ÂÕçıÜŠø¨kRMŠÄn7:4*MÄN³œ'É„ Õ8y¾lœ¾…W‚ÜÁûğ`xÒ¼ÀEA`Kú9©zFª³‘-dş$[à¬<p%‚&S`Ïõ='ƒ~·¡/– •&¹M™ä¡Ã·N»Y"©
›Î!×‘ôç¼çÃş½À›5Ô=pÃÁ!Õ†â˜ÿ•l‰³*$gÑ±´šu+Û>  
H e!À    ¯!
ÿÿÿÿü»BÁA°hP$ÁA«—ÆûÕx¹w+ÍUÒïv«ªĞ³Ñnıö¼ø¯ÔÿëøŠx9êwFÌrí„Ãï!ÿWé¿wÍ«sÂÖsoîR†¹›‘Ê˜ù¼½ªÀµvT]ÇÁÕJ£;ânÃ¦»Lû«Ê5u¥á¢AZZj+%È]Ais‚±(1¥KX™À,dPJ°°"¨0&‹aÀX(‚¡a ”L
	B&0¥TÍU.d½T¨¼•*2ÜySİ ›p÷«ÎõùõS6–údøgäözK›qØ¾^ïÖ\wj“Ë<ú– ‚œõ¿½Ødü¯˜ Ë_ï¥SFªéõ^BCçŠ‰%Â€şg{Ê	pøo.KÔç¢Šô{fTÄZÜ­AnÊü·döğì:aW*Ù`2½ÏÎâ–å}€\À:¥@¨)ğüµgÙÏYF^Ëƒ/t8  p ]!Õ    ¯!
ßÿÿÿü«Á€°¨04Â`¨PD	Bªæqï÷çÖ«WYÖpµI’ë%%Ø×†?mòU½=*¸Ÿ·è3ÊîàCÿ>ºÒã_Ú`£ìÿr. và¦)î?eBñS¸øWÁ¨aËâ
6¬˜k¹{ÓÕgUŠ<@;uà–KH“Ô´¸£:Ò¤a­®‰Å6Š&
èaº‹1Òàq,¸‹(3 ¨Ç@!˜41BƒQ¡ˆBâe×xµI¯<¯w®âa'.½êŞw;·Ã]÷gv}5m/jûõsÓçÏw×DËı|½Ôõ.­´Yä=%÷ÁCæŞš;ï~¡O•z¯}4WfUñ±?Ç²}ÓTá±Æ5ÿ–ªÏ/LWÃjäÂ£åmDŸÁ]†jÔÖmÿÙ5CÀà<;§ó‰¿>Úo5}”ÌE+˜\E£ˆÇÙ,í®°<Şóà  h	 Ò!Ú    '     É	
·"¿ÔÅ`~gÏ	–É[y¨`úi¥O+¤¡n3@b§Ï¬Lô„èa”£èyÏí¸æAZ.¯©—û&½ËÊ.s½ipè·8ºYœ>6¢ÑÙEâŸ‡öi/?/‹}_•d¿ŞeF4yXKJM$ ¶mÔAU`*şŠ¥Ÿšos&>·[ìÇ;“®Úô„xµ¤E1&¿¬mªÀw„µy}0"EÇâôãI)«6í=ª¦÷Ö¡8÷UÜ†@h“-Xgıë§h}*÷¼ãÇÙL¶¨¤¶ÒÕ·×’òNUEÉ~Í)¨R÷rÂ>’wQ[tgÁ PˆÕNr <Ä\¥±—a'r%ï³K^ 'œéëÄ>ZXù8ëö²F««š›*+ğ¯ÙRÌqe@÷S*Sáw=ò®¦ÿ¥Y±Ô	¦|Æºi°…Ó0]ÚöIà±€ñoÀÁ“(jz‚K¼¸¼ª“%[ü¾yyY¹Ã`’'5@¨èÌ£üBy¹çäâLqÑçÏù.ÚöGşçt^ñdcùÇ»Ö¹§r©4tÜúó|3°åwÂXÈt» ¡ı¯cÜ€1îŒHxzöúş¹k2·î	õcÿäk† KI¢ğw½”Ëšß0*³LŠ}
ºm[ˆÉ3q_,œYô4‚İÒj1ş0ÜØ§ÀÕYrÁy@ms±ŠA>ùülªØÆ?&UóáJ°ìm¿»!§m_ƒ š¨c¨,ŸÆÓ¸¡+¯¸4íFƒ¤üg9pgs,S
Â×ıE:¿äÇ§ Íg—°/ÙaƒëƒMÌ#Ş%æÍâŠÖos“DàK’ej„!?‡ÒAêæ‡	¡
»|úKfÈ:3vt^ÙÂwÃÇãàé$×ËŞ…b~m‹À-Yë†]±ã|áS|ò²lÂ1´J#Ì]êµÙğ  İ _!ë    ¯!
ÿÿÿÿü«	ÂA@hPP°PJ(µœg™ùóÎäyÏ¿z½ê.ª	0N½…Ònû·É>9wËÑáğÏë õn ƒäA	½Ê?ë^³ûßj—{‚éOW>&$7…\àºÍß>’i®ã‡®œı”ÄÛ<qh-û¦zÉbyçYŞ‡‘Š"zS(Uu0‰\?§­ OŒÙ .8Š¤CAaÀXˆ%
BbP ˆ(C˜^H©W%MdhÊ“%I4•8€Û»=Å¯—¨Îí‰› İ§®|6•ãëõø}v}£O…òMeÚê´Öÿõ}[WÓºÎYùÁÿ#ø€­9gÁÏ»9ÿ3şç/9÷w[[±ˆ÷ âüS±ËØ—è8óÏ°–uy•áĞ]nã^-Ì—²¦.÷£¬õÄ¿Ä½¸º9êşú1ë¹.`úbQOHŒß ›oŞõÚHíZÀ  j !     ¯!
·ÿÿÿü“	Äp°`4
` Td„‚,d¶oïïµÍnuÏ’ñ`­UUÔâ	ıŸ©DáÓÓg¿ÛoNö÷ZïêxÂ¢köÍßY_Î-Ù£R»Íu¦_8äc>ÃÆiÔıpÚw¢|ÚÉÏúàÚÏGíÙ|pŒnf¬>Ã’u ©Œ.T=Ü.Ô¦™­©¨I¾³
«£.²s(“u!;¤µ&ªì3Æ)Šb@X0&„ƒ`¨P,…¡@™F
—š­õx½É+Y5E
¼¹.w×ÿCfÆ}v¿çÇÉgf‚ŸxôZŞ™f”î×Ó$şj?ı?T3èï>ü?—ü!ˆñshâŞˆl¿—õÅˆ ¯b‹Î ÉQ|wZë«Õa¿˜¿™£3UoeæWîÎ»Şi×¿HËÂO'lœJg$˜–S^jàı¸sİoMÃÀË}‡rp?ÑÄÑC+vg,ÖñÆäÉ`8  Š	 Û!    '     Ò	7"¿OOEKù>„Tü‰ævS6nD ¦_eDxäI8ÿ©Pğ²êL'»óª†‡m.şD¹ôÊ[Cí¶6şn(Û4‡ÊÓáÊ`2d=	"¨šİÑÀ%Ï˜¡ğ©	¼İJ³æ>i…95nş)eŞòõÆ¼
Éş¾Šµ…µ°]CqƒfR:çàY¿èÂsæË?;îp¬1±— J•€¶=¹Íç+
øãD$b(m\çW¦·DÔä3ÅPj&­ÿíçÜüµ¥Œë"’`iùµ¿2•)ú"ö}S¶ëÛ(Ç˜ÒZ¡ÕYqœˆQûõÑz¸šãvïñÍz}m×şN‡æóEvşÀÒÅ¢‚¹"@Ä”5Ğå–%é>Ì-
µQÍµ;r1!i™*[¶qèy( ¿Šïzâ[õßXb=îÃf²çƒ?H‡¥‘I&¸oçoó›(bÿ1‰4…i„ 9:jzq’ø{0ßÀM
U£=­ùÆKy;†ñ _;˜qñâ'Ïô$¥‰ÉĞF1²"0X—‡G¹é‘„lĞã>¼âR_O[Ãøõ_2ŸR['z-A™X¦Ï©/»3
%®ùŠ4¸%\j
…Æ¦%‹ãSáƒ¨’Áˆ¡­9ÑRÏ>cØñ*:¢¹Pı¼r®‰jnÏT†ò`TztŒ$ÎvŠ³ˆTÎ2úU+È@šæË¶ÿŒ|CtF¸[™•:ùÛ0ÀH1ÿØâzÑH¶È0KôsŞmQùƒü¸Ö"†÷ê…iÈ½²¹uEÖny£¦A†zK{Õ2zÍ´u‹ÖÏcR1ùìkVÂ!+RÏù¼ğ±ìU.PV³M`ÍF…7–rUí§­Ç|3vÑ&±¼¤3Ş³ÙÜ¬ì1fÏFu›=Âù*‘ßø'O°2K
»fÆ¦´ö	>Ã§‘  æ p!    ¯!
	ÿÿÿÿüš„cP`l7¢AP$!Y©ÿš‘¦j¾7*Õ)*EIS€ÿ'‡…ß-»_jIõİ_§®g4ìI'Ö(Úú Ì³:zñ~{
Íw—õó ùÈ—ëæ~6½İM/îê”¯0ïŞòImyÂ£îdì×{—Vòµ#AÀ•[äğT­Â­q:oÁ œŠ¯œ«$µD…n©Š!Ò
Å3´ÂKÄTÀ&$„`ÀXH
‚ƒP ”(2
Â!0ˆŒ"7:Ö.]¹%K7kné+oY46º]?Ûò~}İ]ry|ú&7_wú6úæ¬&ƒE%øoİn’ş›£’İÏv$8??èØšöÒYü^ã»€ñÔÛ§Bı)Ø\>dUÃ?‰‘ÅÛŠşÛ$ş³®â³GÔ¥nü·[ÁĞkz¶LşÒª¡yõ~§óCF^ï^¯ WV’ïğşºÈÄ[„Á_Ø|à  { |!+    ¯!
ÿÿÿÿü£Â€°h.ƒa(PD	ÂA,qã¯y.¤Î·çêÈ«B¥I4.òoñë§ùo©}Wõïîôì¡ó{%«õÚuÿƒp ª×¤ÆŸ"{îï¸şYh9íÃXD ¡_ÖÃ0*_ä–î2%%›uêç”¡W‡Ÿa³£ŸÌèV±ßBÍ&†?aŒH\±,"ÈßË* ¤¯;$© ëk®VÈR¤ãDà¤æ7Ö@%Î"l€ˆ`ÁX02	BÁp H.J„Ha ˜˜¯¯·[é»‰/Ÿo¬ûoR¥Kös½nAùço§Ø~Ìš|¼û5ö¥®ş{»oÇ/-ÕS™h.ÚÕ¿¥tİïÅoåÀO›Á¼)7†çÀW¤SíŸy´eOén¤ã.Í.¤c™8ß•İâF`N?*V¾Ûº.–<ö•©ÖgÙ·ÆMmš£RÄ{Zr¢H¾XÊ1Û¶HùÔEá˜&OÉPœ	ÿ_êRø‡I  ‡	 !-    '  }  
ıAš	%úÖL)ÿp´æ ,Ù^ËtUƒËµeÜ’w1w2	§z¤ÓÑ«ÈP£¾*M|¬¤ÊÛ
!0JPºK“tÎ¶:  PmŞ†Âo}O …¼»ˆˆ—Ÿõ¸:0B|†åÖœ#VêãP:dkwÁD[¢¶]-Êo­—AWŞ„‘øxµ lj­_{‹®†=ú‡87Š^ıZ™f½:´ÃÌ¿3Eû­_ñF–`3çô½ñ`ú7[«#ÛäµòCºÒ@ßÒà³~ë50FF#ÊÙì¦¼‹ò+EvÏçÌÓÜ¹ì}ëª“òbH8£äÿ\²ãÖ‡· ìü&âq›æofÇäœëÇ÷ˆl¹©†ŸUíAøÒ™ÊVóFÙ——ºØ{°ÀCqØZF ¥ëeücÈˆ_-<X„§ÍÍ\[–ujÌÈ‡7@yuØJá(€®‚Ëë:ËuùX×ªŞ·ìG~¾±Y%<bÚÔ£],Oİ·Ô·|ãW¼tsÁDûP$5Iúk¦í¼é
lÿÅ.xÈGĞ—)£èÎãwG¹˜¨yŠŞy}^z n!şXèM<°_W…Á%‘b»f’8Z	HŠ'»©YX0A\Ê8ú‘ªv#ïÔ ;ĞĞh³ÖÖ†Ïò\ïï×åt	HNèuacò—•)SÔ#øØ-rÉ¿shb½Kô÷n$ÎµçŒº_aŒ­€¥ÍöÎgî6û6ãyÏëÓƒ-Öšv
ª‘6˜äEÕ¾ƒ@…½yj}*ÕÏ³X¤ ou@i*†®Bº§äŒ XÖFm©–PUæàÔ»F †¬™Õ«lMÜIF+@½y–*ñšÒ(Ù•€‚ÈÆ8ŠÎ÷QÊxü£zİ«Ü~ê®Æ~˜FWBÁ»Ê9‹Éö8œ¦ë /şš6m4-Ã° \èş×iÛ‚Õ´ı%¦cAù»şş}Ïï§µ/Ù|ıºiŠ>š(ñ‘7Å3ØS‡U,#ÙÆ+„º§3{á™*Vù&Ï;ÓÈıYG¡•§X N6É-8á!àúÂu[>r}®"ìqvEò+@†Úò%5ÿ&È€‰‹Š,§8à#ĞaI	2{5¢ì#‹äßU»[¢ Åg‰©¡OC–¡
SÄ@âü¶¨” ‹¿"íx†ªšë&šÉ½6X%©E‹jß¥)Kd¬Ş[­’İúÏã8Ì&ëè‰…6SlË,Ò¾'&gFxOû2œ¢ÄQ?)¸¸Pf~|–¦CZL7ª­Ì.:!6CRÅÅœŠŸDgÓï¼o[ùS7GÎ±%(şY¼J»)Îa®‡ô¹¸ûıs'¿™ğèSØ\*ßŒÀ-+*Ä·¹?£	Ù}‹ºvv@`\;wĞ³…‡åİùt%<öÌ9-t~¨W1Ojl*ÚãÀ®ØND$ËbÊm!	éÀ<áÈ|Š”Ùã×(ù ç òĞÂUOB†êì=€ü­£ \†¡Vª;¼T›© –”¦0‰vO®¼¸8çŞ°ğ9¦æËe‹rJï	–šØ1•âä¾zZiwxºWƒñ‘LéTºÀP…\«0 ÖÇ$L<o2Ke¨mÖ¶9¼®$Cg»«z”PgqOÒdw"ù¤ç†"æ0BÜLe¿ªÓéNTÒò#.)±ÍØ,uĞ€ï¨_KtŞ³8™Ÿ:úGNÎñn{`&qW‹®àÃÙQQøßî™%ÍÏF´çÍÕ±)‹@–åtCæÅ·7ñæ€B6„•P&ÇŸŠÈ’?!CKB81T3ßˆ"Æ÷>”h.—¨K±A¼¿†§Ì7ş#EE½ø"4xò}
«nêÄ¡ÊÜ›yY„Píqí‡;PÇ?0üUùR—rm«¤>gP27L5Ñ½¹¿µíú}Luºõp:©=ÚHÄ¬áèã){ìÑ‹”å{*K'jÓK3ãO‚‘›Qº${Îp’LV :›N·‰-¸’¹üËóöõ‚.!)¤—YMÿ6ÀA0öú9ŒK6ıhmÜîd›¤Ã]a”WÙ´œ^át¨?—Ô E B¾‹Æb³›È¸¸kƒëB;ŒèXA9lÊûùr®µ¯·U˜¢?è¾>‹ÕÏfş`g~qJÿ±À¾Ír˜¤"Ä$p êzc“/~ Sô3¾•‚é'5³¯å~÷RV%5ÖQê¥¡Sú¦š± fN%âµ
T&ü!P(u¤4rÖN¸ã<÷{PUH+'ô( 2,³(Uöå“ãqë XgùNUe½	êˆ±oŞcEs”â,,Áç»Q¢WÆÄU-øº‰†ì gçn¸éÍ®w²ô› Ó•gXÕäÌ‡€›wc`;	fµ ×úÒ-pÍ9‰ØkT\¦"ùÍ€5£Ô??G Çüq8J~îM]Ø;İaæ€ôzæñÿe¢¿”í7á®”ˆ
Y~Ø‹{0ºÌ6ddû£#È—àkÙuVõ/EûWÉ¶ç(@
Ø&é	AÀb´`æˆÁqğ)›qÌ1¦*eeZ¿‚¿-Iƒ‰ÿ?ÂÖ\L£‡Û}¦ûr¬u³ıv!h€5+sö$ÅÈô'X(Ş^ÊÕ'dı£…åãüJ–Æ6VûZ×&¦WáO‹R-VŞUU&W¯ê¨–ÆÚŞ‘i/X(1šZX?r¿‚¨0N'»*,Q‘dêDUŸHÏ«p0?ú¡LÛv…vË[À	øScPû®‚Ñ”]KÖ2ÙQ/P›VĞg#|‘¤zß®€'§»Ğ³“K¥†CüŒ×­ Ÿ­i–äå '</»íÈ«ñ~ªÒ´JùÁğÀÉå	eíìÉ_Àİ€ól|qLUæÈ»ÿd†üaÏ³µ%îç–W(0’ŞX™§&ú_×—ceâío B=-‡ÃˆuõõD+T›¡ær_©˜´?¹YZO'şm&|¼Î!SV#WS!Û”¿ë$ å—Õñ6EX[Î#‰îŒ9wé#2<Éb²ñö#¨—$5rj|nçM®-Ø({¹P] ÆºD¬“x¶×ÚCc/ZÁÆı¨Ìj«S¬¹µ~‘Ÿ
ˆ*R:ŠÁ•Íªn}DŸ•»iíÒ
†oRô'·Pö2Ëé	gˆ@­İB /Yÿ¶²‘U)háPk¼É·7—WÃ:³…­‘e•{ïÁÅ«¼‡ÀÆ¿ª‡¨49ËIËú'êMÊ¸ål<3t…¯å¤*è@$×¿u±İ™´†‡%ØŠc?&Ä,ÌW«¿!x-htä)Ãª85€ğùeÊæº‡/¶¦›;E%û½Ë²Šwóc<FtÆ4x(¥‘[[Óû-~ÊvÍÔB«K¿=ô‹wôB,0¶F.Ãä«^EŸ"ëbŒ¤IˆöËÅ<¸j®LÅ‹mMşº:ñ¥Æ1ú”J‚b_Ò“óÁ¨˜ÿvÂı´~iT3=e`µ•éG´¶9ÇAHŒøÎàU³-ÈÎ¥‘hÌX…ÄlgÁµä³‘5¿ãT’z6U$Œ( šYÓË¶Ìz“`øè®z_*]*—Y…û{åô9¦¨›µ‘3@$`¿âzäà[ş‹·(£]WÂÈW3şJ-´å7úbıÑëTH#À   u!@    ¯!
ÿÿÿÿü›Ä€Ğ`2…‚á` TH		B,eê¸ù¼İÆ²¸¯5×‹JB]Uâï@~ı’é“©ÿ}/g³Õ½û°½È)Ã/&|?œuó]ó~€ªÈı5Wzî¼"5IæíïòNz‚|×a’9ˆâé|=Ü¶r_FèéKÏHg¿{Q?2'vU˜„)èİBqÃd²Æ„‚ÛL%e8#§ FÑª‰’‘j‰©j=`”Â&Á€°,$ƒ`¸P.	A@°Pæ1…B®2óZâ}¢¿oí÷º÷‹©S^[TÀÃ¬¹ùü><$ûü}ŞOëŞ¡<•TQò»œµŸ±¤õİ8êïó)~Uæóº9åãÇ§¹øƒÿ{â¶»‰²pğ*ş—Æ™Öß>­®@ŠèA&q¥ôOµnbô1.$\O§ñZ±w›h“¸èö7–8•åŠ,6díîÚüf¤ù‘	@­JİŸ€)ºp®4û¾ñ¿ì‡d×º€  € e!U    ¯!
ÿÿÿÿü£…†bP`l‚„!E‹”¬“Æ©æxã?²¯$½Å]kè;¿g>û$áû]#®mëëR=u`¥üÇ‡öN6Ë ½µÚ9z<é´iö !³õüè¯­["$iı{}q—íôiÏòëº{â2òH¬ÉrËy¡©åÖnywb­°•¼¾³¬@}¬˜ªH)œÎ’ÜMkX€Ô¸D°¨0ˆ¡` ”(a €THU	Â&0ˆMùçUeï/\êş¸ı·Iš©ğŞS:/Ïõ¿MÈÿ}Ï—Şÿ|—uz©éS3ısËªÏüWìW¾[À¾€Ï¥¿d¼?ØúšV¯§`¬ßĞ—éÀ‹ï¯9ìÉ[æMG.­3_ßKkòĞÂ>+gEû`b6lŸú8ï¶e/ÿS8IvE‘
ö¼P6Á22ÑŒËñS¬OO‹Ë<ÜÀ  p	 ñ!W    '     è
7"¿Æ{ğ<cÿCMc;×ŒDšƒÒ&«Œ4¸9Ô³Ú¹CõéFytæ…>ƒİÁ!Kºì‡>„CS:vˆõ¬ÿ¡¹Q6»Í|¹_0»<÷Öˆ¤—b£vR}xBtd|®)E²7° u¿*0À“ÄI¨²#ì8Ï¦ÇªšG‹ÓÀoS T|´“¬ğ©Èz¦>ú8<@x7u7Ò 3ú‚hD¥ü°âL^ÑŸFœı¿Şµ¶Gt†ÔöÀj5msë eÒü7&¤nº]H(å³@IŸ•¢Y“Há.Õ|uóæÎşë‹ŸñYA:Éˆ§ğ°H˜>	œ{½ı>»èŞYz(9Ä?¹ÌXc>¬Üc&v^ZÌk#vOf¨rC¹5—İì]Rüx¬Ïİû~>,Ÿ~¿ıWg†TµH
ëıñ#’Oüa÷˜‚½s“ÎwÈ¤
şè8èf~®ÓqwZÏI&QÔĞ,Ï¢=i^iÓ«5¾Ÿı.ÀkÑ_â°¨±2İàZGD•oŞı„Q5+ùÍŸÕsZÖOpúZ„œÇ´1ónoÆ¸¯šÿ[n…Mj[S=ÕÑÿ½ûÖ°äˆªgòçİí%É]KvUåÇ¿u7kï‚®Â¤©‚9cº†K çLüÚ Dlá!Ê]cŒ	 ±Tf¸/í.ßÍåø.ï}ßşôì=umÜ¼L2,àvP ¢L+”sìƒ-’|êÛ)«Z9“áNÓæÛ\|BÖ.Hü Ó•Aê°²”26|zw‰[_æJ)ÈçJú¦j®ª!UA RK|á6l™ MgEŞúÿí"¤™q:ìb;‚.Ñëz¥˜„Rë¡î¨}hrKÂÒª:ñ.Pœ} ãş­®‹2Û \<˜Úu,«xı4,&dsÔ'2Âù=ØªóĞşô¸)†ã íûMjÁg,ukÒ‹gÆ¹ŠGb/—XÎ_  ü h!k    ¯!
ÿÿÿÿü«BĞ`L…„`¨H(" ¬Â4ßÎ.ºœÛÌË«Ë¨]L„ŸAú¶İá&Ë7/[_­ÿÂ=;’îè¥~g‹§ÑKºV¡å¡ù¿¿_R©¯Ø:'ÕFBíŸeÚãe?›à5ÛP´¿QSªj…ó¸†g±T*FÒQõGÄÕ»>åï¢â¦£ˆkº0©H7´J•‚¢Á¢É5ÄTÈp ˆ(	„‚a €T(%
Â¢!D&!.¤öõ.«¯Ä©ü|qÓôÚE*qTËòl¹¿ßá±ø÷ú»ù~¾¥Ë¯Ï-¹Sğîí^¿ÒbMÌ¼›ásÇè›sQÇã6"7ªòøÎÃUÒŞ	P~‘¤'íæ¢§‡VUı¿’Ò¤Ï›ßñ¾¢Ì;EÙ¾js4ø*&IR=ÛçR>ÛÀÃÕŸV¾(|´¶ü­E }û ñgïæO×âY/ 8  s z!€    ¯!
ÿÿÿÿü“Á@°`,
CApĞ`.Âƒ ˜H"Ö×UWÇ½Óê=³|EB*ê¢ôÿ-õSëøzöA¸ÿş¡u5·—õ6¯2;îgQtğ‰]¥G{J'- ‡³7.}ı#%¥ïø±T^Åh„úœ•?˜)«¡óË8©ùï‹‚·I£eEÁ©Ma¤š±€a¨Â^åZœ ‘XHFéK 	Ü"`,p°P*
BÁ  L*2„ÄAŒ"î¼î—nunsñÇ{Í¤Ç‹ªëÈ—Õû›9zÒ¿tš<z»>urêÇúŒn•÷sô¢/ä6~¾ß@ğù^£®>ÑHÀgÿŞÑ@º{\îóİŞ¤ÀıíœtjU¤Îu¡ÿfY 'ş`ÒŒ¿tA]@ÑŒ~®Éz@6ÑÅcC.Ø™-ıİÅ»m›«vMÂ•{hêáø«(A$'æÛxĞ—H¯O¸ÁI˜„Øô´2 ?;²&í0à  …	 Ä!    '     »
·"¿{xt…ß i‹¤F÷FõÅT‘æõ¼¼ÖTÕ={bUÿz80ú¿mI—K¹Æ¾ÑÎù]ñ}•ë•FîÄC{ÁÏF%—­ØæS1*/®ë)aØòEÊ†m:ê(z£ÒòŸ^²)êO’³8^²¼÷Ä3ù¼Éğq äÂNW|c›AÈâë˜Ø¨µß±––sÊ¿D!©£«™¢ÆØ2=‚@DcÍ², ’(ü-¡‡Ç’bÏ—ƒA~aú—"D¾ŞÅRxİù=ºP}ºöİ4Àz™†•)OD*e~²Ë×-±$efğ`ÔıÉê­3Ö„ŞtéHYëşU‘6İ2ˆÜ…š½²²T¥Ù%òYk*‚òö«í²èÑ@ZYš‘4Î—Ø øëšìnÄŞr­~ì•ì.Kşv9SÍ•,_–Ï“G”h!zğ¡ƒé_ªq¬ŞN…±ˆÖHÄzÂâYM?§^ëŠ(Ñÿ_XÛd…s5_ÙyÒ°(~ˆ§;ä€h¬«§M5Œ/ı¾u:}±Ó¡L"p¬tßQY™^0$¯€1Ğt>–%3ÉÉ¬°#úÆ„§˜i\–ÔÆ]%Ş**â#;¿Ï•`¥.‹Útş— )¼( }©£õ›¾r£Uãü†±µÓqÔz,ğÇ™U¯ B<ÙÆöexG/~pô6ÿ¶£ˆA‡ïoÒ³HÇ?44¨ûs¬©3¿ó‘“srCÙ¼¦¸Æï‹
Š™s´R)}VDvé..ëF—2
°¬õ•œ¿Øıwº,~Ã…nAqÍÒ–¶·Fq›kE¡26fm,„&9¹_eê4$Š£ÀQ*??äcrô!àb¬íNÏèñ¥%~êSÊ–ì±Î®¹êø]´DÌîQr?nÆBfJĞ˜;Ì8  Ï z!•    ¯!
¿ÿÿûü³Á Àd4…ƒ` ÔH¹ç¿kù­okn'UKBUHË”×CŸ£]L¼”š9áğïAë»ÄÊçÜş
QÜaÀ›Ğ£‚?İ©/öˆú Ö{Ì\Ñ“ô~Óí7*Ó6¯>ïÔ£&èöîæ­I>HR_î[Ôş´mV»Z0õ1éKêÄ7DªòÔ5cE9–Xİ‚|”ÕÉ«0¼ ‡‚°”,Â@¨P,D„`¨Pj
„ÂB0ˆœÅu^{™ª©¬Ë»¿7ª˜ªøxšë•ŸöèçÔi­¸Xøz¸¾‰6ÿòğ¿ÀNdõ_4Æ#NŠşCûß§´âŸ•³;´ }ş¢;iÜÆï#ÛØD~"î¼5gÄ`‹—tğ5ş.uËYXN…D0q<Uî™•÷Ó¦~r«‹{ü0KÁmàõjş”Â„(uo£P†¿üĞ¿¤@²@Úÿ¥Tá;ê-¡Ë‚l7AÛôø‚·eÎ  …	 
²!ª    '  }  
©Aš
¥úÖL)ÿ“S 
%ô¬ÂÂÃŒ3±ÈnşÖ«‘ìØÃ©ÆËí­wx:ÈO¾¯Ü,äT³ø¦:Õo†/_ÁŠ²@×NfT=<„~ÛàæˆÚØ Ø]ê:‚1áqšq&–0Á˜şèîpPyˆ¤U…@IÄeñ½fvˆ»ÜºÕVÑ‰Í•‹íÏãG¼OŸíÔv6ğw;#ºNIgû;óãı4±{)Ÿ¶˜ó@:ñÒåë\w&Ë-œv¯¯¥œ!BõÙ°²DZ/?Ò“Íráğq<Üë…{_ÎÕõEØXZìüKú<rú£ï
'¾é!íÙ÷äËÕrBq !($qšeøËàåXh}0ø)àÈ# ˆR¸bd6İW|ùŠ<vÄ#P‘“ï2)ˆ#jŠGqÌgB¸d´Ã˜ÉCÕŸ°•R¹FašÈsUœÃ.Ø³´; £×pQ¾ş¢³8íaVP±Q.¼,L†èşÿráĞÍ‚
¹$be8HĞ¦Ô„™¿1ä*“;Úc,2 pg<é/ÎÃB!“§ìVğ½½\¥>ĞˆlÙki•ÓÂ ?2EÿB9í·"ô´ñõy LsR
\ö­ßäç<½zfÿÄçÒ.“lø 1·TxÎj‰šÚ!­Ã»÷ö~µßg5ªiªal•@“ĞõVÎ7¶`p=^$Í;q¨Ñ?^”İ4B›n8Ç·"²Á¢µé¶™7H–-ap˜³ì#îp“ÖŞ±Ævàû­iåø’ía+Ô‹5¼s-µp6”£‚²³'Ú$3O Ô¢âöÿu¡<“<o/ÔQ àòu€½²WÅ¼ILsâ6GNí"<`ş‹©!ÀBLY„Ïê›ÊPĞ"–ú@6%XXrFIW]‹õÏ0}ZÌVŠúş<˜Á.%¿S&­™Â¡ü©¬éğ«pdÛˆUö½­Ç®õVÕÀP¸JüÅ]!ëÛ9Ş8]C/#Vt4EcG€à;2ëà¾‡Ûe-y>7DË<ïâ)ı0â U‚¹0	w¤È¬ÚüÜ€aÚXh%éÌÄ5¥ZGÚùİ‘G”’ö=òîg
â[/iŠû”ÊŠn\PÀºûx’ö»U;ÅÉj=¯%4†FíÒÒS¯N`œM/%e[z”ÄîßG™göNÂç>uŠŞ­#‚ğÌÈïl×ÊLÆ÷óÍĞ,şå4ñ[ôp¼R¹µLcÚJ½…‰MÅbÎ¡­î@ù½ñ¿cÉëêkNâ_B%V³(èwKAçŞRb“<
Û‘_2Òú´Ë{.ËCÊÚƒş¦ê	³]«7ıL%‰ï/œ-ûº½¤ æ(ò»xÚÆ‡³8Ï£û$*@ç7ÒìÏ¢ê”véÄ£ÇQ&™hâ
ñ1Ù´Ó!KÇïüôQ>†¿—ÙİÎ-MœŠ+RÊBr;D¥Gp$ößÂf"ßù­¾âŒı7ÀÌœÀÊ/ôrâ…ı“$	~idÂ3V»‘Ë,7càÈ
×šç"£ÙeâA(8RZ‰Şéî0Dà~ÿ—Ê1ü`Ùd„á	eóR‡Şã»Óä£§Ü”fåæV—¤·Ra›+o&#lCLX­	–·€\üÙÍoPŸuÁz;OŞ)P¶ìİøøC ®ÚÊ­š94fXoyŞ=tÕŠã ÒMüDp±.öÚ«å×ÜWŒ²ái…¯qª2ÿò‡8–İù°(ç,ŒÄsO(X9ö`PÅ~°ìL¯¡ Öëô½XÃâ„òÿ&±ÿGÍÿ%‘'²pœ°‹Éî""eƒwŞØÇ”Óa½»T§^Ì‘şO²¤è×ÌŒd³UÎÕ#k]_÷È!5¡³_Î½ÍÃùÓ˜²^IMwh,¨6©¡SîL¯Xkòêöì&„¸Ğóä²Óì¥·‡$òÊD,;Yói®9Y¡|ˆW^ûZÅz#{ÓÈß°!óÜ)ÍSé-Å>¤¸¬_,©§/¯°ázÑğºhu@V pŞi2„äŸy¡
yÀü%)Öi´æ²UÇCT¡èXšêÔ^`¶·EA^›»Nh£çØ¾©ZÌ¥°¬ÛÏ}%I5;RälP?~%•-£¯QV-Ù£wÎ¤œ€\k&©EÖî ÷ÂIÌö+Ğæ§èÿšî½å#h)zŸ°t+¥†%ª[½mÚ×¾X9I¨¸* ˜O³o3şÎEbÄK5´VH…{¦?NíR;ÅOjc±«¼Òûë ì`Mµ=£Ø~<×.)âÅ'½0)à'^ÊLÂú‡?§#ZXœèSºg¥¹ç%ğj,ªI›G•×‘Ç&Án‘Z˜²<}(í\A¥şĞÆÀqÒI—>ÃpMİZrYŒsÎG Ó õárX19“§éö@t7œ"¸Í¯—°e³° `ŠDó‰*²82° <½é%0Í³'Õá–ä©@B¹Ö;W¬¨ËŠR•i:cÜã¦…	~lB–n=*¡–Œ–˜9µÜîñœ${ÜİnP–m,‡z§$ªJ°ŞOCüNf]‹#¶,\o"eTİ$]Uşà´¾B ×óyŒÛ_æÏ¾nØ½F@İÆÃD/åÖÀ5¾ıÙºöİ:Çd'`¦Sè2u(M'¼5?u‚¾ÌZh­Ï-C½…Ñ”6ÖÜàJD®Ti=÷'­×ª'¯pÿ•Àø.î;G`ôã^¯íñıWj…ç´I¸fÉyŞÏğãnÌ2j$F®éb©©<‘;¢¶ÇúWñÔ şİdÅ”¤QtMŸrKaîQAÚ±yQ]½†
'’…<œ‚&RóCÇğ9àûX Íò´À²öì²áğ£;›Zëû3Œ>2s¸ÒÂ‹-€¾˜TRI3Ë-ÜgÅZÍÚ!=jè“o6MI·}DJZ²6KXªj|Ü²¥»À£¡Ä‹•‰÷¶ÅÔ	VElNğõd¸ ×‚â-‚g×Öè€ª]ø]Êœ\0ø”PÄë-Vh›ƒˆ„'WÃVë zƒ¢Œ"ª$`ß]œ{øŞ²ÆT7Eú=üëÌ°‡p•o¨˜£Róğ)[ÙĞü©d|½ —‰LY¬”aÒ­šm‡ÎäU(ƒhƒĞvÿSâä»+ÂS‰®&[·àK×ş·‹}àÁ|àtŞÉB«éÂÀdÙçû6oP†¯¤ì¬ıfx
Cî¹E ¾ä¢_§ı$Íx=udÓOwt³L¾ŒôS¸Ï¯eú5‰Ù­b)ïŠèÍ¸¹S#ˆSŠÇ˜=n¨¯ë”şşğ Ô«>ğª¶ŠàFÂ«ë¨Cş€ÜáNío^ 0M odÉ*%‡Ó@®ÔÇîãÀ
ûuâ0ÜÒQt²]?µ,Ş}FÅØ¶,CªÂïo‹> ÈûmkÀé35ª÷eokIr×1Æ`$§…^^éuGfyäèæÿ"}§ú¹4Ç’)uÛB¹ŸÈ"oªYÚı í×²GğëÛm°½¿Cc‡ uje¶0ÏtÏ”-[æÄ·¸ïPMµŒÜš&»I‚È%¯Àœ%Õ~¶º“OÑ‡9  
½ t!«    ¯!
ÿÿÿÿü«
Ã@° 4‚á` ”(2 ±v­êomf©¬öÉ%Ö·©´dëBï®ìåõ­X÷| ½z¶Ö…
ÿ‘oŸjê|ôËé)¹¿‡Â?UUûP’@û¼IGöÚ¾¹ôfjY>›×;=şËÑîsG ßÁ›ÿBŞE R°Œû¨’»óêÇkâ,UÆÚf–PÖ˜åãZ«é NÚqJÔ*JsE—<@EÁ°‚¡a ”(%Â¢0œ"×~yÓ*åMnë8k)r…döŞUõĞ³÷·ı^~¾~ßŸVş|zºuæ›O²¯ã!gíº:?àÛÍ)ı½ Óf©•kòõ2Ot¿„†~ÅÍ	©õ{õş–­¤>•ëüQËÀo¢E£ïÌ[òn9]Õ~ä¿í½L:x^½‡.€Ïí¼k|­G°öıO¥ãcşèÍ¬‚İ¬ƒ¾ãé9èµ¹>Ç•oØñø|Ø ÌWC€   d!À    ¯!
ÿÿÿÿü£"Á±d1THÅî—nJóRD®7|ÏË÷—V¨“võï/§é-]kÉêcãÿÁSEQã° rOêt—âû-bóaõ†®‘ŠW„*Q­'øïùÅÍóXUÿ<(f™Pà&•ã¿ñ%´›ÕôAÚCyÑÍˆ©5µÛ,º0J)6•f°‚)Úğ+À˜;Ã@°P.B0 ÈH„Db²]k3Y%yÆ[Šôn<Í’{
Ç§Ñ¨Òpá/gŞˆ|ß÷g¿Ux{:uİİÛ¶yşŒâ5G
ê”zÿ„3çTonÏ³/ŠxR +ùgz& şØôó€í8Éş«Ó/b\1çÑ¤ktüåt›Õ4ñ%ô»Õ“È]fİSãÉ’X ËŒ'÷¬2ÃÃ–X0jy´SşX¼äbê¸8  o	 Y!Ô    '     P·"¿Xµ+ÄğÌ}§¶q8Ÿê‚m)$F×7õŸÀŞíàÚax	IÍÂĞ¯dğ*_İœG£Ú3óª)L^ÄÒ¥YìH#¸$u·ôË_ĞË£¼lúı¥õ2ìgM,şF¥Œ\ûê?Mø(åœW‡Ÿû’S¸úÏ°Q¼TXŒ×÷›7»ÇÆM£?½‚ÓY$Fí_’òĞ†¯^ğt“„íä£§«÷`vÈ_à+¢UQ]áûğ+’ÏV}
N3ÄTƒàBHÌ,5ŞB~`P0*!ÄÇ¤Š c˜\ş–wÊreØ­tĞ¨ï`'ÓNqx¼şĞ˜ß·¯¶ÁjD°B¯ò³
ÚÛ0Jør*qbZÖuZ±)!˜^Ç|F œ#¥NàÅs‡çÅƒ|PŸéö‡Ãúm°Càtûb6Y6¢Á.ÑıBê]Ì–¡&}N¥ó7Ú`We±¤Ãâ‚;;Êª†oæ²ù£#^9p=€ Vğ’[o­AÀ-}ŞáøE™t²Tü~\lš:j|2Hˆ“„Ì<ñS†0–‡Ñ!M'¥lmÉGÿˆJj0ëàPDéş²=ıÖa:LUw‘kV•Üå$»FŠSéë™Mó°ûíÄ¼OáÌğùÍL‚“˜Ú @ÑrfĞ¹N~XöÉ¦÷¡÷oF½2IB Kd½¹kõÏ©OëÊVş‹æ®KÒ×çòFµ9©Ï°à‡ÀEı¾µJjÊÃVôÈŒYA  d t!Õ    ¯!
ÿÿÿÿü“a@h0Á TH
‚! ‹ZÆü×+Íd“ª«ãq©ˆ“¡×‡W“/yé£ùtºkÇ—§A ¦tT!á ïx_-UšD‡ß}
ã·Òï„í«A­8€Ùı¿Y‚'îù(rO÷j)=„±¹EË„Ø½ï‡İ pî2R0—Ì²¤»Ô–[½lYA‡/¾PeS!%o¦îi¤nL"`Œ	Á€°Ü(…B‚ ¢"ŒÂ!qâæú¾o"ë]õ/6«T©uuĞKgª¥ÛÕ~3½¸är¸R}şíõ¼0ûJ=øÚLéÿOÓTY«O9ãş¿ø®Ÿ_Ò{<¯²@ù…ö¾¾óóáö-Ö1Ät²şö'×økNv=-Ÿç®y|ĞŞ‡æ%Vµå›Î]¹‹m[´jƒñ ­UÈQø–Ä¹ SòĞùÿ^i$²¢Ë$Ä-‡üBDÀ   ~!ë    ¯!
ÿÿÿÿüƒÃ Àh,D…á` ˆ(„‚&0‰qÏõYŠâ¥8•-"ê¤Åk#ØæßÏ|nåôªízÇçqîoºü¢9ñ"îUE±é~;å_O…Eô†ø×óƒÿoyÖr8^…õyÅ†D0lmMí±øªYœ²NO+:†ÓëJ¹Í‰òYÅöª`áIt£ç4Kü£m„¤µé°Ë
Ö#ÚaUkZQ%tÕ‰-0|›€ìvƒaÀ˜P
DÃP X(R
Â¢€LmÍou¾7­ê¼óç™—2UBœqngóm3§ÛqiÿÜäöu{¿Í“xÓ-­…£7rõMÙ#:wúv|ƒYÿ>9€×9üº9µV…¼DÔnïeCÏÂè7¾MÅPRSu85w/¥y~ä ŸKé/n–ùHiŸõŠ½8“Ám{Mz¦¼Ëûo`µ01oéDw¼÷Æ ÏÇØ ,
W” ~GGÆóüU}Àà  ‰	 >!ş    '     57"¿h§mm¶{"Ÿ§Æ€ì§ô£!óK>ø	ˆ_ygİo¨4;Ù”rC«•Şi•è… ç
ÍıÙ<q4İâORı`RD	Ü­Ğqï¯tİ½Œ`Nâ'\Î{®×•HìÓ"JÄş˜‘~6[Ä±y	ƒÛz°Öğá:v
ofò’öÚNŸ»¡ŠM=v@0,S‰ì|×GD‡÷Í–ê‡à+Æ-¾ÎZİ"(µfÜ¡¶6Šjíq¢¹ -ğ¢£Û¾1 ¥èé~¼b)ù—ÚÙµBs[òWMi9.×í«ğM7¨,Áaî¦ò×û†]lšaZ,B·†wø.ÿ¥o]Tu¶ƒ«›ÓîF=ãkÎbÊÌzg!UÎ³iv”ƒú5¢“Ëäå±*67u]Ú_´F½Y#éÕ—„{]g”Áh¨É73_PØb#½hähÔÍÃ³Ÿ¼ •KbpˆäÜ‹Îà‚ò{XøïR3Lş¨à?®-/-ŞqaáxJ{,ç;,UûìãUTŒM‘ptAğg4½kdÈ/o­q´	g‘6Ò{a™0Í¹ÆÅ‹`Ë³1Şg§bí/Ã›cJE¤£¬õñWië'pyúô8_Öõ¡äíè$‚ì?;0vGd!¢Ü–¥¤°c'—Š 
7ïË‡
åMT9F¯1÷·ó¾v¬®H»q™‘4¾wùÄ¢õ+ËÄ–~ÆpÍ×wkS>/–£“ÜãZMÚ÷]A  I i!     ¯!
ßÿÿÿô£Æ€°h,á`¸T(´Â™í¼_i­ùæJòçTZ…UD{¿})ºù÷Öÿœ8É³lıRüÙ¹§ä¦ë©;ğÆñE`üŸŞVİÎáèDˆÇÑÍõ8j*Höù>ñ"—Gw£E¥©¡¯ï>¨×ëì)Ÿø»Ôÿ\.-™Ê—[²7Û}ãÇƒV3wx¤NšÄi
Ä7
ÊT›bÆ¹
Şp\¼ZÇnwB*Á±à,4!…¡D	T&%qJÎ7¢N<:ÍJªT	æJe‡ü¹ìmî‰‰=m_×ñŸ“²ÿO›ßº¤›oòãÛˆ TÌ}¥_®Y¾QÿÎ§6áÿåMª’òí—Jô§ƒÿé™€âuùe]ñÀ•ÿŸxnâönX«»`6=Ä©ÃÂÒ÷RİmÂ™ó?A¸DG.ˆ}N¤f-›–‚U[¾„´Òdx@ìÄg‰ÑD ˜ñî½7~ÿLŒ€  t n!    ¯!
ÿÿÿü«	Â€°`”	áA8X*
†,\×7ßÕë-œgÆëŠ¸«ÊÕTË¦¼¾oe_ş„–î+Gµy‹¨.ûì&V™AìæLßÓÖL—ÿ]R?ã„ıêô½ıu¾½îr@¾
ÍO$¦U.ÎÛì¨«¿–€WTˆ‘VE3™_(Ô‹ue8Ät²ö’ÖÙBÎ‚í_Ó™˜­¬@5%ïÒË„TÂÅA0PL$D…! H((„Âßë[ó¯wT•{ëuÕUERòym|hWôµ×:y~NÆ/¬óô÷ï³Û³ùûË¿ı‡ëûç@¢o€x’ÿ7Gv¢pcğİø—Ö–üåŸÓÛ0·»gËŞú×ÁGåµ^©S=KÆõ%1'fŸîİ‹ìxÍİv#»À½±‘3Mğ–gm8YßHz<Gm³wÿ: Ê;Üä¦ş¤ATÆ¡  y	 	›!'    '  ~  	’Aš%úÖL)ÿ“S KÂ
b$,ŠjäË.'Ëˆe­lKU!°C¯¶"æ+úªw€ Ñ—R•gZ§jg\®~H1ö4	Ã`Ü‰ å0Îñ!RÅ& **»aş­tÁJÙğÖ‹CDÒöFØù¦èÔq/€65-¼Š•ÔÒ¹ˆn»f«\m]rß¦¿i#7$ˆHè£;¢,<w§’ètU/*}®·r–Š3,zÎ)Ä%<<v\D'Êjr¡šÍ®Vôo¡•_C9¨î£lç:Š´GFp(°ªÑbòÇäš’ƒ5&`à–ãGM})X¼Ÿê[«Y4y”9\çE–u—°™/4ï­L§½€êJ…"{m/Ü†›™1ç'í039·øë­B/“ä†•ûÁîSRÈN«mëí‚fºïT¦OŸDŸõ!^à|QÙ&ÎšÍı_r!Íâ»èu[CBÚë¬99ÜDUÓbr6Û.œõ«óEz¼ šrÍô¼·/©Fõ–×úØß¾Äª²½^¬w¡`	\â	G?#+?qè³‡ñHPˆã~±K×¶
Y'%1ÂG°šSÄÀ…©¸<g£]ÂÄºèÇ$tf$=’šscÌæİıäníÅ¨('
¡iÚP•W”±“ú0œ"Í.Ş(•|îÙOú'ŸvéV%Eìœ7M£ÁsÏ^¼NÈê½«_ ê¥ıõ=8@×J«C÷yÛ€‹Bûóş' í¬J&¨@İ¥n°Ç)“××²•ÍˆÂ·»ÿFFÔBÎõÑÎ“"µÓÌù¡µ³µ„)«Ó3TP†ì&Ìks4U'å:
-8ÕøQ=ÿÏäç¹Ò_(‡Æ—Æì)ä\}!sÂß\ı®ı’|=[­æÜOö”/‘uG%ˆ1X
Fè“~ğ(‡´{Y¡hD1•ûN1¬³ƒ¨q˜îª,xA,38KMà—G‘A»ì²WxCœ@R²ƒ°ğ;õOIC1}Z³ıâ4{O®äøá™rÏ‚r¼¯Ç+”]¾ K/îà €¬{ÿ6ú+…uÜÕæd!’€z)æt?ÆóÓº‘zÇ1»ãòsw©7›[ìE1ˆÔQ]ø
²¶Ò×$ÛÒAÆõ
Ş0sÕÂsNşœ§™ğU ¼ĞÄè'ZªVi±.œÀUãÄÿ—,b@³c«Ó²wE LÃ¿Ô•!Ü1-¥fOà"„ætÅı€&êNó¡gU*sófaîTĞwŸó#BÖß\³¢)c©ıæÉ02™.`f†­K°Ô'$˜~|g\ÂN?m§"İ„‰©¾_ÌøÔ+U ¿÷ù;yÚáó•Ê§E¤âÄûÖwYşK"¨N\" ï4Gÿ.Òò}JÈÀ'.A&ç!c3ÉböæXë’‰Âü8ä#é²`·cÈL‰°8.rU8&sá‰Åzîp·®<À‰öşVóS°•a¥"	ÕCUÕ’ÏX9¤
Ó)ÂTarPA¦HÈ´6øu×ú¨eŠJûQRÿ×‘–@Æl!ªÎ‚„i
ÿ[ƒv»…#|ÁîÓBÚX™4ÇQãœµVŒ¼ao,êŞÄWbQ†¿n‡äà·.µÚlp'²°;ÁÁ¿”hÇNdÇZ€XÒ¹@ *š¯*ñ_ißfçƒænˆ»KVÔŒ|	?.?—¬Ó\Ğ‚‘6ŸĞ’,´zı£Ç©£#±¥§iA ß¡œx´~ÌĞãN›½ŞbÅ~»~6±º˜A~]è¿õ¯xŸ¹EdŸˆz$ÁæZ”9I“àÜÂ‰` )§Ëf:¥Où•M8
ôUŞ ƒ		{åiKh!ï"£lO{‚‚âguYw
!P
×Äâ›„õ=±2ü9}I—À.)NX¤ø!ü·•‘Yå)¾5ğ?ŒÌ³Ÿ"LåÚ.T¥.^Ù3Ä]Yò’B(4nqŸÄ„´¸àÿ¬cKë‘O62MËTµ×Ö(-6«¡³(	XËÅœœ-À5¥áR3ÎtÙy	:yàT´HÅq>tIh\šşÖ´u5ÄÊ©Œıõõ×RZÏÕcĞL˜º±¸éoOë (ŸÏŸ×ˆĞD*ã;:F$£¥…tßÄ™ÕS(®ĞcÙÑGøéHÂ6ı_ŸÓÜ¶·¥Ü6|¨kÂ0Ø¼ì}vëu÷DŒ·0áqNŸ4S†Õ=Ãü2£è¶8Gá¬üƒbz\2ÁBq°*bQñÙöEè²DÆÜî§œ‚à)îÉ§à<îl¯°ŞÎÉ&äÖ‰Ùt›p¿ÚƒÖa‹DñæÙ¿Òáy8JzIùz~Ôkı@û\&¯w½Ñ-£Ğ*CÇª…‹1IOƒŞşB¦[»Ïö5‰IX†ÎÏ$¡¿*÷W·J«`d‚âë^ªä&j0´ùağÅmi¨E_=§Õªåç~ÿÕ$¶şö22UŠ>ò[uèÿa¡éb'I~„íd÷î¤†î
ÆÜ»ªä SùFl:>'sÈR×—7˜äe•¦óŠ`v„mÈ²×d$®‘E2ÛñÆu®*½ÆöƒÕ?NbçRéì@åJm´ZnÕïQu÷Ä¦àh…¶2Â¦»èğ¥£»$ïaÜf‚ëó?jÀIFsfä±OB\ÿ#-:wáqøXJ|’e>?Z˜„æ?A–÷(LPyÌ’ƒ·9<Yˆœî¸Kˆšá`Ò¸VpêWË&}%›ùbíÕW
ºl>1ÇüSÅ—·Ğäà)ÕhöÇ*à{"ÅK’˜»‡X¬şİ‡fÄâPSıïÛ>á‚ÄZ`´V¾luV<%)ªÚ°~|¬¼õ#² 6ãJµ}¹vÒt7‡Tùnğßî…¨[§şÊ„QdÛZŒÛm•ê	VÆ°Ã…CL×1oÌ±š7ä3ÍCşw†e¦¼I¨ë’kHÌg~!™\æopƒüQIğÌóh²‡,xª¸îòâ0ÄJ¾7ç²N'¡•Û
ã‹Ô2¯«IÓSgF_n×ããy¨:GÓ=G’p#ˆ'¿½6ØvÅÛ,h3.¡ö“èÀßp‰€¯U%ã(îşÊk®zBŠæê~‹r×U/_ÖV¬¡Ñ‚²È.Ş§…ìNUÉé+]¸ş€ò¶9H÷ |ÿ‹“$øàuËâcÆ³·‚'Ÿ–Ç -3çûTÇ‹%9j°cˆÓ*T†ÛS1  	¦ j!+    ¯!
¿ÿÿÿü«È Àh,B‚`¸TH"´iİß;ÕÔÕ]y8]Ò&]R2ø	öÿ‹í¦\ZnÂğë«ÍÃ«Üä0}öcş3ŸöáÀßğ„†·¸Ñ‚ê~ÒéúeâA“Àvï•bé„¼û=–š¨ŒzD2Ún·YÏFd„:œ¬›lï^’®ä½($U
å‘•¸„–t^™
]q¦ôFjTNL
,3İ b@"à,#1Fƒ`¡Œ*ˆBa½¼UÖºï-y5|ßŸ{«¢T©|LŒöN·ÍË:_&©ÊåéöËá7›dO –»zzë¦L7m§këÕ*ãÉV¾Ô-ÕµşÒU/£ÏOÒc¥~!õzOËx%!å|š²MU6âÒ@|°—Q²[Æ6M‰3ªİvÚÃ :/m¿}f×£uxĞü[:ONSë4ÜÒğ¨ßÁ ój
^+ìƒâ‡E%ƒh¾¬Ğ3\  u e!@    ¯!
ÿÿÿÿü´	‚a@P0ƒ`ÀX*áA”"ç	“Ÿ>³‹İ¸•ÆWUWl…Eö Øş¯ıòm±{ĞĞ|'áÃğö'U“î§å8şöVï¨°„o>`½Ïp·Ê9o[ÄíÒG½@m½Ÿ¦Te{¦›šÕß~.WÏkIàÈxev½³’X¯û©ñ´İ‰ršQQ<£$×²p-ô¿y¬"ŸJÍR¥RC0&”Ã€±*D
‰AA¨L"SVeœo«îìË¢¥G¶¶“°“¨}Œoÿ_?^Ÿ?—_Ïı}í—>¯Û•Şé“5mºŞ×<ºd%tWå?Kó|û@Çòïöí ßÂ>¯òĞ&7p¯tíáğ:çœwÃ”u)<?†Y“+ñO2õcûL@&…³´@Ç]ş¯Q$²ªÂœ)³VÎà«‚‚K„>Q Ívq0…IÙ×  p	 ?!Q    '     67"¿ÅèÛäIJã·cMéÂ@Ø®Õ§ƒæ)qšîÑ€¡î¯•LÉgëå¼ü+cq»Æ_UÒÒj…ŠåÙ˜¹Ã‹Çæ>OÎ´º!,Æ®è›Ó¥oõÂÅ›Ÿ®¶ç5 ‘÷i
A`|œz+ZÕÜí]!‚l>%ğıGÂD‰,°s|`VæÃÏ_Á°uOºÉâ9yFG}}hß];»jj÷¬0ôbğTåÃü èÿ.‡øâT$q9&áß­´tŠ0’è'tœÂbrÄZ¡!‡y<¯zY«Š4ì0•8bd_;Ë;aŠİv½&=$v7œc§îcÚĞE¥®êı$ºß?(¼?‹÷Ähtİq¥*«é*şÑàĞrÛ©oW8¡‘<ÅâÜuë“5tqƒô¸ûõ³kıfœÖD;åM.l‰¼ö¼ä}kt¯å“î;‹àôÚúùñ1õüÒÀu÷Â ‡Xè0DZÏ•uâÊÚÉ¹wegvï‚ğ:8ÜÙÎÆŒ«5Áæ0/ˆÚ’C»Õ)ÀËt´ÇÄmS©T­ğ5R…«tõ5ŸÀ!5®’Œ¡’O‚›FÛ4‚":êvê?Mµ*‘Q±-&ƒ°§0[±Ûék*í«ô¾[aÍ!`^¢ƒ~åA+¬T³³XÉô–³ fy&[İ€N[àª—mÜ~ÿk€¥Ìs¸8,&XI¸û_MHş*êYÛ`·¬VşSaR:k%ÌŸ$  J a!U    ¯!
?ÿÿïü›ÃPX0‚¡p Ô(" ¬Â§—ùõªÓ¬¹´ªµL—_C¾|¶é×ÂOá§o»·nƒy@ éãŸË½çQ»´ÇƒªÎÀØ×ó•F}Ö´^şšMÇ™‘¶³R¹öıµ´”qWunwšÙÆiÄ‡&Qr¬¦ã‚J?[Â2¹Ù#YUI¶ÍÒ|ÚÓrä‚3 N¹•g0‘;¢ ú¨# ,(Ã@¨˜*A@‘"
„Da ®²ºßœ“r÷íßŠ¤Lšøæq›ÿš÷ıãÒ»úmúDøğô¥<`ûÄCg›C[vùº« >ÿïíà¹ì|#İ}½%AüîI‰Â£ìd¿qGëı¦Í©˜¶ÿĞCÑçR‡ÏìÕó¾Ã<†º±&öãºî~#4Q÷w} dşÌ3‚ÒåI‰àüŸÒT” {¶²—|h  l h!k    ¯!
ÿÿÿÿü³Á¡@˜0&…¢@‘©q[ë¾~7]n¸¯%ÕH’ƒ×¾–öOåõPZO÷÷Oª=~È]Ã<5ÏêË#ó¢GÁm½€ò__¼œ1Œ{ª{EzôûQÉ7©ó¿KM§Uƒ>=äóUI½ªeññ4’©H³]…á+åê_££Ó¥%h›Fs`A)ÈE’l*BTN<‹:YB+•+ " ÌHÅP¸L.
	Bƒ  Ä¦	t•.“8ÉS¬ãmÚ“/5ñ’µÎ†Fç‡Nnà(ÍËãş|½ş>ûöU`6ş”)ú–åa÷vvHò[7¸É/õq@_×Ú+ÁÒ§÷ú­ÙjJ&‚-Ëçéö#b—âÕâúúª÷yåsE¢ÑaÙ°ŞÊ/ËñÓ{9ø-Á½sr×ü’ıU“ód4ùc`u>L{S+µüã@Êw^”\î
î ªDo!ùˆö€  s	 !{    '     ·"¿?»ßEt—ÖRV£-kbQyõã,Çëæ ´F
b}m/¶k©æ]À/Ôœ…3y;ne½Œ·²yš,¿SƒÁ¸Ûk‹…Gnuåj?÷¹ ­5òfP‘æ¢ó…“¤Š×71ïq ‚ìÅÎéğ¦r 1®ŒX$W,8xÜS7DLÂ€Ş…*\*«HGÊkUÅ“	©xå¢Ëx‰  Ra-®×jÈ»/[Ä¸aÉĞúâÕSj:xÜïö+ëïàı÷[Ïv÷©+æÖ26öV.lhü·Ç&Ó‡ïa¢º€"ıú•%„†ğÆ.’¥½¸FYËæñxc[®{—ùõ°Û«Ã@«]ùHH¡k:¯2¥+]'ÛŞ&ğ1¢eŠ½æ)D.ÔØÁÜ×arµO ‹é0®¶ğ~Sy¨šÙğlÔU´	]SÊÚ“ãDkÔ“+9À–—•ÕØV‰nºÊS´¶_®¢VHo§MT@ÊŸîÄcé“¹RHUSÜöK6²~_Æ-?wLÏêÌÁøÉxè¤k%ˆ
”F»Hé%ç÷³ùß\ @½Õ|‡C4o z7®Nõ»1lZŠDC ĞağE<Y¸¡kje¬ÄK¿µÆaš¡é›5ú´Nİ]DƒÇ`§YoNÃÕÁÆ1ãÑõ«Ãórd1+ï»€   j!€    ¯!
ÿÿÿÿü’†b@è,(
‚áP Ô$AcŸ39šñ»·\Î¹öÃKRU±ÛÈúuİİ×I£ÿ¸ûãDş'=+¢cyŒ¯Ô;ÉAvì;z‡?ã „“{ßÄ'ûı>Ä¸Ç)àøş«&û9¨kgäùZ*Í¥ïğÔ,è|Ö…TuóZˆül©nYÒ,¿yN4)^…ÑµS¼
ƒµÊâ>–gNãÌ6
Á€°à&
DPX(
‚ ¨ˆF„Ba¤ÖJÔñş›ïøÉøùçŠ­µUy<ë|Ï=èY~U}²w;´4bñyÅ›;¿Âl‘üY>	ğ¥ñû¡:ù‚µ_ÓQ9ÏÔÄ^ïï~F—»½’¾¹$4D.ÿÏu¨‰:¼úio5Êö\İQ¡Óõ%é;I”ôbÕDÍuÏºùèî¥ 6Ùy&QR„…´)RÚ®ùRIRø] ¼¢WıP?ÄC€  u m!•    ¯!
ÿÿÿ÷ü›ÈP`,
†ÂP‘$c&³.n’]W[önä”IQ‹+ÒQszõı“rx÷îüŸêïóÃB=&´Ô¿*·xNÑ¨¿j^¶H_Ó²–ãÌÜú!Êi
QÏ»àÌD¹£—»ÿùW&ôêjŒÜùÙpÿS8ÔâI“¼¥lwúßQÉ°¨ºqeä„êy\Q^¸B’ëuCJÆ¸feT	ƒ`À\,h¡ ¡(%„Ä#1³Ï/>w9I¬N7úş™**ëï˜İ¬Aş|§üôyaé†^³ûnÏº­÷İòp°<D¨“ı°èå>[8·ÿ«ìñ?®^ûGCcÃÿÃÀ”ĞëéêàïQ9iğ!Àz7İáô€´_vív¸¡«hK™úœÅú¢Š¶»JÚbT=€n•g]€cØüì”ıı]mø“Î0 ¢Úy„cWyhwˆ|hÒ¯Åì à  x	 	°!¥    '  }  	§Aš¥úÖL)ÿsg¶L8§ ’ªXŒbÅ¾ŸLÃ§GpÅeb#şâkêÂ¸º®J\ª›ÎZrAvóÚ&K„œ6ù\­İ¥}Ïö.Xa·{”ÆÛìš}öqh f3| aW¡‚´í•WòVë0Y×~†E–‡g{ õÇVŸüÌãºNŠ“’>ƒe{÷!£ø'…2lv™F…¸Uìe29ÔD¯+åÿ/«WávÇøóf‚ÿnÒ´­TÓØVb	F`J!9.6Å™=k?¥¢8õhµM™ iTQe6šæØ,±ßò@ˆ”Ë" K &gY¥¬eg,÷Ö1t5X¬¥uÍéÌpV3˜6ïÛï»HöD$İûSó¤um²vrMœ©róZ¿=8pÕ¦ Ôz_ş¹ª'UıxBf~ßãBÒ2Â ;…'i¦ä›R\IËËô¡ãzŞ¶ŒûPÛ‰ä>ÖğY‹ö8K•.]aŠ‹ä®ŒXû×VÈãÃ6Ã½•>‰îª*üV½v`„³UZBC¸›a‰"Éó—©é5Nä±@=.ÿ¾ğtfúÀä™43yG³¬sh `?a=A³¯/QL³iˆÆ´ªHÆ ŒiÖ°=ª{½¤f§Í9‡·˜ªÒj7®Øæ=½›ß”3å\bü•¿ôå)¢ÙÜæ.w7ÆçæËƒ²yˆ/PsÖ°VÃ½¡Æş{.ÿ•
İ7ªæ¥wŠ|ğ«™?˜IÒª\°Tùè}jËguS$î÷3Éõõ#0İ`]•9qí†NØÅ|niOTOØÌ­«¡ÓWµÔõÑ^ğ®*±À‡×¾´)öì£ù5•ÙŞî­-Š×Õ
~½H°”‘š¡O4sìˆâ¢úıfŒs>#3f‹Õ|¸<Ji×Š I¶·¸şYŸo3®¼§üEzûëg‡;v4ïfìM[æ´²¤ıRÇÚ²©=¿c¥x˜\dûnHŠ);r%ÕÅPî„‚yè|/_ë¥’8[+3’†´bØft¬wVçŸxKê7£5®=6<wlâ|õ\3enú}•bó2}öŸŠD•ŠqéNaLú~2!	Èµ<,Ti’	—‡[úmÀÃkâå9?ÎCú=á8¢´ÁNN~¹º}k4}Ö±<m´ïõ_Ü$*à»½6ÊAãÓgXóÆ§îG¿ËÕ«;aÃ$*µŒ‡™„üL¨/ë%‘–=ùh”äªÓGìÜŸŞè?,6œ³ÁéÊVˆÈ:‚ÊÑÖ#Gyço¸Ù÷;:ó_)ªŞw;ÚQµ_h{Cu@	-è3„ÅHô¨)”L€†´¹¦³nûsıçXÊâør‡
Ì
:Â»«ÄklgJyÜ0ƒ!²{’WÇT‡ VIƒ0Ãââ/™“ùy'¡t$éj,·™$ì¡… ã›]<n€“‹&¾ZÍ1ÆÃ`ú-Ssƒè’ü|¸Mƒºªàcß,a9!;á]cè_agƒşô|½Ãt3ºäNòÉ^5²G	”X]<¦ƒ9¦Çû¾BêrÔk4hÙ•ë"¶áhVïôŠ"b‰â¨ÜİàÜ’CÁ¢^ÿHÍ5¹Eîø_MõL½×Ş„¥ã¯ºuñf„¬ñ£GTºX¿XM”İ	5Æ|¹ã¶J0£œTŠh}—Ú¡qò‘‡â9ü#éƒ¶‚´;í]¦¨=­=u÷¸6×¥OÛm-È÷î÷„&\ğí¨/Y©'ì@°æ	\®­àG;Šì]ôÓiBm,ìî†øÒÖ
­ÉÌàöÍm ;LHJ’ äÏ¤CëÎäövE»k¹q°–4¶Ä ·9ÿÁ‘“>É¶j± Ù'ÜCŸLO:XÓ€†Şò±ôš@tÜ49}éštŸ#`b¬d‡1‹áÁşô7²“%wsùğ_ièßã^zF’³º÷ä®Şò„4ììêw*oíd7€§Nïåí:UDá“ŸÏ¢¯+9!.}yF.83ÒØ“ÍŒmCÎÖ*–¢i„•„°åéÅMmü çAåëzğq3{4mD2Á•¿&pôìq¸Ö×œ‹@QB)Ÿe˜V¶µ®Ï®ÎKÎ !îJ¼]86»'ÂèN²Ğ‰ËQ¢k5ŒœêçÄ„ãëÉàİÛ€(Š‡B™Ño^'³ä+Aõt­€âhŸâ?õyÂiÚ,4Á×—–İd?"‘ç¯ŒÀáÔö§ºjh~úÿBÒŸ##~9€Q“lĞ­Èg¦AC²’£óOkgòi†óñ(!ÑxÑpµh®µ¼š2ş¶íßø¾ÃË] ònÙIày©äc«Ç¨îFHì#¬> Í„º3azQ–OqÏ§œb,8ègœæ†”š%q ¸'ö!~İ<ú¿ö§ß1¼Ğfrîd¾‚«”’jJm‹Sg@m?´Íİu$<ªóÉNQúæ†Wh)å)û1#@dß’ü¸m¸#ü¾
UÇ’OË'Ú†Ÿ£IR‚•‡ìQñŒc	zæ‡ìSâ‰R!Âü•-Å~Ğü8W3v[À§4	UKHİu:ø¯<FğuÛå\ëTïdW¢®è«Ày`Ø¬<\uó½‰r2^Š„Ch@ Ùc¿{ñõ9RµÂóë5Z
âšI³ìúuª{]¸°‹ê•(ï é²sâu™ÉÅÜck¸·˜öµ6¿3	—1ÄS ¥c0Ri‡ÕÉ…}¸ÈuÔ¼JmL$¢âwµH ïp6øëì\6¬ÂÉF¼EL®u¢	J ÈãÑ4õòÇ·ÖÊ_£860Ô8¢èª%‘x£­ÕÓwÄËaºÜ”£²?«Ä³S—	àô~¤.¦Õ¿?¢VyÑÁí7¢ú·¢®$¸ï	X‡+6óZ‡'Šáğ-i?Æ”Å«'iËñì&vLí	ĞJ6L3KÛ|…4Ô“¤œR"e°ìv]ÀS×³'?	ŠĞß(İxšx»oEJU‰ÔÊ¬´¼á«æ|Pé„9Ã«Ú7Ph~2,µ:ÿâP‹È%J½/Á&@T›Ïú~ª·Ógşd5·2XîS¯)w¹(ºßûXºÕë•;œŒ3òkãœˆèã;…£ù²5åm"·DÑ•É²®ñ ¨¾ÊëÒeY
¼Ã°a?î+,ë=bÎë	{_îS¢ú·£t˜ZFiÜ`ÉÁ  	» i!«    ¯!
÷ÿÿÿü«ÂÄP ,	BP Œ$Aa×)¾ÄÖîW´¢DTŠ”Uğ9ëééôÛÛ¨úMÇ«¾•éoxËE7g<=ø‹Ú~Œo=t–VÍñ@±êæüßëã2İ~wô©ß¹Gç:Ad¤[ÈG¤3/¢M]x›:1I‚*¶4¨~ŸI·ŠğZÌªÖRŒÕ2A@V¤â½XEY"TF(F‹Ò4i]Á€°à,$¡@¨Ü(b
‚2L"&q¹sw:ÄİÃ¯ZRV¶ºÕJ¯:	›¿W´±ÓôØ_o—<]8şãß†»h½û¶·z+í~}û¿44şW¨vÎÙá¾“«ÃåÉ%¡ı¯Çı¦R·ºİÖê·‚¬®7Q_©¡U}·4gß¼Ä2]ßë*î1—0ê–K'í.‰PšnOì­ˆşïÏ“É =/¡Ê'[İÜVğ§óú P¼*^÷  t h!À    ¯!
ÿÿÿÿüs	Ä@° 2†„ÂP˜Pd#„‚,xMŞq~ë^qoMn@šØ©Öéø—úÛ±éÇ¿?ÙïÜ4n³÷²¿Øaö´iB‚wQä`:Zis7Ÿ¹ü"2ŠSÿ:¯yø9¾‡¡O«;g£íP|ôüß]¤Ùyî¸L(=pI&ûGœBJ-‡HMQkŠÉrc”C<u–D&=k—€Á0"àL#Å@°\L
BƒP ˆJ
„N½ë&²W·†³E~¿§ãßïÑ':à]ò|ƒıß¤M·3ñ¸ï7ç´®ÿ_«G›€ë—úªÿdÈ«è"î”A5àëö\8 -Û~^ÒŸÓ¿f=–AştnO@gôVQrvK›vë7…Y¸ßVğ×¾ßéµÙèëZy±ùÿMôd®ï28”ÕEFX‚Óóç«íYäÂ¾é‘¼ e%€}sNW—Ş0  s	 ù!Î    '     ğ·"¿|¦Ş ¾}µš¾x9òŒ¸ iòËˆj“zÃñ(ãeEô¿ç 2ıW­*Áİ›[‰bÏ”‹#bş¿Ÿ`U"ş)Í”CAülù+2s¥1K¸iïõĞ®à×8årÏØª>ºÓ€D=lîCD¯§İ”ı…"HS%ÔQZØáÉÑÄ–¹¾VcZÊ½g½`¡‹adË…£­t)×Ô¹]‘a6Ñ<RTËaœn[¡k»qïjØóª@kåq°&êÆØË+v<obá×Û¦À¶³—²üj>½ «`ñIúFå ÚÜ²;_ù8%¼ï3Ôj+÷&t•‰ï5Gh®°•¢]y¶ıt_AwË•±*™ø[mr\¾‡\•3â(È„²+:ÕùÈŒyÊÖš*À+Å%4½ÒÊ5jôSºÒÙüÚ'o½¾µ°w´Çœ	~¿¿B½ˆêÇâÜœ(„²ë‚xÏ¯âã
SËYÒ“‡ÊLŸSàjw6ô	º·ÑÀZÀñé÷\1jú æÚre½‹„U‡hUŞ26¸i¡MÀO›t°ëzR‰ wèHıù#©	usŞïëx·BÈ¥İ‰ÎTN‚€Ÿ>ƒÈV·¤3¾ÈO•®ÿV.IT   k!Õ    ¯!
ÿÿÿÿü³	Áp XPCA`Ğd("„¡ ‹¹—Ï]â_\g¶SU–Š¤¥ğçoù½.xÑ2İ.HızûêÔó#/é)~âxGíEñ7_R¼¶×ı}j{(ôüJ)1Şçõ_ÓıIoz#·7Ñ›˜t×‹§‰i­RÈë+¥H½5«š]’º”©"ö«zô¹P%õèwª©0@ØšÃ’áU‚£; Z@‹ ÀX0’` ”.	…a  L(
‚b·íÍK™PÕîu·Ç·Û÷srgG8ê~VwÎ¿Á¾¿ÛG©;ü)ëÑŒ½•S_ğÇ™Qe¡¾>RÔ[ê~ÂUPİ×rÎû»|;Ê{„ùÿÛöùÓ·§¥óÜşòÍ+Ú÷ì1¢¾İ›ÃÜöÎ.Ü]jÜLû*xD¼Üz—¤¢ _4=,ŸÇÅ S7‹€hÃD
_ûKp  v l!ë    ¯!
ÿÿÿô‹"B€° (
‚¡AT$1cŸ>§Ÿzã$’¸Î*KÎ¶I*eJ· |pòõ{?3?›®jıt}6õWônHî¤:ÏÖ¿©ã.n«ƒ1ÇøÎa§ı/ˆ­ÃM'£ôŞ#•¨|~¦.,‡ß·úÜª‡ùøímò!±)óá-æTh±‡8Üw-7J:ï[AÉ¼É—$µ”‰¡2PZã,w*iAay­aŠ	õ€ŠX2ƒ`À˜paATh"
Ä!1Ì"SÏmd­UÔ¯ùûsÑy”¶j\æºwZı'ÿıWîç[÷îËø|^üŸ[¼Ò¿¬ÿX«A—RòR~‡„—v­’®?ä¶ô  
Ûâ€ùÖ7z}õì'_Kl¬šwfÃ¼øº„>’æº‘–>äş·WkD©s‡ø¸#àïãy•K¤ú¿@ ~!lÊï±Şğ6v}ljÛÃ€  w	 İ!ø    '     Ô7"¿¢¸™8ffñœ(¡ª¸3µÔ¬ä0sLeé"ªyç‰¨MûzK)»_?š‚§uUl·~¹ç Qü÷o&§ÌÖ¯#|6>e‹™ÔÂ= *ä9Ãöîùå6N†1ruK‚Ç©`ìSR³±Ì ÎïBƒì=õæÚSH‹Œÿ>obo5Ú'dÅ
Z$|‡â*á$@Iò˜ÇGõ±ÛYqÉÏ\ÀÓ×`=IìŸà:,ê.XÒÜÉG‚ÄMğ÷bWä-:la”²4l´oşrL?³2îX'yÒmwx‘çÕ€œ ÄšêÇÔõÇ.÷ï©>üDQcH2Çs¡ù—¼l0Áí¨­Ó¢:¬A„áïÎ;P{Š|ÆC'C5¢ëİŒ~ú÷1=9
ÑNW!&”(øÄ1G(2dANa„+‚Í,?.AVÌWzH$Ã9‘ıƒëêVm‹pÅdÇ•,v`c»× ‡2¡byn	é³YÅÙN0ùû]•\9‚Ğ/& %·&SëW
ˆ>{Aêš+¿qbyê„™BKn?vG¯(²D²CZ8k!ğ_h¾á çƒ	Ñj[;ãõ˜fèÿôc.Ø««º`  è `!     ¯!
ÿÿÿÿü›aA.BFR3ß¬â®êJö¢Qj¨º¿ ÿ5;+ìUêÓĞh¸ü}Zr÷»¹M{(•aß™¿é\uÇßgõôÆÀA¾<:§+%œÒĞ·wùÊ.»}ÿ™şqtRf´ÛÅ¾™ãŠh‚`i,ŒŠÿ÷[Æ›òñü6R›ã!ã¹‰¶Ö€ª·”Í+Ë TBªIe±¬.”I`7šx	ğE@è,(ÂA0*$…BP D$	Â'0²šãÇ×¬¹*5š›}÷¹6'Ìİ=ƒ|ü›[‡áÃd¹’.ôx¿¯–tò˜”«ûÛ³ğYÖ?2ÿg )dMü¯ÇÌ÷æFçîÖÿx=O§›ÿ·j§_$Ã‰)Îª’¶u-í/·6Ò|×—<
Ÿ‘Gv›r`ÃKÔtô#S-d O˜Œ =~NÑáDÉùg„VÛ2ïÀ8  k d!    ¯!
ÿÿÿÿü³Á@± T(¡aD$[}²¹×‰rµÏÃ›ºº¹‰k%‹zˆÕıoÖ‰á6É{6ÑÕ‘RZ}Ø ù²µ|‹ó PQÏğ{'ÒäC^ßÿ Sëv¸çù~%ˆÚ¾‘4å?1=Ô~Ô¶³]"Q£¤9ÈŸÁ‹i|!¹9ÁzfN¤tR ¾c|Tf*AÀ¹—NÁej"P6’` XN
‚aAL"CˆÂŞ³:ÎµöÓs«ªpÊ«Íl¿eøª¯ yğüÜ)şŸ5W—]¨ëHõÏØ½ıÅûİ£nı—ùdÿ½*Óù„íÂõş®ù
‚…ß…`*÷ŸgØÃÈÙîAĞÂ8>£´_Ò´¬aşóş¶Òî:'9c.Zác£)é‚Y¸ÆWjfk>+hş°iDŠÔ^Aó6Àß‡×÷î¼ÄÚÿMLÚ‡  o	 	„!"    '  }  	{Aš%úÖL)ÿ:o#Ì÷‰›,§gÏüN©{4ªw.e!ÙÇyè[ˆQ“}2%Át6¼Hc±æ•u`vW]¢Ïß`ß\Æ—1	ÛÙÈ“şw
ÊòTÎ&Á«·pæ6£0ıµ6eUÔØw7.–:—ä)òcR£j2ZÙhJ#İZ9TóH=ìú{ª£oÿDú|8?Üp›º¡v[ÕKVª{å:Âx%S¡„ô1á@@wµe9ws…sŸ~ÆeT j¼x}Ú ]VQ°^	J”¤€x‹öœÜè´{o'ªtü=†ŞÉ˜™"ù¤¶$xG	}‹†ØVXOƒJàİÕÙŞsÃ@ÌÂ[Ë÷y
’˜ÈF`†‡J3ëQ^ó6%ˆ¥ÛíAwö©G1öHœ€ÀÎÔòGÔ“„“øöƒÄ—[¥i¢Öu¥ø&–¼µé’RïŞ+c=kœm2ß)¥'§ÊsD
Œ¼Œ&!A³"bxŞÿ ğú0@Q5Vçƒ> ı,ÔÖİp•p}İ½ °ÛØAŞÅ>ü²z]}/ÚC‰6Éµcªä¥{yÔáÈºSÃ9Q©åš˜EÿF•!”yfåuªt‹ei_µµBqâtGä´¹²Ÿãé9³û!úÇÔåÈ€TºX5TÃÒ}Á7J™®ş‹„œe¶»óÅ E¸â:…¡ò7„
}ÿÆ
L?ã4N#>*ZüOşuWÕ]ÀRµI#ñoÍÍ)öî‚’Y4@€fÿöÚ!sr·õˆÎæa‘ÒîÔî¢º…	|X#‹vÀ8j"Ú£û·Ü¶–Ğsôş6Ãª‰@*…çŒ+\,ŠŒÊXæ8BÕ_^í‚où¨
.o#ÚË*ÿé$ç$wÇ´T¨â ×Îº1,O]xù±
hïavRCŒìë(Vñ„g;9>Áêº¿&ó(mLWucò¿µ§õ9¢mÓv-~Z`£Áá™pauºî—¥oSŞÂibb^õÀËì¸§3‰n¿¿¸Áª‘'±Vºªjÿı©î£ÿ6Ø7—ÍDÆªñ.m<	O÷ˆõ- s<ÆÚ:”pOØd]¶H¶Öèl! à–²ëĞç`Q/„ûÈ„ÇjŒÿö°ÊwTXêÚUˆºúS›ÉØ0‘²:CjĞ7†¼XÙå·{Ãôä:8ŒOd@¢@ø£Õ÷3Aaa8;ZøEßÏ_\¥*yt!Š(Um“lÇ1°mÖK¢•œTõı÷³ØÜ]CIÄSÇJ—6~øy{×pVr’ùrÛ§öCQö8Ï™BÓÉ€Ÿo/1ÜÈ`ïüN>v×àãS³b U¸~Ûâcû¨"1$:—p‰¬”™]ñÃí·ß9p‹s¶2˜gÀ[),$"ƒC¡_ ùˆ®2«1¯÷i;‡)îõ]·½±íå‰=Ã¦cnğ^T.a‚›ÆóÿË~·ÎÖwËa(˜;Ñ6péni,~”šÈHFYô	>Ú=ç*læ!H“©¯f5D)ÎB™—ĞfrŠ©‰{uæR^}Y*³ÍYç¦Ìt·x€1³ò$$–RÙa;óÖŸ‹2/¼–Šª#?4nZîÑŠî]#Á¦Ö GÌª<©÷+K’¼fµç$	A+X«ßøqvh³ÕÍ$.¼O"ÑÔO ¹½„Zƒxƒ²°şg)Ëºa‘˜/¼P=ç9zÌ-[3p:pÆ²¯ñÜ?5Ôî×D4wÀ¤é»ú1Ş§NÏóDÊØAF¦=>Ó†.šü VÃ|o¦¼tIfŞüåuKäç"[™uJşjìyvæ n#XÈşÅ°$
úD=ÆÈÌ„—¨õãfğ9ÏÀ4ù½3Áİ=^Ğ’Bˆ“ò’ÉÎÍæßØXÏã³Uá)ş? ×˜Ø-İõ-{Nš#±&¼'S¦x‰èuÁ—a»T+ˆ' ¢¹Îùn‰TKJ¤¿;PC©ÿÎ“DùÃmœá$¾-¹3RÜŒó°8*p•,‹[îˆ[¢‹Õ -y“`ÿ´‘d³ÇÈT@Ğ,ü­;@®X÷¤rÏT#¡¬f÷LšJMŒ:
Ü‘êüOVYrÙÅíy3Û§yãûĞx¨—„kı)»[fR¶æõKG¶òÆ6küR&š£›ÚÍšˆ\‰cö~È™f+Rı­X¨Ïò\Ÿ:K„ˆŞ˜q÷\æ&Õcd¾d½åà‹æÑ¸±‘Á
£Nñ!èG$Ë%(a¤'ß…³íU³Ös8Ä0Ëş‚†…(T3ÃÛõ.bûÅ'u±xÿÕÃbCï4ÿYİ#ÏÛ)8İ©ZsË²(
=ú£½@ÚÀ¯&2=Ì»¡Óë„
¾Ğ¯Õ•¡æÚS‰šÙÎZ,},’“¬-WîÍáT«÷†“ªáşÎªÉC<Nô»øùT&^|N˜ğˆ{ºn19»ç:.!*·e—«•NìPu»ªbšQŠ³ÜØ¼
nĞ_–;&-ãRI/Å" ¿ğrõüÜ¼¥µş¡vFYwøóøI4k\‹Iîè2§ÍV1‹Œ¯?²LÊáÑFÓªqmœ“)‰y¡¯¼
ğ4Yğ*üÚm»ì‡p¼Eƒrip{F ÓÍ×fg)¿Ğ`à1ıÇ}%;Šh±0|·ƒ—•A}}«ÛBêqÕ¹.i5«AèÛEONãM¿sàŞ¾V]k»‘};o›`X…)'Ä*ñfğ]‘ÿd†r%‚…Dpá#O[—.“’M‰/b¢
¸’ã’ªgÕÚ¦w Üu ÆÌRµ¸Ñè
X	Ë‚jqnGïmüœcXv»üõÿÎ”ù'hMƒ¾|Ôé_ƒ@BeG©jFQ>–\reû&¸]Õ8g?}†‚}Ó†Pöïó-½Ø/®ÇjºKŒòĞ7ÔĞ ËC\â‰³ÎFåYşMõ¬¯n¸:Eÿğ<„Ã¶3€ôÍHõäêèlüôT/î|ÚåW½ÎsÇÂº/¾jàÒv z“]i‰Œ•j±J]tQx‰ 5[<ùÏ‘o©Õiiè¹ =r|ÓÂpÿ¬½rrOô+ye.%:B´$ Î¦ö²™]M"ãd
Û#KZ¯¤Šú~˜WÅ¼¢Ü¼ùÖDìêRõ!  	 T!+    ¯!
ÿÿÿü‹&Ba¸XH
ˆ-ró[Ş³wWsz¯®jâ×U)l´{
õo;^İ™yóöë£ëÿzrĞWW¸Ï`pã×,w¤ÒaÇß×¥>e+íG4²]ÿÎõâ{CbsşöÛ•JÒw³¶*TÏz°÷’9F³”1V4š«gƒg‹ebëFj¥ÅŠƒİÄP©ä°Œ¶g,()°
^£ l(Ä@°ĞJY…A0Eëß©W»©ÖKÖî³Y’Kæ^ø¯˜}Øÿ4ì>çGg®ƒİÏvÎ«~¥ú×…tÍO^Éº9¸Oï%üSÑ·k6Ôù8ïÙ~r˜Îs²g^H[X 8.š*É
W”P­Â2Óó.¤KÕêî½?¹|±Z1ú\MIƒÁú…ä^k…Ö/Ño­=³pm‰´gü€gÔÜŸÕXéş&mş£>#„½@à  _ b!@    ¯!
ÿÿÿü’…„áA0P0*……a TH„,a×9Çª‹ëšá«ç‹%"L¼^³îeL¹önaıC]¿­x“×'TDBH]œ»¯h¼©MçOÊaÁŞ3ñQ˜Gî[‚B·ó?«‚”ÕE9ùlÙÔ»óÕÀÈ¬ñrÎQÆ¿Ñ)P!„Ì×ŸBY5NCDg¦a(ƒt,IApÆ¨^DAÚàj€Ì8 Š„1L4"…„‚P ”D™œnïŸsÄ½nSõR¥E]ÒjhQú°ıé_§
Õyº"ÛØifz^Ø2ÇßwÎ>ıı[è¼NM‹»*è~6õLgæÊîÿ©õK®­—¯ÛO„ÈP„‚Ú`Oô*(w:NÙFy];œ÷=n«Ò¯Ç»SšT±¥n
a_~®%\ƒˆV‰Obùwı›šÜ´ìùÈhÃH'ø»ëw’@?‡‹(À¢10 p  m	 '!K    '     7"¿^¦[ó}"³fë+Üò¥¾ê÷jqékÍŠ*ê¿·àJË¼Ïİ™Ü]_-PÿBV#-0+Á¦÷,9òò»
÷DÔS…k0Ş³¦uOÎĞªÁ¨‘k÷u8¢ˆÃ]wzç†¯ğ"EËMˆMm—ÁC‚ÄmPu-eí;·ØÊ70Bu–\¾»¶í_Kî‘“ñùÚàrƒ{Cj³ô2ÉT³½V#UƒœšÔ¹´°x!Ÿm‹B~RØÙIÃ¡o³İå€²ÅPƒMÍÎV(‚¹e_°Kaá‰H|WÀDG¹:%#Ç‘I²şoÊrgË‹#Æ#İ:Äf!“¯å§“¡7Ò2Ã±?£]/vBõÅ¤i…NØ`ˆèS™g+º9fl™LOâƒ¶ ¨ÑhÔ‹bbÖ·n¡/¾Äê?bEeÖ›ÃÚj2(´W˜%jÀÌõly§?*Ì¯¤ÀO )z`ó"©XÅ€)ÙV#®<oPó½5*/Hx÷ÅFÌ-
SiÖ˜”4ûAê$bÿWÖ_»¤0c.ûŒ¾gà<£`ºEs•°5ã„¶ú«_=1‘ZÏ¯†M‚|M³Ñ‘Õh\ó¥R¼…Ç.÷çu?MbJRè©,”ºÃ2¾_Pl§ OÉ€©İèåV›VÓ5\XÉv\ŠÜ4úE¶À5XílåÎJy  2 d!U    ¯!
÷ÿÿÿü£	ÂÁ@°`,(
Â€° (%	CEMd­wÆù%oSª’¦²Õr›µë8ñ—×Ş7¿ëüíƒEá²ÿ™'PŠ
MÙ]¶YQô+ì½C£[pM1ô1G¿×£80İõßÌˆ†Š•ı÷_§L%…qÜNšsí¶S.ˆÄÜ;lZ–†geuãİš
WC„Î¨—ë:İp(o‰H)™˜ˆê’j*} EÀ˜AA˜P*C1Lb5O>/}eZIûï¸kÅ*Õ2ø×5g‘±cöƒú÷}¹ããËâwïû~ ïöá¿°£ù;K.ÙÒ@xqõ+–MQkÕ^øÕ5i_á#MXjQ¿„kç—ÿ¿œİ«—:Ó{ËòëÁ\ÓM&lÇp»6ˆW]ÃéµÂÑáÉÆbvÛß´Oo÷!ç@Í?ä¥¸˜gı9„Ÿ“„°
ø	qó€ı³¤À  o Z!k    ¯!
ÿÿÿÿì³Â` X(
ƒ@°Ü*…B!‹‹ënzğÛ‹ÜÕ{n®Í)¢W‘!ñıWô8ßùÒéñåS«ü84}ÉÁµe¯õŸI¥Oëğºö!u¥ïÚõµ?)¾1×ö«UÖªâ^¾jN°úXk¾Èüƒ™¼*LÊ^¸ëúpÀ•c~„eÆi+$‹„a‚ÅÂÒ´HP
-EV•„Èò”@‰0`,(ÁP ˆ`
…¡ È"r…¾7¬ÉyÇ?{ßÄ«ûszæª8ÖèçèRàé÷?/_Q„Ÿ:M1=ŸuYOõ7õ&{ò}YöˆogO±ñp i÷×Ú½XFª¶¼J‰_º üZnÕüîûjÖoÛå{ŸúÊÆs¤Št.)Á¡\ºà>jáÖfCÛˆÑÃ<k(´Âğ>,BÎ·‚ÃÑŒX9¼*ÿ[ÖW  e	 Ì!u    '     Ã·"¿’@ï>ÇôÖ¼/—Û%JËâøYå%åî“ñóöîaP¤$›…àï$„ÿ_k·ŒX4„Ù¼?óÈ·"Ç¹çÙëH#ñfÈBˆÓæN«Š¢sİ&
…Åd\JoIƒ9êY/œ955Ú›¥%F£2yÔ\ûf§Ø=1ÀH9ù™dW8Õ³‡?µ˜Z@&&lµ©6"½-‚jºp÷„»—¬€Èşô<8cw‡ˆ~‘Z	ÚrtÎB_&³~=E¢^¦à?×%O%8ìŠú˜»&Ø¯\:¹¿ı¦gÀ7R«ºë–müÜDìÓdOvFfY…fˆÁ.Ô¹I´ÎÖ¼*y°£7 -bU*#(R<úpÔo’Á¹¾œ Fû »¾Jo9sù¿ÉKˆÿ œë€K¼—æep¯§‰²ÃdûñØ<¶fäCM­‹
ÂDf#ßì³ÉGÇ™gªŸ­1¤£wO?VÒ’D2ÙÖëÔ·$Iàÿ4ZÉ½{*û2’şú~Ôsªæ2¦[-ñ¸t-¦iÔw" ’Q6ó_QxT0g¸M¥ıÊ5˜  × Y!€    ¯!
wÿÿÿôª„a`Àh2âa \(	" ‹­ë½o­dºö×®²êêBñ2ë§ıWóÿ£û—»è´·_š‡~’ßïGÔ¿‚Íğ©{.õ»¶_‚3DîüŞ¢¿Ã»h)éİ’V •½µ§‰Øj½Ã,ÿ\¬+fâÃÈµ-9‘G©a8Ì”óW"8DŠ²”&­“)tT¸‰ ‹‚0 L(	Â@¨H*ÂP˜P*	PanóU|ñÏã¼¸qûéŸÛ¬/™jJŸN:Í~¡Ÿ˜_/Î­¥ìñûİÇùùô’Æ|Ÿv¡İ÷›]Úv'¯í0‡Ÿñ6¿(::å±Mõ´}'_òÃïÀsâƒé}.qôÈV1`kE{Ğ~ŸT5G•·ÔˆGÚÂ`–¶»Í’ğSeš#™©t§FG4'ñ†ÙXNèp  d b!•    ¯!
ÿÿÿü³Á@° T
ÁQ H(%
„.\•;Öğ×\ë%Ö·rnåLˆ}ı|ÿø×¾•¤ÿäİoşôL¿ôˆŒnúoü§&Yáêñº8Ûî®ˆgòuÊIôçùW«ø«ÒJ+êÊ«ÃïÔ•
‡£Ş¦&%å
FPßÄ©(é¡•H ŒQ6]á
¨š7N¨lÆa%a@˜P…á` ”$	¢1 Œ$	H´ÉxßëÇ®»^¾ø¬ûj÷Uç¸k¬ÚÊÔôûø}ª|V[ğß7ÿçñş~„Ô_bİw-Èê<û«Ûı5o^—\ÛíoÔG‡³Æ$#ÔwnZçõ5[9rëĞéä<ÿªßæá{tº'°´Éìu9kGÖ¿³­Eí°àK·æ=z“È@ 
òá¡¬ä9&Á&2Léü[tKÉò¤›1Aş&  m	 	/!Ÿ    '  }  	&Aš¥úÖL)ÿ@Àî—f€t.íT¥¸@:Á$şŒâÿÒ|G¢V ‡±Dà­Õ¤ÿı8gÀ=EH¯ypãÍUYfdú2FL.9‡)‰çt¤(RÚñ¡~áG³ÍÀT¡Bû ó%î-Ç\ş?'ŒèDõû<‹ÑdÇÿs}Åèİ›`NäT^¼84ÜBEŒz·Sœ¶Ào£,VX	à‡†t—é¥£TÔ‚Í£sGûú=ü}—~ÊŠW1„½²#‚$RËl+ëÎ_µ¶ÿ’ù™òĞzÖ+ëtošúİ¹ÒÕ¾ò®);Ÿ¶UŸc•WÒ-· H¹?Œ|á|òÛñOJ+½­ƒ%Y¤”müXOM%ã˜èä%‡.NZÇ?£ÅJXÁ¾ß€ã`à'–ëmïÈİQ½ôDŒ»ÊBG÷’ È³Ú$ÒÃQ—b´£4n(.-’Î»¡¿O®rúœÌ\)ê>o5?3éµÄœ‰âÎ§S]ö77g^k;µë@ÚÓ=ÁnĞş×†àÄé4¤AMçaE‡’ş€à:›±?ÃùQZÛ‡3Ö$†4±±ÖÜº¿õi\A³›õ·×_3_kÂÃ<?SÙ²–EÁàd ½øAŒù‘ÿönk‹<QQïÀ!\ CRÉæÍp”ğlŒÑ€š®NDÃ,R,šFÊƒõ"y>œĞGĞyvøı‡·´IN¿ğë„2%ÛŒÆ¾·äóWm–ôLœ<)“,'ÏV/{œ¯ƒÈ_äÌ$^?®eXµkËµ¢U³<ˆ0mA.ª]+G~ĞñX2@éÿvÙo^»ërËîBYÛ™¨OÖ`âBWeYa‚]v“y’¹CŸÒ¿ñløA•Ñ²ĞúAšã/£0Cwİùè4jx0^üó„;‹ÃL—Ã»Mj‹Ç”»‰u+¸Tó,Ğ#Ï=“éŒâÌÓĞÀg“üx»ì·›ùâ=Ú{=¿ÇkÈÊıIÎØŠvìzH}/¶IT!Œ@áZ9GËé—$b‘{GhÍ¼[ğ$p­Ø¥(íCìú¦X à +Wx’„y
¬ÓføU¬_Üõ6‡óÔ?AŒÄ´0BœñIm”&*J½è†Ö‰eˆÀÃ?c\ÀfÕ)Øs7şîÎÃ„
“õ"˜†ŞBó¼‰°a Î¦&¼f3È€î«+ÃckıH«²×ÈòĞ‘mŞTË…HTgC»lgëÖ0®÷ÛÓÓFãot÷^6¨ «xÑEÊ¸[«|R½Z¸†j³@RaèwëF»¥*d‰»Ç1ĞÌ¿¿ş´Ö
=+[4Z–.7V÷ŞÒòº†úÌ˜Àêy:ı§ùs<”<ÁÃL’Î%İÌP£Í˜Øú$Üæ½™ äõk~ÏjIMºÓŞê¤GÿD\ê¸w‚ŠÑëtÆf»÷ Äğhşó¸Äò‘ã$›Ü»no">şÌ1ÉüîÖ`Ë=Õp¯ÃèÔ¼Ğ˜XÒH¦‹±ÂNìu²ÏÑC	á0¼İ“‰ÃÈlÖŒñUMæüÚó`Ùº7æáa9ÇhÉ…ª›Ôêâä±Y¹)N<-å„f¾İWwlB~=7¨ÇƒLCñ¥ßå•!Àä9J*§•BŸ
ZBŞ´=QUM2…åN
}zKÈrÇDnÌídŸ	ÒõgËš¥"ÀğVj\—\¤4Ğ¯>ÌÙ‹{ÂmA½)¾í,5³üNª›Köó1ßÄù×MYÚö„Û×ÃTµÃ]«“Q]­£ah¢s~u®ºF/ü*%İkâ…ÈÅsc,Ma5ÇÖm7h<¡S…5WFÿïòîG(;HÑlĞn@ É÷ç©ÅÁä'¥Ã”ùÚŒ j}HƒØÏÈÎÖ¬¤
ó{ğ¹D4xÃl™‘NZ2ŠBWÔò¿Ì›#V”¼´Éèa¦¢B®l¯ğc¥K\¹6é—'Nø1•B†õZÌr‡HY|>¨ÖnÔ„Æ~¤xÃøï#Ú“}­€ƒ:o§_Xös·˜AW!}ğ'úÓ­ŞY¦'­l‡gıtÙ…|\YM½ë¸ª—>G2`V×£›ÚÈl× iOŒ-‘çÊ½ÃT$PÁ™€Kó{ßšÅàÛº™û+Ç„€œàØf~Ú¬zlçâY¿÷œ&C$­4Ÿ¤o$q¬än]:wëª#%û(9xÇXv•Š°ÇåĞb¸¿+ŒíMå19¬bÔä¿Øoˆ-\ÎÎşT&2Ú¤¨û‰
¶†[µ»>Œ‹ÿùKÓå¡úáG®¸µVDÓØVÆ: úö¶³EÙ µ]œê+Të)$g«®­ø(mŒjç];§–/ùÉ”‰Lø€bFü”‚/ÀÛõ1]ÿ`–¬(o]l;6§»ŒĞ€ï$
ñLïx"İäÑ°!P^!òª™¢¯":pß”îš+ÜÑ:¾4Q:m£ÔU¸ùPVÆ%N»Éõ^Ü.mVnª‰œ·j{±Ø
|·škzöÄ!TÕ»5Ó	ÜÜ §Ù  QŸÑg›LQÊºÖÂá¼ÜA¸Ù¾•[b¯K¢#cqJ»ìªÕÉ|s8 µ.`êe!J#K84ªÈÄ6ãs¦ŒÚB“O¬şVBÁµådÿœF‚8†"a¬“w­øüo`½zªIõß™qF†í{îDæ‹¾àŠE(èÓØê¢§CÏ‚÷K7¹CYÖjşt6¯ËyÔB°Ã+RK%©(’_VÈ¹£ü¹H°aS	Ï/Û{ñúâÒáÂ£Ã$†VÙD’àv44üÚbV—›$,(rz€÷$	MÑ×î‰U•c“Ó6”ìÔ©ØÀÚhÈ`¢úV§@šßÑ¼Ïgÿ]kX!@“E8Ï©™N•ck­—‚ßhçå,”Móy’?%
s8|~8$uºxzcßÏ*~¨ğÀyX:)‡ Ëyş<äWâqİ•ø;gnV™º²'óô8¾ı¼²ËEuGåals0FéM²UË^;ìŞt¶‘sö‡:Å$/XíµÍwlóç|WºoôÒM8k3&çgu·Ü€  	: c!«    ¯!
ÿÿÿÿü“&A`¸˜*…Â‚0 HFa½Jï®êêu¹u«ËšÄ”Š¼–Î…½z¹u_îJxp·wOAz9Úé.6®ÇöÔeÛôìË¼»Ö=Ï¯=øâ­eğãÑÄÛqÛ÷w´²z÷şñ*«›¦¥ìXíÉ¯˜LÆõaÑ÷!Ì¶Ä«vÌõÇô/ÄnLº6F‚sq7é¶2E[4 €äŒí[ˆ„T…a X(%	…a" LJÂAW»½«ãÇß6®¹|ŞJûkö«®9“'CÖj·‘±ô::ÎïOÚëüşt{<Í÷sê%ßË>oó§_/“ş½oóå¿P şa–w=^!şWNˆd/ªwÀ¯?üÀŸ Ë÷0Ï6U/Íj»dAßà‹ù­ÇX}îNûD9…²…aOáĞÕË‚ø)æQzå'*E)Ö:mØµãâÂş»²ó]Ïû¡À  n u!À    ¯!
ÿÿÿÿü«ÅP`,Â@°P*	Da¥äûxÂúw©£Œº“5T”è/íñáÖßPå=²qì§¦½
Åç†w§o€MYªÃÙ¾Õ±ŸÓ÷píğÙø*ˆ¾?²ØN Ë¥ø3Æ†·5ÅxêD/ò‡üöêÙK¥{Ûuã>ş½$½)fDÖÌs8Šj}óAåXØÀ¢rNÄ3"æ "àL
Á€°`,#
ˆP T(
Â  LB3„Â­gšªŠâ‘^y¿×í‘W”é3B8¯g/Kyÿ>şÖ4Ùåk¯v}ßìøØn=®veÉÿOü?Äü²pÓPRX·2ˆÊÿIØ ¿ÏœĞ_ßï³ÄË?Ÿ³Nø­z9šzåô‘¿y]ÇÙ¨Cğ¼œüoÌÎÒİIé)É”o“yy9¬µÒVÛJˆ{ïVÂ: Äœ"'ìrâ'OZ‘bı$àp  €	 ş!É    '     õ·"¿’9Q<pj^aó`}‰ı`€k¦ÓeƒÀ%¢ùI h¸ˆö_Ê´«+%èˆîDeÖ
M®Püc¸j]’LqúkÅ™X”4˜±È`£mlÃrŞ­gzPt$ŸØtoşQøAü£Í,W”Î?k­˜
ÏNÒ:WbE#o2k³8±ô3‘Wµ\5‰\ÑÖOhmq»Áp¹:P^4×ÁR©róŠì—*lPæhÎ`¼ÅYú#h:`éÌlŠ@ëÌ%iÙ'š­âKİºÈ.0!N¬±>m<Ğ©ØœK£%ûØH%‚Orx‚íÎ+½EÂˆ2)Åm;ì?md²ÇMHÿÓõ±íQ²q\5á±@Éš_¤3ŞolÈÿÙ÷É{¶“êÒs˜b	'ÆWÍ€“Şº!k¾:f¦+ÈM²p‡°àt«F„|öŠÛ}ç¢L]-¯¸ıŸœ'!ìwKÉá9©0â×ü†A6¦/Gñ§Ï¥}¡Êexáàtš+˜ï’’~¨ÿ-¸^91Ä·®{D¬¥H©2|Î]WÕİJ^â;Ï}ÍEànØõ#óÓ2=O)(PNYx‚ÚÇ‡o?U†¥}uxpYÿH lo8ô…“ÉtF[ÎË»Ù  	 `!Õ    ¯!
ÿÿÿôƒÃH`,d
‰a!‹UÍÌÎµ“‰ÏÆ¦âUÕÔ•V^‡…÷{kõ–¢ùvİEÇg¾v¯B+=5ßø\ÏÖ¬’~¶NM}+¾åã”@voÔ/(«*èzô‰¹ÑõNS>ØôÏ‰èµOÈ™=ä*P¢Ô;ÂÛ®àB\²Té‹ Y{NúVT[DË/Bs/¡ûØ	"RW#rU×CÓ "Ø6#…PTHBÆ¢˜†Z­Ç7—N¹²yÇ6¢µyÃ^4=ÿog§ú³çÿ™¥"Wk÷ËïÏ‡%Şßmù}©~îßnØ®+á®­¹Ã^¦¦hj¼ …“¯i'òçbûù{×ö€Wã»= só¥¯ÿEÔ[‡ÁaCèr-Ù5:Öş(ƒ™Äı6ïË9HëUj¿˜6²7Z
Ÿ‘gEôB^WÜ2û€ Ÿ¤ynEüSâ¢  k ]!ë    ¯!
ÿÿÿÿü£Â ÈXp‚A@¨$!rNnwñúË´¿3%ÅUÕªª#È«Yh¿^ú_T½ÛpüfŸ>¯ÉÍ¿á‰÷üs»Ôƒa—şïÀ		while ( bitSize > 0 )
			{
				// Put the input through compression if necessary
				
				if ( inputTree )
				{
					RakNet::BitStream dataBitStream( MAXIMUM_MTU_SIZE );
					// Since we are decompressing input, we need to copy to a bitstream, decompress, then copy back to a probably
					// larger data block.  It's slow, but the user should have known that anyway
					dataBitStream.Reset();
					dataBitStream.WriteAlignedBytes( ( unsigned char* ) data, BITS_TO_BYTES( bitSize ) );
					numberOfBytesUsed = dataBitStream.GetNumberOfBytesUsed();
					numberOfBitsUsed = dataBitStream.GetNumberOfBitsUsed();
					rawBytesReceived += numberOfBytesUsed;
					// Decompress the input data.
					
#ifdef _DEBUG
					
					assert( numberOfBitsUsed > 0 );
#endif
					
					unsigned char *dataCopy = new unsigned char[ numberOfBytesUsed ];
					memcpy( dataCopy, dataBitStream.GetData(), numberOfBytesUsed );
					dataBitStream.Reset();
					inputTree->DecodeArray( dataCopy, numberOfBitsUsed, &dataBitStream );
					compressedBytesReceived += dataBitStream.GetNumberOfBytesUsed();
					delete [] dataCopy;
					
					byteSize = dataBitStream.GetNumberOfBytesUsed();
					
					if ( byteSize > BITS_TO_BYTES( bitSize ) )   // Probably the case - otherwise why decompress?
					{
						delete [] data;
						data = new char [ byteSize ];
					}
					
					memcpy( data, dataBitStream.GetData(), byteSize );
				}
				
				else
					// Fast and easy - just use the data that was returned
					byteSize = BITS_TO_BYTES( bitSize );
					
				// Read any system packets
				if ( ( unsigned char ) data[ 0 ] == ID_PONG && byteSize == sizeof( PingStruct ) )
				{
					// Copy into the ping times array the current time - the value returned
					// First extract the sent ping
					PingStruct * ps = ( PingStruct * ) data;
					
					ping = time - ps->sendPingTime;
					lastPing = remoteSystem->pingAndClockDifferential[ remoteSystem->pingAndClockDifferentialWriteIndex ].pingTime;
					
					// Ignore super high spikes in the average
					
					if ( lastPing <= 0 || ( ( ( int ) ping < ( lastPing * 3 ) ) && ping < 1200 ) )
					{
						remoteSystem->pingAndClockDifferential[ remoteSystem->pingAndClockDifferentialWriteIndex ].pingTime = ( short ) ping;
						// Thanks to Chris Taylor (cat02e@fsu.edu) for the improved timestamping algorithm
						remoteSystem->pingAndClockDifferential[ remoteSystem->pingAndClockDifferentialWriteIndex ].clockDifferential = ps->sendPongTime - ( time + ps->sendPingTime ) / 2;
						
						if ( remoteSystem->lowestPing == -1 || remoteSystem->lowestPing > ping )
							remoteSystem->lowestPing = ping;
							
						// Most packets should arrive by the ping time.
						remoteSystem->reliabilityLayer.SetLostPacketResendDelay( ping * 2 );
						
						if ( ++( remoteSystem->pingAndClockDifferentialWriteIndex ) == PING_TIMES_ARRAY_SIZE )
							remoteSystem->pingAndClockDifferentialWriteIndex = 0;
					}
					
					delete [] data;
				}
				
				else
					if ( ( unsigned char ) data[ 0 ] == ID_PING && byteSize == sizeof( PingStruct ) )
					{
						PingStruct * ps = ( PingStruct* ) data;
						ps->typeId = ID_PONG;
						ps->sendPongTime = RakNet::GetTime();
						
						Send( data, byteSize, SYSTEM_PRIORITY, UNRELIABLE, 0, remoteSystem->playerId, false );
						delete [] data;
					}
					
					else
						if ( ( unsigned char ) data[ 0 ] == ID_NEW_INCOMING_CONNECTION && byteSize == sizeof( NewIncomingConnectionStruct ) )
						{
							Ping( remoteSystem->playerId );
							SendStaticData( remoteSystem->playerId );
							
							NewIncomingConnectionStruct *newIncomingConnectionStruct = ( NewIncomingConnectionStruct * ) data;
							remoteSystem->myExternalPlayerId = newIncomingConnectionStruct->externalID;
							
							// Send this info down to the game
							packet = PacketPool::Instance() ->GetPointer();
							packet->data = ( unsigned char* ) data;
							packet->length = byteSize;
							packet->bitSize = bitSize;
							packet->playerId = remoteSystem->playerId;
							packet->playerIndex = ( PlayerIndex ) remoteSystemIndex;
							
#ifdef _DEBUG
							
							assert( packet->data );
#endif
							
							incomingQueueMutex.Lock();
							incomingPacketQueue.push( packet );
							incomingQueueMutex.Unlock();
						}
						
				/*
				  else if ((unsigned char)data[0]==ID_SYNCHRONIZE_MEMORY)
				  {
				  if (byteSize>2)
				  {
				  packet = PacketPool::Instance()->GetPointer();
				  packet->data = data;
				  packet->length=byteSize;
				  packet->bitSize=bitSize;
				  packet->playerId=remoteSystem->playerId;
				
				  synchronizedMemoryQueueMutex.Lock();
				  synchronizedMemoryPacketQueue.push(packet);
				  synchronizedMemoryQueueMutex.Unlock();
				  }
				  else
				  delete [] data;
				  }
				*/
						else
							if ( ( unsigned char ) data[ 0 ] == ID_DISCONNECTION_NOTIFICATION )
							{
								packet = PacketPool::Instance() ->GetPointer();
								
								if ( remoteSystem->staticData.GetNumberOfBytesUsed() > 0 )
								{
									packet->data = new unsigned char [ sizeof( char ) + remoteSystem->staticData.GetNumberOfBytesUsed() ];
									packet->data[ 0 ] = ID_DISCONNECTION_NOTIFICATION;
									memcpy( packet->data + sizeof( char ), remoteSystem->staticData.GetData(), remoteSystem->staticData.GetNumberOfBytesUsed() );
									
									packet->length = sizeof( char ) + remoteSystem->staticData.GetNumberOfBytesUsed();
									packet->bitSize = sizeof( char ) * 8 + remoteSystem->staticData.GetNumberOfBitsUsed();
									
									delete [] data;
								}
								
								else
								{
									packet->data = ( unsigned char* ) data;
									packet->bitSize = bitSize;
									packet->length = 1;
								}
								
								packet->playerId = remoteSystem->playerId;
								packet->playerIndex = ( PlayerIndex ) remoteSystemIndex;
								
								CloseConnection( remoteSystem->playerId, false, 0L );
								
#ifdef _DEBUG
								
								assert( packet->data );
#endif
								// Relay this message to the game
								incomingQueueMutex.Lock();
								incomingPacketQueue.push( packet );
								incomingQueueMutex.Unlock();
								
							}
							
							else
								if ( ( unsigned char ) data[ 0 ] == ID_REQUEST_STATIC_DATA )
								{
									SendStaticData( remoteSystem->playerId );
									delete [] data;
								}
								
								else
									if ( ( unsigned char ) data[ 0 ] == ID_RECEIVED_STATIC_DATA )
									{
										remoteSystem->staticData.Reset();
										remoteSystem->staticData.Write( ( char* ) data + sizeof( unsigned char ), byteSize - 1 );
										
										// Inform game server code that we got static data
										packet = PacketPool::Instance() ->GetPointer();
										packet->data = ( unsigned char* ) data;
										packet->length = byteSize;
										packet->bitSize = bitSize;
										packet->playerId = remoteSystem->playerId;
										packet->playerIndex = ( PlayerIndex ) remoteSystemIndex;
										
#ifdef _DEBUG
										
										assert( packet->data );
#endif
										
										incomingQueueMutex.Lock();
										incomingPacketQueue.push( packet );
										incomingQueueMutex.Unlock();
									}
									
									else
									{
										packet = PacketPool::Instance() ->GetPointer();
										packet->data = ( unsigned char* ) data;
										packet->length = byteSize;
										packet->bitSize = bitSize;
										packet->playerId = remoteSystem->playerId;
										packet->playerIndex = ( PlayerIndex ) remoteSystemIndex;
										
#ifdef _DEBUG
										
										assert( packet->data );
#endif
										
										incomingQueueMutex.Lock();
										incomingPacketQueue.push( packet );
										incomingQueueMutex.Unlock();
									}
									
				// Does the reliability layer have any more packets waiting for us?
				// To be thread safe, this has to be called in the same thread as HandleSocketReceiveFromConnectedPlayer
				bitSize = remoteSystem->reliabilityLayer.Receive( &data );
			}
		}
	}
	
	
	/*
	// Statistics histogram
	if (time > nextReadBytesTime)
	{
	nextReadBytesTime = time + 1000L; // 1 second
	for (remoteSystemIndex=0; remoteSystemIndex < maximumNumberOfPeers; ++remoteSystemIndex)
	{
	currentSentBytes = GetBytesSent();
	currentReceivedBytes = GetBytesReceived();
	bytesSentPerSecond = currentSentBytes - lastSentBytes;
	bytesReceivedPerSecond = currentReceivedBytes - lastReceivedBytes;
	lastSentBytes=currentSentBytes;
	lastReceivedBytes=currentReceivedBytes;
	}
	*/
	
	return true;
}

// --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
#ifdef _WIN32
unsigned __stdcall UpdateNetworkLoop( LPVOID arguments )
#else
void* UpdateNetworkLoop( void* arguments )
#endif
{
	RakPeer * rakPeer = ( RakPeer * ) arguments;
	// unsigned long time;
	
#ifdef __USE_IO_COMPLETION_PORTS
	
	AsynchronousFileIO::Instance() ->IncreaseUserCount();
#endif
	
#ifdef _WIN32
#if (_WIN32_WINNT >= 0x0400) || (_WIN32_WINDOWS > 0x0400)
	// Lets see if these timers give better performance than Sleep
	HANDLE timerHandle;
	LARGE_INTEGER dueTime;
	
	if ( rakPeer->threadSleepTimer == 0 )
		rakPeer->threadSleepTimer = 1;
		
	// 2nd parameter of false means synchronization timer instead of manual-reset timer
	timerHandle = CreateWaitableTimer( NULL, FALSE, 0 );
	
	assert( timerHandle );
	
	dueTime.QuadPart = -10000 * rakPeer->threadSleepTimer; // 10000 is 1 ms?
	
	BOOL success = SetWaitableTimer( timerHandle, &dueTime, rakPeer->threadSleepTimer, NULL, NULL, FALSE );
	
	assert( success );
	
#endif
#endif
	
	rakPeer->isMainLoopThreadActive = true;
	
	while ( rakPeer->endThreads == false )
	{
		/*
		  time=RakNet::GetTime();
		
		  // Dynamic threading - how long we sleep and if we update
		  // depends on whether or not the user thread is updating
		  if (time > rakPeer->lastUserUpdateCycle && time - rakPeer->lastUserUpdateCycle > UPDATE_THREAD_UPDATE_TIME)
		  {
		  // Only one thread should call RunUpdateCycle at a time.  We don't need to delay calls so
		  // a mutex on the function is not necessary - only on the variable that indicates if the function is
		  // running
		  rakPeer->RunMutexedUpdateCycle();
		  
		
		  // User is not updating the network. Sleep a short time
		  #ifdef _WIN32
		  Sleep(rakPeer->threadSleepTimer);
		  #else
		  usleep(rakPeer->threadSleepTimer * 1000);
		  #endif
		  }
		  else
		  {
		  // User is actively updating the network.  Only occasionally poll
		  #ifdef _WIN32
		  Sleep(UPDATE_THREAD_POLL_TIME);
		  #else
		  usleep(UPDATE_THREAD_POLL_TIME * 1000);
		  #endif
		  }
		*/
		rakPeer->RunUpdateCycle();
#ifdef _WIN32
#if (_WIN32_WINNT >= 0x0400) || (_WIN32_WINDOWS > 0x0400)
		// Trying this for better performance
#pragma message("-- RakNet:Using WaitForSingleObject --")
		
		if ( WaitForSingleObject( timerHandle, INFINITE ) != WAIT_OBJECT_0 )
		{
			assert( 0 );
			printf( "WaitForSingleObject failed (%d)\n", GetLastError() );
		}
		
#else
#pragma message("-- RakNet:Using Sleep --")
#pragma message("-- Define _WIN32_WINNT as 0x0400 or higher to use WaitForSingleObject --")
		Sleep( rakPeer->threadSleepTimer );
		
#endif
#else
		
		usleep( rakPeer->threadSleepTimer * 1000 );
		
#endif
		
	}
	
	rakPeer->isMainLoopThreadActive = false;
	
#ifdef __USE_IO_COMPLETION_PORTS
	
	AsynchronousFileIO::Instance() ->DecreaseUserCount();
#endif
	
#ifdef _WIN32
#if (_WIN32_WINNT >= 0x0400) || (_WIN32_WINDOWS > 0x0400)
	
	CloseHandle( timerHandle );
#endif
#endif
	
	return 0;
}

/*
  void RakPeer::RunMutexedUpdateCycle(void)
  {
  rakPeerMutexes[RakPeer::updateCycleIsRunning_Mutex].Lock();
  if (updateCycleIsRunning==false)
  {
  updateCycleIsRunning=true;
  rakPeerMutexes[RakPeer::updateCycleIsRunning_Mutex].Unlock();
  RunUpdateCycle(); // Do one update per call to Receive
  rakPeerMutexes[RakPeer::updateCycleIsRunning_Mutex].Lock();
  updateCycleIsRunning=false;
  rakPeerMutexes[RakPeer::updateCycleIsRunning_Mutex].Unlock();
  }
  else
  rakPeerMutexes[RakPeer::updateCycleIsRunning_Mutex].Unlock();
  }
*/
