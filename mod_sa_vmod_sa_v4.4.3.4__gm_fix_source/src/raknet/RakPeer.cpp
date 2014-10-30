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
 
 // If we don't specify a secondary identifier, then the list j�<4�z�_ԏ�ѱ��ש�g:����I���g ;]���T�m=�(���wO�w���e;����9>x��:�3�o���,��t�g�b������ <��K�@��  Y S!    �!
��������a�`*B�`�`(	��b ���fu������}����J��j��j�Y�_9����^�?��7=�Q/��^w����$ˉvQ��Y�'�w�5�jK�]��5�z6��3jϭם�8_�r��V�M�rKc"�b�,Ę�U.N`��R �`��PJ	��A(P$1	B& �R���*g�g35͕%q�2�M��������f�y��ҟϧ���k��1�� �[Kf��}�/�Z*'z�eF(S�O�2��ޒ�Kg���;��P��;���M����V�s��+r�t�,�d����E3�T�l��&�����U� %���R3Ş���.  ^	 �!    '     ��5"�A�$�}m�]���k�&F���i��%%���ր���D<t��K�_D�M�}�k���,r�����:�{p���tҶu�� V�sqSZU���:�k�Y��@y˼2�D��),� �.8,^l�8T���:K� �qW��h�!k]�&o�n�?��������M_�x]b�ч����ՙ�]r|������Q��*_�Ϣ�$�e"mT0}V�
�sU�V����>'�D��IG�ŋct+��ī�"7y�XUǄ�F�6�� �qY��2�!
�.��v�ا�W��8��-Kl� �*����7�ǽ1{e����ۜ��sftA�Ñ!���[��Mv�)�L��5�;��ؐ|�	����mU'Tl����Ɯْ1o���	L@�4�K���\�j��d_�Z�۩2����90���,q�~��3��@WVyK�81������A,��a�����*p�*X���0��n~%�ˁ�������   N!+    �!
��������0`HD� ��D�[�n���v�~7�׵��r�"�Yr4��)��N���R=�U����t+Ot�Z`J���͟����]rS����5�N�g�A������h��e��q���ʤ(��H됢�����tXF%kA>2xRPJ)�Ā�`,g	�`�P*a �L"5���-����<���U��T�U��~�n����>��u=��������53���\��R���7���	�м
��G���}�xq��?�����"().��-���dޥ��ʘ�Ϣ�?F����|��M;�k�
�O��,D#�  Y	 	!>    '  ~  	A�$��0�_W���J��h�{�N�'r����c�C�F����]3�|(Qɒ:��%J�1ò�Ӗ=��g��Զ��C_�l�0H��%ͬj��6�漯%k���)%r �A������P� ,ҳ�'�~��p
��nf*����p�Ӷ��j�(�I_
]k�X� �"�X;��ڑ�Ղ�{����������Î7|pq���˯7��?�:At-�QՓ��C���3~R��M�m�)8�Ϸ�0(�������}I�MM�@�*?���|ɨHq��X�n�sZQk�,�ӈ�V��u��7�^�h��h��j�k���Cۥ���ʃđ�N��(�q��P�d�G��b�6ݓ&���PǠ-�f��,K�x�:� EQf��Su
�*"Ϯ�PՎE���9`����C;tL�X���!L�X X��c�uEW�\3]{�_3./�֕���ؔ���~�eE����l��)�8Π�p���a�PDs'L�!,/���u֓�~�&�-�Y 핺3d́���8�x�k^lј�c=���<��;?����ϗ$��챜!(	q��%o���/B����C�eA�wEr���5�b��i�!-�иpm t��T��L�m�$�.E\O���T0Z��o��2��|�P�	�L���=���8����.6�d�z�_���	�a1\G�}��v�c
w˟��������ą��R��:���ޞB�h�V#�Nr�Xt�8{@-������jI�h��Y5�:� CJgSG3{'f ��*�[=�Ag�`C6���3��(`*���A��Q"�� Q�;��IH���$�yD�~G�
��� -���Y�5�7�gwC�]�$�w�H@�g��C|+����U�v�/�����b���3�C��D�Q���
7 %�>P"�Ht�k��b\5���i|��r��$�_�gTW�	��d��Wf֍���é����Ū�`��O�1i*l�"����q��߳=�������e�m�����!�]�~���n�?%�42����k=���*4�Ov>��kx;�!�#���=�lf0cKfwA~�`b<��t9�$Ya�U-MBYŧ�\��[H\��'�됃L�U#�P�){�T��Ȇb�/&52�^�&�Ɩ{�1_�\	5](d�Y�xrPDA	%ϓ*<ׄ�~�< P  �X��`�>����|�삏d:�_W�����	�>[��F��H�� �_?�����[剺�-q|�W���pW~���]�u̓	D_������o�P�mg���n�y��F�1 �z������E������}}��'u�	IyYz�B�M�BJ�9%L��9�ނSJ҉q���b��dC��<L��`'C�T�J)i��[�g�>�\z3�(��D��˵���*��a��x��d�I4�Dvo*?V`(�NC�6�,��9��?���_�p�T�����!�EB�M�x������Fj�x�@�Ԩy+;^��4_�H+��Yg�="c�ֶp�$�^����|II_����HK7G�������o��K�@�!� ip }޶��.�.��
$�|�@�H\� �}��_��9FZ�t
�n��K0#6&w,}����Ԅ���C��d�U��K��$9/Ʉз@򴟁�;�05�d��S���ϸ�C��QcSw��=o8	����'�U�X<���A���}'n<��I'd���P(V��C�������8;l7ԇ��Mǅm
_��9�ʁ0%̲����.�K������e�k�oz>��nӑuUe�Gɾ'���<�S�;����cZ�L�F`�[��_�N ."�r.G��1��5f������R5�����fʢmŋpj��Ơ�1p@�!�n��j�'bZ��'��:d��%���[��2h���'��q�|?�H��rk>���ٷ�g�r����}�V����=mm�� �H���)���2-A�ek���3�E���nTk��Jsd��Ԙ��T�0{5U)e�Y��>�q�C V��W��\�M��G�����o�������D�?>7�`��K����=�W�"� ���r:n���.��LV��Y< ��V�.ԍ�e��aʺF�F�?s熋��� �7��O��S���!�嘸5Ɉ�a�c[g�յ�
���M�kux�kr>����)MJ��E(���Z����cjjS���|��0�:$����H3fߴ��2��뼼��N��Z�T��I�Å�{�r|������֊Ū4�����s!�lOv
������宼��)�$y����A���A  	  S!@    �!
������	�@�`,	!@�T2
BA@�D$r���}~���w�λ�W[�$ި�]��_׫���Нߤ���ǌx�0?A`�]x~�w��qG���#��{��������ҫ�2�ƿR�h�2���s'�K�BUYv�B�SKb?����Y$Q
���A0�H�
C0��uu8���oۚ�*W]�K	v�CW:����/�vʟx4wh�����k�~�eٟ�A?պ���nΩS���/��\�� ^}o ��)���%�B7�Y���6�y�����{��SA��D�-�����Hc�w�o���?���҈N5&�j&�$P-�  ^ h!U    �!
��������@�PP&����XP�¡!�H"��_Ƕ���λ��y�t*�Qs\���A���?��p�����TF�p�tgMȥ�?B�W�y�������
���"?
�k��[��u�NԆ�-$U���>�Ƞ���.��ڵ1�0�����W�5�p��[�L	�D4�%0����,H�A(�J)Ba�D@�s$��i��|n|=o�c%_M�	Y�\O����5����K��͎`P�UH�����I9N���tֿ=>����@����������� 45��h�f�]a��?)�g�u���S���ޘ���_��-���<�S/Õ�2W>���db��|z $@O��	�V8  s	 �!h    '     ��7"�a�9�������4��
�ɎyG��L�+��4���o����/*ln�*��~�䢩��y!��)8���LP�z�Fe�/�X�Y�&2OV��m�Y�"�C-Z�md0.�~s;3<�Sh�&��G���щ�Ά8E�A?���*\:g�?rv�v�$3�l�+;�����U���)`���(�!�Ͼ�B�R�V��="�bb��(م˯GӉJ)]�`�l�K��w4�=^�iU*���ˢ���L�+[V����R�!��(���(ix�lq�aD/��d���DeL@�~� ���e�r@�*D���w7P01]/\�cދf6����u���˨�� Of�����D��u��j��d�t�<�/������Sm�^��1]���{"u�X�P��$�������<3)��/�H'�W�-N�\�Wy�R�#�=������H�*#�t�̞XJՁ�/�KT�2��o�9��P'Zjg2���{I]n�P:^�   p!k    �!
������ŁHX.��@�P$5	V�/o?n*�qZ�ᾅJ���wwq�7�~3�o�]����xi�Z���� ���$���U۸�Q~��H��L���?�ڟ��ͷ���B��?lK�s?&��V�x��Ѐ����X��i�h��|[+�[�'|s*-Ie��^+�PYfy��p6�c��,$B��!P��*�;���e�j���(*�W}w�Q���t��_����&�<����ע�'���:�{�ǰ�����0=�7{��/��Jx�v�K����O� @H�{_���Rx?}4�~�o�?��� ��V?p}Wz.]�{M-�I�!f�o^����u����-���E��ӂv�� %�'  { h!�    �!
�������@��.�B��$%
�+0��>'>��'>ӿ5���	�i�7g&ޓ���Z=k�^���ށ����v�~����ƛ�����7��~O�����իN��sS��-�՞<y�a�#8P;涔>�_�R��-�n{�R\�X�ɥ0w�BR ���`�XJB�0�HJ��#0��(�K���čoX�~.���}H?�������Ǻ���~�������:!*%����ɬ�2y�;�������P]�������x"y�W���j	QiO��㖂�f]�f�?'�����(�*��<ת!z�=	\x�_�xs����l�� ��UA�  s	 �!�    '     ���"��ΰ<�~�My�����A����"	�_���ħYTG�*���(���oE��NN�YCwE4��F�N�8��~@�R%�ޟoU
Adfe�K�l�vK�|�ZK�POO�!�{���>fg���Zv��W��٧��D�e��<F�OoUPS�`U-o0��lG)g�7x��GD�6�`O
zHm�V��!̉=󧔜}C�T��cp_�f��Ǯlp�o'��j̷&9;�ho��r�S؉�{��m�N�"r�5�P�.>�"H�V�!��~��.���^EO��I}��ψ�\��^g5nƅv
�^�&?�ʢmb=&{�
����@W�E7��Ր��B�>PR|y�Es���k�;�f����:�i��=��h�k���c��V�<� ��¨�����i�{3����������Hـc����o�O`��F�"�X)���n��&�'a0��S��~#N5���&�4�Ï�  � g!�    �!
�������@�0��P�PN��!!
��Ug���i�j���I(�\��h꟡�B��������y>�M���]�9��zeҕ��u�:��#:���Ey��as&`���a�!2t��%@Ӣ W�8N��mS�B�ʰ��S����@|M@�,�{D�p&D��aPJ$
�ĂQT&�D�7�F�2�Zަ��ުbI�+���km��|��[�m���~��oK�n\�xW٫�6l���6��4qsϷ���8��?��:C�}c� ><{ .���W.ԲC�_o���v��7���!<<�N�(�>\ˌ�z�U�z�5�^���/:�@_k��<+'��	Z����& #j��  r c!�    �!
���������@�P.���h*
�a@�PD1qw�__��������}�iV�(\�G����Ṏ�훯Tk���ߟ�H? ��\_����������6�O�Xw}�%�b;[��mnà���6�Ph���]rx���y&$0�ZE��DV*!�(��@��2 l4�BPB�H����y&�
���e��8�jK~Ϋ���}������y���I�x8	�{?D5������~ZK[$/������}��~{�m*K�E�[���Z_��z��wytٲ��^��a��)�|8?���:&
�_���^�l��ҷ�w��c� ���X0����ssz�f�� ����E �  n	 !�    '  }  A����L)��_k����҈�T��փ��*h�K��������%�%֋uM)E��T��`Wo%�C�3�E��&ē��]��q#�����d��IF*��D7)�U���%�稔������%xQ��/�)'l^A�Эf�LZ}���lb�L/�\�8�ꐖ!����r)'2�����B�9bI�?�N�/��z�.u1��ZJ��U�����ݚ�	Xn�9��H�3�+jD�Hd�䎍�Β��x��8��!���.s�4��T���Nej�F�o��o~&�Ԧڂ�	�w��!�R�V��[��aIY8��H/�C����R�,m���L~%�'g��˒� q�rZI������WC����8h���(��V�N�� o��{6�Y(|({�R̞;n�����w�ӑ]:�g"V�Μ5�U�H����71�Uƪ�._����0� �����FM218�����Yڢ6�R����؎> �U=e�P��/J���	9;!�\�l��#݃yCD�G���uO]&�.��7uЂL����ll//U�(��$cd�����]b��7��e���+�lȈsj�<pZ|'��ԭ����'g�����H?^�l7�X֔d���؛0?�����,�C�x��Fk�a<v��HՑ�T5��q���h|�g�Q���ӗ�K�v�ա<�H��N��wE�0�.���W彦*���
�ꆱ���� �h��w�QB���ؘ��x�����P��uI���A/��4/_���S�-f��^z��[7Ȱ���3��֤��F��˿B0N�/Nכ�5;�6C w�ֈ���S�a�H>��aE��>֦�!tw͛� ������O���"�@��[c9/07�]�V&��=���n�����QY�������r�F�z�����BD�_����r0aϨ�`b-��P
1x�~��R���<��6GR�~�b��������~O�؜��	
��o}��������h���1�v���C�l) (�HDh̕�a��i}��KB�NDE_��̵dd���?=��y��97���^/��x�O��o��a6��j��ӡ2�� ��6�V2���d>5��������� ���*����/���HQEỄ�lh)Eh3Ip�l�ʝm/��/�P���!󭡕��b��p,���@D�1��x9� ��(v�
<O�/��o����+�biU�:�G�(ӎ�^G�z�Ak�{��̱0�adj@��V��a�3N��@1�̟���r#�c���������1�vb��O�;V�ϑ��	�%�)>����!�4�3�/;{9�w�\��Y��Ḧ�$Gui(�:�����h�Q���cHх��P�jt���0H;O�d��!'�o`�Ŷ-�*EdS�a����Ј8���y�7���)�_���g�E���Q��:'u��7�����G%FB��Q g�f_����B|+:��˓ v�fq��\����$_o���C�{�����
�a�l3��s�}ϱ�Po~�ǡ×�g6!O �@ٶ��hCp�RA�����{m/�a��0�	q�͟�k�d%k	ߏ��n@)@�]��'%��G��1w1ɦ�v��Ip, <��Gq�mU��WTq��M�I�J��������=������/�A�m��~�M�5��}+�G�٬氕0���*��R4.%��y1h��;W0����B��u���dU{�)�ğN�|^����t�ա����L~CZe�����U Kk��^2zWfm͟)L�z�e�\ao�Q�d��ߢ�o��;�jK�n��[�Lw��`�����MfNB���M����7�tH�:QG��A�`���yF�
����r���a	F�W"."�nǶ���uAAG����S�Zh%#)���bf�K�Rk��)�l��C <�8��T�<w���lc����*k������[Xd�i�����年��a�xڹ��)���w��c�ڞ�S_��s�����x���T��2u��`|}�lZF
ʥ���%}�}�����g{+������it������e���K  ' q!�    �!
�������@�T,8��!P�T.
�A@�D$Z�\�?O��u���ߔ���6�&�}�8�w�W�R�}.Z�=��Ц����e�6���ww���ǔ|m�s_X��2�DjI����sA�!��=J՚��H�GC�BjP��#��I�V�YBq���@�����.�@��0&B¡`�TH%
	D!0�L" 
���ʺ��ԕr�"��+�4��*?���|?���ϛ��ر��[��%���~6��{-��*��m�~{��i�e|\�ېR�3����潝J��U��b� vr�W��~��[�9��.���r>�m�ؖΜ1@p�6��%ƶ�3��#���y�ϐ?щ�DQ�  | k!�    �!
�������@�P0ᐠX(
�� �H*zK������q�ڼ����f�%䊙u������?�4&��=�V�H���g�u��Q}�i�#���w��f��]����;�SY�32����&�7���R�M휵)+C���MVf@S�B���U�H�@�*@�`�����0�L(BBb�Dhk�ԓ#X�~w�˪U�Z�b?/�S��}�ݟj-��]���>^[z�w�����g^hs�gx~M}�|�+��Z��~��_^��?�O�C�����ߟ����{?����=0M���=aX� �L���%�ӴW��)���mt����{^� v����U���j�x���р8  v	 !�    '     ���"��ΰ<�4t]�Vaxv�.��Q�w��m�M[<([>������O=��h�*.�K?��'��Zp3l��|��@{�'��,�}���������3H�@|��b��>�+?w�4������I��>"Q~�n�ӁQñ��r�_�3�
yN��]�Ž�����KkRե���s�`o�c�?�b��tM�iK�����)��~8}W�����=C�G�xZ��	�e�f�1mo �C��������C�8���Q�ll)FYP�|��"�qY͋�C�9" ���Qw�։�h�y���5k�r�:�A&y�f{h�����-� ��ޞ�Yig̝�_v0R�Sm���׹��v0�T�#��,{�D�������C �`*?�s�@t�X��/{2���ҕ��э�5e�kD5�u���������N��7E����*�s���z� �,w�ܶ�;��H���]<Y^��������\��>���+�U�Ɵ���L��m�Nt�~+�0�%;sK1�n��,v���   ]!�    �!
�������0�Xt��`�h(#	A@�E�j��_ۮ淪��������2+�"O�~�Y�Mߠ��>�.��u5�����,����ܣ�����m�PsPsЬ�k�����y��2�vF��fwW�1�[7�](�U_d-�Fm��� %-	���$n�j��.�-��@�a��0&B��C(PD	�Nˬ�}���'ǊԬԢ/\��C������'w�X����D}}����W�����y<,��,�B'�}��X�'w���<oN��������l?ܶ7��*��b���KNɻ�B���:*U{U_���lO2�O�(���[�|�� "�6�o̺�K�L*J0p  h O!     �!
������	��`�X0&�@�P�"����Ǽ���o�_y޳DJ���7:g�l0��-��{®H�����U�����o���m|[KʛC��w"QX6�D?IVy\��p��W���C�(R6���.�y�p�x��+l�"�T�PX��X
�r�`M��
P��
����c�X(��'I�~����j�[Z�$��Iv:�����k8~�>~��Q�5>���'�o&������L�N������J�	��F��񬥸�]��*`9�/�S\	.�E�hL�}67���+:���uq�o>��z�x J���|�{�-�/(���&������ո  Z	 �!    '     ��7"���y�!�T�3Jo�΋�nNP-��䗦m� ��Cs��Q�>�W�5�nh���R����M���z��>�.(L��b;APkM1�P��*�'*� 3��r�L���lO(<��AV���M!C�"�"���%}A\'�Ob���G.��po�_K��`.1p<�f~�Ԋ�b{1B��13�7I���7[��N�)j�1��&d�+�*/�Yy�Ò�Uԁ�yH|ƙ�|Mg4z���^O_o$�?T�)�y�@ۺ{w ��Ss�v���\�kF��Κ2@�9c���iml�+��h4�Ѱ�B8���;��ɤm��n�j��Z-𾗫�J@��q���'�&�u ePU5�!ce��>�V�P����܊�  � o!    �!
������
�@��T���`(b0���x���U����Y���\��O#�=�]0g��_�o���I;V	��!����C����w¼�f��Oײu���*�MS���>�]����P�ق�v"�����,���I�&�ȍ7���K'(�hB������א��-6J�R����u�- "0V2��`�T,�a@�D&*�����8�T���ƂT�L״��q^��O���K���G����ݡ$��������;�ӓk�����'(W�5rM:����^ӝ�`�v��i�L0��r�?���2�v��e�Eo�9�킧�Q���;Ĳ=�������	$)�L`W��1%���\w�=���2��  z q!+    �!*������
Ł�X0&�@�PDQK7�y�}�לw��ޫ[��y���:�}�(w�u��-��4r�wj@^T�k��:�������5����|����x��kF�dϘG,��i�_Uk�Iګ���ZL<��,���*o�J�}`�d�;�b��Ø��x�^�q�c�Sޱ��H
�H�>�A�`�D�`�TD
��P�DF!榒L�Ǎu��m{�J�\�ͦ�>����I��h5��z�w�R�ҩ˴��t�>��:{F5w���_m�p@փ���i��~<�=�Y�WG[���s�rʾ���Q.Ʒ'�6� ?���>{y��Ɖ�[�#@^ ����� �v9Q��Ǘh�΀�!P���/�/��
N �  |	 �!9    '  }  {A�%��L)��.O0�	�w{5!�m���.>��n��-�v�<�)d� M��T��L�K~՚������� ��LNHe��f��m<�C�yW�4fhi�>Q>��w�e��㜲c+Z��&)��{��WlWr������=y��pm$X�~�B�ם�`�~�H1�p'E�V�M��X�0@;�S����v�9��@��R�!ɳ4���T�JľCx�D�m]0�9%0���;vAO;����d�I��5xc�^����m�1�L��b_pJGҟX�=�Z*6�`�3�4�C�L����rPL$�NR�ր���L��J̸��줧�@-��к�d��pz��W�?�:�$6�􆘟g&	�2�E�/ch�d��w��CuH*��,K:_o<�Fv���Cc9�7��]�ޟ�k᤬��t��I>��Α+*�xH(Հ����m�������jn`�(��R���H4��)�ܦ��`�B:}4M�9��I��mByňF���I�� �
1��}"�6Y�����u$7i=չ��?��ih�%�H48��'`���[ɟ|���]�Id�h'zA#��@�L]��P{���ML�Ǵ���PU����7p�Ӿ*��ENq��R��}P:��5.G�T��L�C�.c%�����!_e+ZU ���>5H�b���B�q��Q�Jsb��9��ܨ*�h��lb>p��$��|��v9�ۄ�7"����-Od��	X�h�C����y٫��&?��gn�׾ܐ��Fu�?�V
���R��.�J�֞P�l�­���La��F� ��_զ.����ѿmg�7�%��{�&#�@��������?,UtG�-�Gݼ{K��O�l)Qd�7�j]+��ƻ5�ޑ�s�%Q��+F�՞+BGd2:+��7�!��/�j�J�	j�K󫠭��e�ͩ�_W�E�.�ri�q'�o������rwm]Q�8��������&n��k����к�Cݬv4|����TpL՛�
�=,zA�i=����Q���}�ŏ�ೢd���7G����S?�xW��YkKg!Yk9-�"�f�Jh`N�;�y5�'�!�9�+�C�(�ko�Scfp��_�DV�C�- �l�S'�v�
��ؾ�T���˵ߧ�]6���,����:��d���PM6�b��&ğ��|��J���Ą�V�\�,2�Fʌ�*��\��=�L��ք̓Tpw��!���Ɵ.�v,��Y�;�COO�k��U��C�?�8  *T�%P�(��
X�U�t�:��2(�cI�o��3���
��x�۰�֧i���?�����"Z7LmQQ�Gu�=��,1 ������|�V�2���ʹ�Q�1@���Y�>�L�É�Ji���Ÿ{��� 	X}^��+��d���-0{��=r��E]��Nj�ك�ıb|B�#��*��UgŪ�E>��oq;;��^I���@�+/ y�?�����'�O«@ؿ�OHb�F�͆� ̈����K76�/,�]�	���$���P���Ԙ�����e��/x!��Ș��'�f #���<`��_j���(�A� -+fX��V'}�Q[�V_��˃B��+SHO%����Q��e�4ȷ���/����Yw��:�K�||�i}f �bO�z#��DOh�wX��3�N�ٟ�:~��98.�]�߄�)����U��v1u��%_�}�{���]���޺�P-�Ț��(��mHth#�MB�׺�2a���S2.MM\?>� �o�ָ+�X�v�_pv(�իNȵ{�%�0��#���F s�L�=T�w�Q0D%�{�H��T3�`�ՃNo[�,q��)|��� �(�{n���$�N��ܵk���GM��P�
�u����
�WX� l�*�����)�e�=�f�^��Ŀ��@����3�b�ALt�� ?\o�|=���=�������Ə��+�8�����a)�ʸ�$�R�f���h���/;�,�z�5���=2f��2�����GuF�=otA_o��'%��?����T�c�"3�ߧ�~i���x�o��ڃ�t�}�YW5T�m�X�����2�"��fȌeN���/��V�7>�a������efcO�B�FP��;5��COͳ�&�-ձ&M  � �!@    �!L���](L�
2˞�G�0��_�;H��^�!m���cv}{�z�=����3��_�;<y����]�|�(v���@����w��#�<���99���)��i�lꤳ&���!��	PJԖ��用g�o�e��&7*��]�p՝/.(�����>J���6m0|��O��TЦ#K�_]�'K�(wګTGt@w1@(,T�2	��i]�D�ax���h����S3��=�I�t����!/�e�`�����4Z����<�"����>K��=/�4��|��|1�&�v���M2�3�\%�I$�s��ǚ�$�7� �:f�!�,/�H�BT�E�pWfӱ�v6��@>`ȜY�5��/��xkB P���1}���Pp  � h!U    �!j�������@��0�`��(2�׏f�^3GS�o�sWR/k˟�G�����9=�>{�MQ��{����%�^��A�:��~ �`����h'��Ur/��?��dN��n/��C�⾩=���d2�S�i�d�C����f�a����)8�V�2"��#j��ou�u���X� �aAX�	��!(D$ ��լJuX�ʤ�UR'UN �I��:��'���u���������_�T}��7�,ݽ��@K
z������*�;��Q����הw~��:��� �����H���&cLԒ�<\;:��i$�9�Դ?�S�/�7M�NsP���l�s&�|+��9@y�����%�7��:�,H|  s	 �!b    '     ��7"�r4t��S��DXN%�C
��z&P�fg��-�d��������,5�Ѻ�j(
�{���O$kO ����P��W���3��	��[�s�i�7�:	���� '� �P	H�B��q��� y�
4.��-
�R������2آ�S��9"6@����M���3U��� �e�.*s�6�x�<����"-�r@I�����4_��.:�l��c,���Q�(�9��Y|�.d�P��q�FhƝ��r��'��-UM>��T�^Q#��O`�Ђ�~R#ICL�����Ȝ)\�PGw��!ҏ+�������8J%�-1t���ϕ&%Ҏ��nY�c�T6�.cE*���!��V[V�I�fw���J^Z�՛e�f	q���������Y��^M��B��'��upt��$4��9�\�A���0  � K!k    �!
������Ġ�d0B� �Hb�y���ޞӞ3X��k<��|A�XF���d�=q���?�ɴ��~������ԉo�j�H̆di���R����{9���76�N�`<S{��Q|�+�����&� �Z$��(��J�q@Ox���*HC!Z�"�TRĆ �Hf!	�J��I�v�W�~d�ܫ�o
〟�䓊U������/�����jӞo$���<����������poe�*���ZTR_��5�k��GM8��1� �a�#mEi}��T���!����[� �0�<�����
X;��Q4�*�))ѩ� F M �  V `!�    �!
������0�`4�a TH2��,_^���ꮳ��uI��WT+������Q=���~���!�}�s���O�m���
���4�<GO����Kh禼U�h�%�X^������;
o/^?�5��]D�\a��HbثS�䉍{Y�e�5���l��ʨL<���p����n�@��('
�b@�Hb3��z�[��Ks�ߞo5�f�_�9��@�?T�ۺZ~z ���E��;<�'��&��w��i]k�|�?�=ԡ�.�P2
�~�R����� )Ė�4�<\��{ZO�np�5�[�ѩ�fe���L����#������	�[��$��{��4��Fi��s�s�8  k	 �!�    '     ���"�<�4��&� aS4�)�¼���$ڣ��2�Q�ȇx���?[���3�G����Qo�R4��qBD�T6�`���I[�Cǽ���������YBlM�I��dC�����6�b!f�5Ww�h����-3ֻ��V��'ݨ���/�]ؖG]�E�g���D
!��?KR����\9�?HY���(=]�J�'�ۍ�"��5�Pܶ1I��i�4�`/��5N��>kh-�p�+;����k����߳�}�`n	D���X�Tq�%  S&_���Qz��^*p/�:���;2��)Ҡ��B7�����u���2��ĕ������a������:���[k-s��j�;��׿  �	��b,��m����o� x+�;-�zt)7M[��{��̓*��υ������.gtS�y�я�q]������S��Κ[�TJ�  � ~!�    �!
�������0�`r��A�H("
�+^Eg�WR����U)R�"4��_�~n�>��߮�z��J�]c�
�y��G�WʁCF��I9ܤ���)<��7Z�e�v�b�	\�����gQw'OӕC�/��Z׌�� SU$�9j�x|��0�{ Z&�� E�������*����,H
�A0�J
��B0T$2nMe\Ɣ�JI��8���Pl+|{�Կ�g��ǖoׇ��"����r�p�S�z��߳�
�*ko�`�5F���V�~��c�"�k��ƶߕu7�c�qp�%;�]�u���za�~<>�����w�6�o��/�j�OؖnT�Kf���Ȓ^��C�|��Vn�vFD�6����7�*�j�M:��  � ~!�    �!
������a@hp&B�0�Pb����v�p�V�F�d�*8�K�ר�r��Sm^m^b" '- ��I���ϡ
H�/��3�=-�"��ݴ��C��rK�@z�����x���;F�����J��;q�-z��P�3$������3vI�6��v![%���:�^]N �T���<%��`�XHC��@�Pl
���1�R�n>;��s<��湋�ѩ��,cnsq���bg�_�?�5�^�+�Igt~���M���l��|�=D�W�U�߬�%� ��jn�.��!g�(�?Әʹ�D��~�#�7S��c��δ��]����#�H�����`��GϾ��#�� +B�e��e65���y<#�D�-�I� q�+["�A"4)�  �	 
 !�    '  }  	�A����L)��/�S���r=h}�@����%W~j�<�I1�yZ;�f�l�B�D��j�f���rQ��.i�FʋǑp)i�E����OEG[�lA����N$y�oT<n���?Z���p?����@څQF$�"4��4����Q\ҡ�{Tkc���+��wZP��c{Ҫ��ض�+l��4.I>���r?��p�ʧ:�h�%v�m��L�(/��mo�#����Y�*��P,%m!jF윑��r�kyJ��7��#�f��Ҟ-L;G��U_�ǐ���F��܎�z��-�O���_^��˞�ԃ�/a��;Lԛ�Lͼ�G�:t��OSw'X]*�����۪C+�.�������:�hY��jp��V��D��(72±����2�ӿ��D��ǌL���w�Lʬ��-C=��&I�Y����0�(�,����sˊ������K�G@R��k��"j<Lyp&�OO�#I�:�|'��7�YJe�<�o	[��@W¥[�ޮ�N������V�5U탶���ٻJr�A�L�=tB8���P܋��k�|̂ؼ�;�~��v�@�`/���q��[��)���1�o|������3{�H�W�DxS����#8�5{�S����C��\��l�����L@��@a_"am	ELť$��][]� ��L�mM`XQ_.���-��/6�ݮ�u�œ�'-��C���2g�d�1H�z�G.f!�5�
&/��Ax�A_�%�K�&��̎Dӕ�_@���K��<8=�s�����L�Coπn�L"K"�����	\��ɲ�Z��P��`�CF�1#�S>�zN�YW�%>om�*���dHf������ "I��b���e�\��YM�4P�v*K��)'�nJ~�N{Y����=gp�D�"����\p:�=%��W42�䊉��DiȰ����`�����}�ݟ��ݩϋ�qЄ'��L/�|�`���B�ei�Ħ��a�\�ȓ�B�ph!��{b��Q�Q���� ���"nX'�'��\M��C$ަ�,یtiٵ�g)�Ʈ�����'j�ေ�v~��T����=V�geIĕy�Oݻ�͑�^o��v����?<fh��؞�xI�c�yn8�T�'�2��_1��6�6�����[<�ҙ����z�	�Q�}!��N�b��I/̀��r�����HR��Ύ��)*��ƠUD�Y��f��zW0�Nʵ���E��/ht�N.�$��u�x@n܍�\�i��wc,ͤcV�F���b�>�Q��<��?w���LWǀ:	;a�d>�K�%�����Ƀ�0�u�@�q�W�O8D���/���$f�I69�M���!w!�
,p9O\KG����]�ҡm�+Vw���L�5g�Hsy�2�hm޾�)`���NN0�(?i�\�g$���Ǟ+@����%-_V��� _4�:g?c�*ڮo�J;�&�'��i����fdj�ѓA�ʹ����ErZ}��	7dN��d����D{�[|X��K�\�:{�c��1T��>H���B�j��&�����T2*��H��O/*6�~���HAV���yXR`����S$l�����S]cْ�0EHr��i��7BR�x��R�'�:���]��U�=���'�,c����յ:W�I�_ JԹ	J5(�Jw�V���m�Ę����t�T�!8��Hy�5x}(��լ���h90[b��+�bWt���*�)B4���Í_h�!�c��<W�UL��$ɟ�4�(�1��ߵT�Ed�j�5F�ԑr���x+��N\�X��grT\���-BQ8+�ZבY��6��RP����p7%C.tv
c�w�h�SH_ֶ�V*�$�J;v�0d���Q�z�a�*ܽ?#����fC���P�U�t_�8>�����w�!1#����~Mq��8^�3TM�5GB{j6�݆��f�zJ�@
�	u� ���-����},��?@�0���j%��Κ���#?ND�.Jmv�);qG� 6V��+�f�@�YY7	W8�.��2�'���P�Ց�:G?b1��8��R@͎͗��Js�9�4D1��}�]��B	�gҍ��)H����8����ǣ���z��%���ܪ`�$�~�lt1j�
��r:��� ���"�^���9�Z���p?>�Y�ߕ�����֧�x�*\W�tdU�F��8��0,��t���5O���N6յ���J��Py�Kn��W�6K4¾V��n���ȐYib�E�8��?�~��v&��U��!�v$V���uN���/h�|>f�Kv�r��G�l8>f�$��B��jhe���+�z��K`��	���
��9��9>76^��.5�>o�`N=g��Ӻp.� ��L�Yd��L��[.Qb�Y6����&>q5�"�C��{<�}J�u��I��0�|��o�RWl�]<�s#�;��Zp�����.���QuY��e�f��{qm��O诊�d�X{q��W�9�	ǜ��]���i  
 ^!�    �!
���������`2��B�E����V�-��^VZ/.e���O�-�r�!�Fz�r?�Q��������醟��S9
�Mφ/<��~OK=�g��A��Ͳ��%J6����>8�)�b�`~��O���R6�|�t*�:@�KǺJ�nDcR2(R7_`�noc�X(&B�`�X(AC�JCT�޳UJET���X���/��_C�O�o����<;�,��Mzt蔔��%�r�/�~(�g��N�+�|�9p�������W7��[�޾�[�}�Oϻf1��� �m|��o?�֑���c[��m��T����.���O��B��t]���(H��H�@�<�N`��  i m!�    �!
������@��V��a T(%��-w/����ݯ�Z�3/�m�RL�ރ�p�k|�L!o���ӟz��D�'��K2�D֭	�0bv����%t8�z"l���Nii4��R�[='J���ԃ%~�7�bؙ^�$�&�����I�{���E��(@,^�) �.�`,H�@�PjAP�T(
!�[�Tj���Q��;��0����~���I~�^4���lѧf��2�n�e��펺�+��2��02�,r�����J�׺��)��O��"M/�f植����S�Ϣ���C�!9��iXPN'�D���f;���z��>+$�~=Z��;�����oܕ�-��V�����¡g6�D8  x	 )!�    '      ��"��R2�%�[l *`y�M%����5��w�IV �m�K�b�R�lk��5�]\
�1��Z��id��fA�h�N/�ھ��Ҝ;g�I�b�r����Z�;i�
�x~���"���Ћȋ����u�.�V>�^��p���$@�Ms����Q�?������&	74G�I�DA�"���Y�u��fk
�rF3�v���2�G�!oy/7�����6w���v�f����N�0�m�iPh��	�'�%Ɋ�g���O��8�n���23��
(�$,�\�Tx~N&ݚ��=���Y �G{�}�v��2����[ȵ3aT�Go����҈"��OQ8�
\_��T~4�0�c��Ǫ�/|ثH��<"$��`
֜��U�g&Je��h�D��!:-Q��u�l�]�g�9=.�<���G1k�%�<�L&�^����ȱ����n�h�[�F�٨���ߤ9�E�%��.�����ݰ�O&�f�9Ь�nD�� �@b�b���Ӽ�c�E7b`
"\i�_19!Nu!f�0  4 E!�    �!
�����	��b�d06�A@�L$	Vƪ���J�U��U��ݸ�L��A�];�����ʚ;|���~0�i��%�L�%����>{�k���%�y%]}�����^�Mj�a�4����J�����N�%(��A�R�%�Yv��!����Bv��`(�U	��rv���
�@��*���P�(��* �uw/*&���]UZ�i�f������������7`�O����Z�����>Z
���*��@+��}h) l}.0q~�u��X�3r�M�hL0���]�!�8���,	����񱙾&j��*t��˂� �K\��C�  P i!     �!
o�����a@�0��@�L(
�,No\�^�.�f�M2�$��D�F�{9����_�m��]J=	��G���Q���q���m9�>����'�:�Ŵc��к3sZ��G��ޒ�vVv~�Vw5z&1:$�ϰ+�M%3�K��J��R��u��i=�՚� !M%(ְ��a�XH
0�P,	�AQT"��" ��\w��n2:�es�|ws5����^yw]�O[���?��^n����[����ֻeӯ@Q��u�?s�ѱ�Z/��?��{+���1�w�Zo��I�ţ=�7��D�����ˮ��^I[��>�7,����dǾ��gwOP�%#o�5� `��p  t	 �!	    '     ��7"���Ԧ�+h,�P�Z���1W�}��#8k���d�a���+� '�  JX�������i!�6Qs[)bam��g/������o�9�y���4V+���	�Q���zv4-Sw8ϧ���>��S��Q1m|q	Zٽ�s2����c�-����R�1��,G-�����͕�\$����v98�ԏuQ�
mO_�B���g�$�Eͭ��SgC���>�L���8�Kj����iVpʌ��]0,ºHk��P��ly��:謝�`�>F�;U]�O���e��9k�'^Dj��C��!�_�SІ���vb9R�gJ���?�^��7n���s��T���A6ʵL�3ȴ�u��2Cw�%c�v*����0(e̒�\�bA�q��C��;	�,^f�4����q�����|		��hnd쌘$�&jh ���s�DQ$���A~%��u��eW�g����G�  � f!    �!
������X0���C�"��#���Qwǯ;��]T�^D�?��uQ���Ri3pG����~%`ɺ�����5K���s{Mw
�Z�|��Q�Bn����@������V��{�C��0�GG� #�.G8��<�M���S32��i�Zs����	��Qe�4�R6�"\#`�D�A(P&
0��F1��8�}su��^]u�ֹ��[j��^{��y�+���m��z�M�w�^U�%�����7E�X�L�<������ww�.�P/���@um���}��{��M��m"Y����B��'�Λ�k��W�_/�ͭ)[��l,)ʘ@?�Q	�!��1 �U�o��  q ^!+    �!
�������c@h2��(
��!H"�����}����"�T�����5��I�l��^�v���߯���S�=|��˼��������ȅ�6�-�u|��'-ܗJ�a�d�>�����>ܕ�F<��~&�����e�z"��&�2��&��c.�1W�s�l.ӥ42�+Y*��(B��!;�H��J
�	��`��*
��%0����j�z����_2Tj{/s{�	�;ͫ�~��|*���ӫ]I���uW���mK���K~Kt�iM�EB���@�cS/�b�A���Ǎ�[�~{�Wӊ�n^�󞋀/j���I�3u���^`��_ "*� l�
�G�� Ӑ!pp  i	 	R!3    '  }  	IA�
%��L)��o� "8��'�ő���4�B�gZu��T?������׷*$;��z�Ӆ�J����	}����,Z�R�pyQ����L%��=�y٧�2l �Q�ֻFv������N"x��Z�� ���7���K��ue[07ӓ
c)���w"�F F ��
.LF6`\kg�h��Fe1��!��n�ED�1��qӞ��,�(�`/�Y�����-͙��C'(�{*�HHJlce�T4��7i9���;��w<����1%*&CXT'�G�A�L�����iDm�-}�M��Hj�x~i���1o��ɽ�z��C3���JR�{��-��Td��e�[�P"�ܐl�1�C�� ��q͙���nb��z�>.'��;��eP��)E-J�(<h/�.���՗wz�]9tP��p��w�%xc�G
Ir�� dR����r�^0E������b�J1ARݛ��[�y��\��2��2^P�c�[�Rn��m�"ݒ},�)w�r�l�I7��v�[���,B�sd��^ )��jR�k����<�h�2��;�}���@Pߖ��)EG�T�L��kT�+
����W�6 4� ���p�o�݃ˬi���W��/jr��$Yz��z���1��§A��ku�1���³�r�S;����D��59K�K�Ϥ�'�p�>o��[�c�,��r���$�f�wjeli|9B�& *6������@�EP/�������qx�����-��}U8�Ȍ�`[B���
�Wu�z9P���W�KIÓ�z���P<�N$��)��������/�@���B<�*�j����SI�S6����&�lH7iGbv-�*�6�q�5�Q1�{�4;b?��E��q	�x��M=���~?ʨ!�(�Uwj�V�.S����C��F�x��0�s1a�!�pz���j�n��G�fXR#1�Ʋ�;�/j�Tu�Z�\�9D,�������M8��(͑�sh��l��e�Nf���g%`���('�Qմ=��9r�J��!�f<2���U�=�AŔ�7��xF��G�fc�� �@	.c���`*k(�}�ɈQ�4�ߠ$>:���KrЁ�wԒ�*"2Jt��F�;8sf���}�^}�Zl<�i���r9xW��U��N�P���OoM���Y"�jծ��>&4HzP{tjn���?�X�� �P��� Z����00u��8q�P�K��쒍�Z�k`t S����0��ъY}�,]�_ٿE�B�UWM�Ѷ�+�Y�-�w]��.*�j<)>��!V�\A���.����n���b�����[˱��L5�!'�%VZ�7���@n?F��r��3O�C��@��o�y�zC�×�%��0��SF7�~�x��x�-��گ�8ӂ����Y&EF���g`˽�(+�%�Q����\�g���2��<C�?V1IKԘ7i��=DR���2�0lSY�u5�$ͮ��E$�'x�!��5�le�䭧�KL-	b�����z���M>�\�.9 �8`� �3b�+̄	����ܚ=ϛ��"v�E���
��/؏���H�1�!=���K�^W�05���|y����@WAra]	�+�ц6��|�:Q{��� ��21��_:����
S������ܤ~VQ6�RyW��u�e��eG�	D`-���AW!�Cu�>]�B)���_2E���M˱�=�tc!#�ܯL��J�?Nmw����[&!��37�J��ṯB�y��B[��ƪR"�=�wOBw��	w�T��c&�S
�����#����t������ń3)�O�	���GN>JV(::�aV�ld��!�� �]��z@�_g�˼}��k���g�Nx�r�g�'`Q|d{�ը�ό�(�)T/�/xQ�`�5pM(�&�����}�����p8S:#�ħ#�}�1'~	��M/=|�	7`9��(��r�e��]	�r�D����9��#W��p�'0B��Ю�f���*��0g��q+�eu?r1<�.�(�)����U��H� ˴F�l&%i7/;ss4pN����ۙm�{���ο]*%~�)J���`�^��'3�����H�̛��5@����;z�z����P�suq�(]�/��k���n��^�͉E��3���1���(ǫk�o�kr�97��[}g�?	*$����ѝԨ���,���|AH�3Y��<�s�C�Z�>ց��"�>E8�~�]~4��n��V��ث����+�t|��W�+.J���A�b���6��k����
�۽��OےN�J}R�C�S�,�
}g��t�*�e�P�Q��V<����3�B�4������F�i!�Zu��  	] f!@    �!
������@��4��D(Hb�n����^+����*�Re�EE��F����&�C|�_��i����//f���Gq$��2�>W��f!������F�L??�lK6���G��*uD���=`}�\�<[�E�Bd�����T��"A6;<q�.4�Ii!N0�Fɮ֥]���ط�y�Ǽ`�`,8���CTH5	�Hb��?�.T�T�ݩ.mN�)��as��fn�פ=o����ו^�7�g����v�[���ϝ��E�Jt�����ia�w�!�����f�~m��;�$�������B����O��[ͬč�gՎ����c��]u�B;pO�p=@D��~�9���D  q }!U    �!
�������@�`2
B� �H(B	�B+k5��ʹ�U턔˺2.I�����W��j�;7}?�>�8|�� �K�A�u�Z?��=}�����������\"s��ՏC��kp�ބS˥Sy3��j,�ө��}��rf-��~�R����S�j"� �|;"ߖ�N��@#��M���1 L5�`�P����(D&�5��x���n�"V������}��F�Q/�V���:I�9n�]Έ�5��Fyқ�kR+���j������ɶ�Ј�޳}�?��_�?[�z8���^B�_�nV1R�˫�t醿\�Fr�����mY��W���s���,, ����?������ô �8  �	 ?!]    '     6�	7"��6�	@Q:���	�^�/��t���x�s'f�@����`��:���U7���@0�[!���'� sM?�߃�)��=����#v#ٯ�hT�S���;�}ŝ���Y�'�.��)l�V���Y���\L?����'�ݎ$<�HK�9�D�4��Λ�aF�IT��If�]��4Mu"���vy�Fח�^��1p:-F+	�2	L��:��*�b:�\�Sp��Py����~���=��;]"��ߙx���V�7�' n��+���>,l#�D��*`���]U�)�$��SB��"̳8G�{�4@L:�� !��U� :����8�^�i-s.�8
1���,��/h��5tH��e"��jQA%��j��������誙���x��yan��^�/n�;�&b��V_���u�6z���`'�e���4��'uo?��Ob�Ӟ���GZ�����oؽ�`%ǢEL� ��5�q3_�9���Vw����]5�
��ù��P�����4�Gc�ј�i�^���4�^|��5�  J o!k    �!
�������p�X�
��"
ѻ���T�I�:��%")j����;�������w��E�?|>��k_��??F��s�
��"�(���oq�|?����ȇ͹�{ub����44A���K?/4�e�fJ�_�R�(O$��)��c��M]kK
���+�Z��_���e*ؚ��i������@��,$��@�P�	��� ��"��{{��J�&��7�L��_���ϸ����w{���azm���ϻ�K��M!�5��|���m��9V����/���o��긷/� ��֥����b��V��̈́>���|t�] ����T��M�p~�d��Ʊ�n�b�qf�Q3ѷEj ����濌G��'�!~���  z j!�    �!
�������0�.	�P�H(	DA��+�o[�1��%�U�E_?W���7�z�.��T���_nF{��|���*��ZԖ���}`b�����I���9��oO�s|8�����ל��>�o:Q|H�3�R~��tf>I�B�%�5�Q�k[$�GH�8(���"%�3@���a@XpB�p��(
	B(fi{���H�Z��Zܹ�����M��g]�{��?D=iשa�������P����l�x=���Yϓ��en��a�=�b��}='�j�A��mEu3�V
�y�w��|����-0��̉t����9K��r�?�Y��m\5���'�p
�j��Y�L@���1���  u	 G!�    '     >�	�"���`~_k-�	@40e�OU�=�R�x.���������~H���P�IF�f�������i�\3�mi�:����5�͔+]��!���(�7$s��vI�������[���>���,?�D��E���8=�,Ly�s4=O�IO'N�!��E8�
=B@��(" G�J4��X�:o)$".�M	~Z��x�.�J�1;m��>��.j�_FI��U얎��F����a���TQd�-<�r,l>����mX�d��Y�-��Ʊ݇w]�DT@�.��=���Afe?�v��Xs��Q9�%so�/H�H��zPlj��%-�� �Nċ��zс�e�gѮ�w�m��U���_�	��L���}ؼ�r������T��	=��p��� ��F����dL�N�#�ޖ��-(��ϳ��=�_#�jB�ET�M1k��r(���)Ά��eG:nBL���a�Ɩg����O���5 w���ͼI��U����!DR�8�:�O��D������f�ʍ���5+�/����:l����*�����N9;��6�z���+�U  R m!�    �!
������&A���(
���AP&��*ksN��椼i��ZMȫ����ە��S���'e>�}_�uG&�z�H�:x���o�'�	������Uw��Q�&Q^o�FM��=]��WOG����+>��Z���d%�cZ�w4�×�+v�+(�H��OAi�((��,��Ah!<�� ! �4	�@�XH
¡BP$�a�_��7>8�5�����Q�o8����z������k������I�~V����]�}H�N�?����0-�l����]�YG�Q^Θ���_��PZ
k��E[��z�4�����ó�:~/��z^�}��tLY�����0?��k�q�/���8)R��!`ii�o���  x r!�    �!
������Â0`N���P�H&�T�^o��z�_}g��[���̈��s��6n���X�G��}o�D��g�G��Ц�ݍV�y|�ajݵ��G;�α�I��?���"��adǂ����Z04��>|%x���}��#����������#K耹r]�c��:!ER
s��$�*,�(є4.À�&
B�0��&�%0��㹗��$�{�WL����P�������N�*}4��o��,'?�[�3�;��������� 5���6�dq����!ɯh1��� ?�<���R[�}�����oo�n���9����9���j�\|۟�u 8�?��ۡ:N�r����� �s/Z�AQ[|�|�?���~��  }	 
=!�    '  }  
4A����L)��{l���P� I�H?������I��0=K5z�
{��셙[�_[�	��R��/�� ��>�e��t�S�����g����H��J�zza��hΟ���NS�� �fB��Z�u,ᘔ�	X�_T��|�z�g�j�?�H��Z5��#G1�8��j��v�I��نk�ь}I�p��"�O
����('_����F��eR����{��S�+�$$�x �W��
l{P���ͶM}f�=N4��]U����eڗ?��k(�JxX�o�$0��x�e2]*hyP�e��;�~"�:�����n��L��>\�?�V��	p�*�F�W_���B*�X����p���I��� ���
���h5y�s��H���
ڬx|�k/�e�82�#�n���±W ���������؂�ȁ���y��8��wö};��D���֍G<��i!�*�t:�G�~�Ř۵�W�4�qm�)@����]d�Ǧ�L|1�^݁�9��o���X��	⩶���$��6�8f^��>m.�`8��N�-����#��G�����4�{�L�:}ૌL��W	C==}y�?��ư���"�|��G��vi�[Y���I�PjGZԚ���O�[Ԉ�/K��X�W0����3ΏLa] �J��c�ң",J���8��@������H�ڻ#��}}�o���P,��:'����v��#�Cnb�Y����S)��l,w�&�y���oV_Ċ��:�/�oح����)��!ۢbL��b������u�r�p�&�V�G��8"Y��p��}�1��7ż&�\������>��8�M�QZ�̐�:0�1��̪'��8�}A��
R� ���Grkq���!F��!�P�b��q�:Tߣ��(�~lҗ�e[�N�L���2�����j"*|��c�eZ|L�3F��Y`y>ό%�M����Y)�l� �I�GN�ΐ��Q��Zs�y��!��
����>N���S{gU�����/�4jv���Lط�P_�ﱵE���w��H���(�,1�磾��e��iia��lɣ����{��^K)[~�l�l���ZOq�ϝi}��Xp�O�i��иMG=�/���7�?�����X��{�my���PX�yDw�\,��܁���k�8��^uh�ht�t2Lat��gf���xS�����{����|��Ұ���ԭ�s�JQГ��O�ŵN��1�F0���
��>_��~����k *�X�{�K�>	9�f6d�� ��#��k$d^���w�,�m����:�|��{t��z�Y��N#p�hG���p����j;o���&l���]Ɉ��ٞ�x�+|�ڳ}
��� �F�ߖ�J���2��rb���m?c��ң,�\���"��RCa4��/R��Í�O*�|�ך��=� cq��y�St���ʃ� �d&<�9ߪq\�F�v��뼣����8~-��h������[z�Ĳo1�^[Ia��&�Z� �w����v�����{�d���8j�cu8]�R��㙣1i����|�<�m�N�ϳ�X���� >� շ��{QJ�\9^bip�E�Z�ӻ�o���J����U�r>�=�� �=Dc[�W|M��78k��-��t�IZ>��������}�ph��{@����681
9K��q$�E
�Ҥ�(G���x{I�Yh-���z���¾"3p��D�rw� ��0*)��1f�8���Tt(_hf�%�h)@��3G;<�i���y�R�4�^	$�}���k�/��{�8t��紻�9���ɨ�7�^p��3@T|m�����??�ah,'"�3��Ry�Y@�F�\��0�u6����� R>�D�T$G_�u^r�F���iJf�X�ӎ"��}�<�Ӱf*�ɑ{G�ՋF�2�.τ���CJŤ�N_�\��O"�;�����pxE���R>+Wƹvܲi�Iz���s�3d_oZ��s������\P{`k������$Q
1R4�[Ӟ	~o9�E9Zl��|7﮽��W�3b��fC�*Μ�U}��v%wQ5[t����G���]��N�o���%k�Mjm��T�@�a���EH�(� _�Y���&�@

Ru՜H��&����Γ>��lX=ت6=�@�X㢙j}n>�v��f]�:�eR�C��S�8�Aɤ#��H�*X}�{��UǱI��[�W!�M
��<�w쭈J�V�"�~��>~_��qG�A8M�g8Ho�fc�{�+y�/���e�3cO���*N����$�sЇޜj�u�c��{����j���u���
Z(�����I}H� ��>#x|���ހ*�ŧw�`c�'qe��/0�tG��S������IuG��1u��D�C���`��r�V6Hu���f��0�a��&�ݳ��6F4g����ܙڈxJj��wC�����܊���kRM��n7:4*M�N��'Ʉ �8y��l����W�����`x�����EA`K�9�zF���-d�$[��<p%�&S`��='�~��/���&�M���÷N�Y"�
��!ב��������5�=p��!�Ն���l��*$gѱ��u+�>  
H e!�    �!
������B�A�hP$�A�����x�w�+�U��v��г�n����������x9�wF�r���!�W�wͫs��so�R����ʘ������vT]���J�;�n���L���5u��AZZj+%�]Ais��(1�KX��,dPJ��"�0&�a�X(��a �L
	B&0�T�U.d�T���*2�ySݠ�p������S6��d�g��zK�q��^��\wj��<����������d�����_��SF���^BC���%�����g{�	p�o.K�碊�{fT�Zܐ�An���d����:aW*�`2�����}�\�:�@�)���g��YF^˃/t8  p ]!�    �!
����������04`�PD	B��q���֫WY�p��I��%%�׆?�m��U�=*����3���C�>���_�`���r. v�)�?eB�S��W��a��
6��k�{��gU�<@;u��KH�Դ��:��a����6�&
�a��1��q,��(3 ��@!�41B�Q��B��e�x�I�<�w��a'�.���w;��]�gv}5m/j��s���w�D��|���.��Y�=%��C����;�~�O�z�}4WfU�?ǲ}�T��5����/LW�j�£�mD��]�j��m��5C��<;��>�o5}��E+��\E����,�<���  h	 �!�    '     ��	
�"���`~g�	��[y�`�i�O+��n3@b�ϬL���a���y���AZ.����&���.s�ip�8�Y�>6���E⟇�i/?�/�}_�d��eF4yXKJM$ �m�AU`*�����os&>�[��;����x��E1&��m��w��y}0"E����I)�6�=���֡8�U܆@h�-Xg��h}*�����L������շג�NUE�~�)�R�r�>�wQ[tg� P��Nr <�\���a'r%��K^�'����>�ZX�8���F����*+��R�qe@�S*S�w=�����Y��	�|ƺi���0]��Iీ�o���(jz�K�����%[��yyY���`��'5@���̣�By����Lq�����.��G��t^�dc�ǻֹ�r�4t���|3��w�X�t�����c܀1��Hxz�����k2��	�c��k� K�I���w�����0*�L�}
�m[��3q_,�Y�4���j1�0�ا��Y�r�y@ms��A>��l���?&U��J��m��!�m�_� ��c�,��Ӹ�+��4�F����g9pgs,S
���E:��ǧ��g��/�a���M�#�%����os�D�K�ej�!?��A��	�
�|�Kf��:�3vt^��wÁ�����$��ގ�b�~m��-Y�]��|��S|�l1�J#�]���  � _!�    �!
������	�A@hP�P�PJ(��g�����yϿz��.�	0N����n���>9w������ �n���A	��?�^���ߝj�{��O�W>&$7�\���>�i��㇮�����<qh-��z�by�Yއ���"zS(�Uu0�\?�� O�� .�8��CAa�X�%
BbP��(C�^H�W%Mdhʓ%I4�8�ۻ=ů���퉛�ݧ�|6�����}v}�O��Me������}[WӺ�Y���#���9g�ϻ9�3��/�9�w�[[��� ��S��ؗ�8�ϰ�uy���]n�^-̗��.������Ľ��9���1�.`�bQOH�� �o���H�Z��  j !     �!
������	�p�`4
�`�Td��,d�o���nuϒ�`�UU��	���D���g��oN��Z��x¢k���Y_�-٣R��u�_8�c>��i��p�w�|�������G���|p�nf�>Òu����.�T=�.Ԧ����I��
��.�s(�u!;��&��3�)�b@X0&��`�P,��@�F
����x��+Y5E
��.wא�Cf�}v���ɏgf���x�Zޙf����$�j?�?T�3��>�?��!��sh�ވl���ň �b�� ��Q|wZ���a�����3Uo�e�W����i׿H��O'l�Jg$��S^j����s�oM���}�rp?���C+vg�,�����`8  �	 �!    '     ��	7"�OOEK��>�T���vS6nD �_eDx�I8��P��L'�󪆇m.�D���[C�6�n(�4�����`2d=	"������%Ϙ��	��J���>i�95n�)�e�����
��������]Cq�fR:��Y���s��?;�p�1�� J���=���+
��D$b(m\�W��D��3�Pj&����������"�`i���2�)�"��}S���(ǘ�Z��Yq���Q���z���v��͍z}m���N���Ev���Ţ��"@Ĕ5�А�%�>��-
�Q͵;r1!i�*[�q�y(����z�[��Xb=��f��?H���I&��o��o�(b��1�4�i��9:jzq��{0��M
U�=���Ky;�� _;�q��'��$����F�1��"0X��G�鑄l��>���R_�O[���_2�R['z-A�X���/�3
%����4�%\j
�Ʀ%��Sშ�����9�R�>c��*:��P��r��jn�T��`Tzt�$�v���T�2�U+�@��˶��|CtF�[��:��0��H1���z�H��0K�s�mQ�����"���iȽ��uE�ny���A�zK{�2�zʹu���cR1��kV�!+R�����U.PV�M`�F�7�rU��|3v�&���3޳�ܬ�1f�Fu�=��*���'O�2K
�fƦ��	>ç�  � p!    �!
	��������cP`l7�A�P$!Y������j�7*�)*EIS���'���-�_jI��_��g4�I'�(ڎ� ��:z�~{
�w���� �ȗ���~�6��M/�ꔯ0���Imy£�d��{�V�#A��[��T�­q�:o�������$�D�n��!�
�3��K�T��&$��`�XH
��P��(2
�!0��"7:�.]�%K7kn�+�oY46�]?��~}�]ry|�&7_w�6��&�E%�o�n�������v$8??�ؚ��Y�^㻀��ۧB�)�\>dU�?����ۊ��$����Gԥn��[��kz�L����y�~��CF^�^� WV�������[��_�|�  { |!+    �!
�������h.�a(PD	�A,q�y.�η��ȫB�I4.�o���o�}W������{%���u���p �פƟ"{���Yh9��XD ��_��0*�_��2%%�u����W��a�����V��B�&�?a�H\�,"���* ��;$���k�V�R��D��7�@%�"l��`�X02	B�p�H.J�Ha �����[黉/�o��o�R�K�s�nA��o��~̚|��5����{�o�/-�S�h.�տ�t���o��O���)7���W��S�y�eO�n��.�.�c�8ߕ��F`N?*�V�ۺ.�<�����gٷ�Mm��RĞ{Zr�H�X�1۶H��E�&O�P�	�_�R��I  �	 !-    '  }  
�A�	%��L)��p�� ,�^�tU�˵eܒw1w2	�z���ѫ�P���*M|����
!0JP��K�tζ: �Pmކo}O ���������:0B|��֜#V��P:dkw�D[���]-�o��AWބ���x� lj�_{���=��87�^��Z�f�:��̿3E��_�F�`3����`�7[�#���C��@���~�50FF#�������+Ev����ܹ�}몓�bH8���\��և� ��&�q��of������l����U�A�ҙ�V�F������{���Cq�ZF ��e�cȈ_-<X����\[�uj�ȇ7@yu�J�(�����:�u�Xת޷��G~��Y%<b�ԣ],OݷԷ|�W�ts�D��P$5I�k���
l��.xȝGЗ)����wG���y��y}^z�n!�X�M<�_W��%�b�f�8Z	H�'��YX0A\�8���v#�� ;��h��ֆ��\����t	HN�uac��)S�#��-r��shb�K��n$ε��_a�������g�6�6�y��Ӄ-֚v
��6��E�վ�@��yj}*�ϳX��ou@i*��B��䌝�X�Fm���PU����F ���իlM�IF+@�y�*��(ٕ����8����Q�x��zݫ�~�Ə~�FWB���9���8��� /��6m4-ð \���iۂ���%�cA����}����/�|��i�>�(�7�3�S��U,#��+���3�{�*V�&�;���YG���X� N6�-8�!���u[>r}�"�qv�E�+@����%5�&Ȁ���,�8�#�aI	2{5��#���U�[� �g���OC��
S�@����� ��"�x����&�ɽ6X%��E�jߥ)Kd��[������8�&�艅6Sl�,��'&�gFxO�2���Q?�)��Pf~|��CZL7���.:!6CR�Ŝ��Dg���o�[�S7Gα%(�Y�J�)�a��������s'����S�\*ߌ�-+*ķ�?��	�}��vv@`\;wг�����t%<�̐9-t~�W1�Ojl*�����ND$�b�m!	��<��|�����(� � ���UOB���=���� \��V�;�T������0�vO���8�ް�9��ːe�rJ�	���1���zZiwx�W��L�T��P�\�0���$L<o2Ke�mֶ9��$Cg��z��P�gqO�dw"���"�0B�Le����NT��#.)���,uЀ��_Kt޳8��:�GN��n{`&qW�����QQ����%��F�����)�@��tC�ŷ7��B6��P&ǟ�Ȓ?�!CKB81T3߈"��>�h.��K�A�����7�#EE��"4x�}
�n�ġ�ܛyY�P�q�;P�?0�U�R�r�m��>gP27L5�ѽ������}Lu��p:�=�H�Ĭ���){�����{*K'j�K3�O���Q�${�p�LV :�N��-���������.!�)��YM�6�A0��9�K6�hm��d���]a�Wٴ�^�t�?�� E B���b�����k��B;��XA9l���r����U��?�>���f�`�g~qJ�����r��"�$p �zc�/�~ S�3����'5���~��RV%5�QꥡS���� �fN%�
T&�!P(u�4r�N��<�{PUH+'�( 2,�(U�����q� Xg�NUe�	ꈱ�o�cEs��,,��Q�W��U-������g�n��ͮw��� ӕgX��̇���wc`;	f� ���-p�9��kT\�"�̀5��??G���q8J~�M]؞;�a��z���e����7ᮔ�
Y~؋{0��6dd��#����k�uV�/E�Wɶ�(@�
�&�	A�b�`���q�)�q�1�*�eeZ����-I���?��\L����}��r�u���v!h�5+s�$���'X(�^��'d������J��6V�Z�&�W�O�R-V�UU&W�ꨖ��ޑ�i/X(1�ZX?r���0N'�*,Q�d�DU�Hϫp��0?��L�v�v�[�	�ScP���є�]K�2�Q/P�V�g#|��z߮�'��г�K��C��׭���i��� '</���ȫ�~�ҴJ������	e���_�݀�l|qLU��Ȼ�d��aϳ�%��W(0��X��&�_חce��o�B=-�Èu����D�+�T���r_����?�YZO�'�m&|��!SV#WS!۔��$ ���6EX[�#��9w�#2<�b���#��$5rj|n�M�-�({�P] ƺD��x���Cc/Z�����j�S���~���
�*R:�����n}D���i��
�oR�'�P�2��	g�@��B�/Y�����U)h��Pk�ɷ7�W�:����e�{��ū���ƿ���49�I��'�Mʸ�l<3t����*�@$׿u�ݙ���%؊c?&�,�W��!x-ht�)ê8�5���e�溇/���;E%��˲�w�c<Ft�4x(��[[��-~�v��B�K�=�w�B,0��F.��^E�"�b���I����<�j�LŋmM��:��1��J�b_�ғ�����v���~iT3=e`���G��9�AH����U�-�Υ�h�X�ďlg������5��T�z6U$�( �Y�˶�z�`��z_*]*�Y��{��9�����3@$`��z��[���(�]W��W3�J�-��7�b���TH#�   u!@    �!
������Ā�`2���`�TH		B,e����Ʋ��5׋JB]U��@~��铩�}/g�ս����)�/&|?�u�]�~��ȏ�5Wz�"5I����Nz��|�a�9���|=ܶr_F��KύHg�{Q?2'vU��)��Bq�d�Ƅ���L%e8#� FѪ���j��j=`��&����,$�`�P.	A@�P�1�B�2�Z�}��o�������S^[T�ì���><$��}�O�ޡ<�TQ򻜵�����8���)~U��9��ǧ����{ⶻ��p�*��ƙ��>��@��A&q��O�nb�1.$\O��Z�w�h����7�8��,6d����f���	@�Jݟ�)�p�4�����d׺�  � e!U    �!
���������bP`l��!E����Ʃ�x�?��$��]k�;�g>�$��]#�m��R=u`��Ǉ�N6ˠ���9z<�i� !���语["$i�{}q����i���{�2�H��r�y���ցnywb�������@}����H)����Mk�X�ԸD��0��`��(a �THU	�&0�M��Ue�/�\�����I����S:/���M��}ϗ��|�uz��S3�s˪��W�W�[���ϥ�d�?���V��`��З������9��[�MG.��3_�Kk���>+gE�`b6l��8�e/��S8IvE�
��P6�22ь��S�OO���<܁�  p	 �!W    '     ��
7"��{�<c�CMc;׌D���&��4�9ԳڹC��Fyt�>���!K���>�CS:v������Q6��|��_0�<�ֈ��b�vR}xBtd|�)E��7��u�*0���I��#�8ϦǪ�G���oS�T|�����z�>�8<@x7u7� 3��hD����L^џF���޵�Gt����j5ms�e��7&�n�]H(��@I���Y�H�.�|u����랋��Y�A:Ɉ���H�>	�{��>����Y�z(9�?��Xc>��c&v^Z�k#vOf�rC�5���]R�x����~>,�~��Wg�T�H
���#�O�a����s��w�Ȥ
��8�f~��qwZ�I�&Q��,Ϣ=i^iӫ5���.�k�_Ⱘ�2��ZGD�o���Q5+�͟�sZ�Op�Z��Ǵ1�no�Ƹ���[n�Mj[S�=�����ְ���g����%�]KvU�ǿu7k¤��9c���K �L�� Dl�!�]c�	��Tf�/�.����.�}����=umܼL2,�v�P� �L+�s��-�|��)�Z9��N���\|�B�.H� ӕA갲�26|�zw�[_�J)��J��j��!UA RK|�6l���MgE����"��q:�b;�.��z���R��}�hrK�Ҫ:��.P�} ������2۠\<��u,�x��4,&ds�'2���=ت�����)�����Mj�g,ukҋgƹ�Gb/�X�_  � h!k    �!
������B���`L���`�H(" ��4��.����˫˨]L��A����&�7/[_���=;���~g���K�V�����_R���:'�FB�e��e?���5�P��QS�j��g�T*F�Q�G�ջ>������k�0�H�7�J�������5��T�p��(	��a �T(%
¢!D&!.���.��ĩ�|q���E*qT��l���ᱝ�����~��˯�-�S���^��bM̎���s��sQ��6"7�����U��	P~��'�����VU���Ҥϛ���;Eپ�js4�*&IR=����R>���՟V�(|�����E }� �g��O��Y/ 8  s z!�    �!
�������@�`,
CAp�`. �H"��UWǽӍ�=�|EB*���-�S��z�A�����u5���6��2;�gQt��]�G{J'-� ��7.}�#%����T^Ŏh����?�)����8���I�eE��Ma����a��^�Z� �XHF�K 	�"`,�p�P*
B� �L*2��A��"�nuns��{ͤǋ��ȗ���9zҿt�<z�>ur����n��s��/�6~��@��^���>�H�g���@�{\���������tjU��u��fY '�`�Ҍ�tA]@ь~��z@6��cC.ؙ-��Żm��vM{h����(A$'��xЗH�O��I�����2 ?;�&�0�  �	 �!�    '     ��
�"�{xt�ߠi��F�F��T������T�={bU�z80��mI�K�ƾ�Ώ�]�}��F��C{��F%�����S1*/��)a���Eʆm:�(z���^�)�O��8^����3����q���N�W|c�A���ب�߱��s��D!�������2=�@DcͲ,��(�-��ǒb�ϗ�A~a��"D���Rx��=�P}���4�z���)OD*e~���-�$ef�`����3ք�t�HY��U�6�2�܅����T��%�Yk*�������@ZY��4��ؠ�����n��r�~��.K�v9S͕,_�ϓG�h!z��_��q��N����H�z��YM?�^��(��_X�d�s5_�yҰ(~��;��h���M5�/��u:}�ӡL"p�t�QY�^0$��1��t>�%3�ɬ�#�����i\���]%�**�#;�ϕ`�.��t���)�( }�����r�U������q�z,�ǙU� B<����exG�/~p�6����A��oҳH�?44��s��3��srCټ����
��s�R)}VDv�..�F�2
��������w�,~ÅnAq�Җ��Fq�kE�26fm,�&9�_e�4$���Q*??�c�r�!�b��N���%~�Sʖ�ή���]�D��Qr?n�BfJИ;�8  � z!�    �!
���������d4��`��H��k��okn'UKBUH˔�C��]L���9���A������
Q�a��У�?ݩ/��� �{�\ѓ�~��7*�6�>�ԣ&����I>HR_�[ԏ��mV�Z0�1�K��7D���5cE9�X��|��ɫ0� ����,�@�P,D�`�Pj
��B0���u^{����˻�7����x�끕�����i��X�z���6����Nd�_4�#N��C�ߧ�⟕�;��}��;i���#��D~"�5g�`��t�5�.uˏYXN�D0q<U�Ӧ~r��{�0K�m��j��(uo�P����п�@�@���T�;�-�˂l7A�����e�  �	 
�!�    '  }  
�A�
���L)���S 
%����Ì3��n�֫���é���wx:�O���,�T���:�o�/_���@�NfT=<�~��戎�ؠ�]�:�1�q�q&�0������pPy��U�@�I�e�fv��ܺ�Vщ͕����G�O����v6�w;#�NIg�;����4�{)�����@:����\w&�-�v�����!B�ٰ�DZ/?���r��q<���{_���E�XZ��K�<r���
'��!�������rBq !($q�e����Xh}0�)��# �R�bd6�W|��<v�#P���2)�#j�Gq�gB��d�Ø�C՟��R�Fa��sU��.س�; ��pQ����8�aVP�Q.�,L����r��͂
�$be8H�Ц����1�*�;�c�,2 pg<�/��B!���V���\�>Јl�ki�� ?2E�B9�"�����y�LsR
\�����<�zf����.�l� 1�Tx�j���!�û��~��g5��i�al��@���V�7�`�p=^$�;q��?^��4B�n8Ǎ�"����鶙7H�-ap���#�p��ޱ�v���i����a+ԋ5�s-�p6�����'�$3O Ԣ���u��<�<o/�Q���u���WżIL�s�6GN�"<`����!�BLY����P�"��@6%XXrFIW]���0}Z�V���<��.%�S&��¡�����pd��U���Ǯ�V��P�J��]!��9�8]C/#Vt�4EcG��;2�྇�e-y>7D��<��)�0�U���0	w�Ȭ��܀a�Xh%��ď5�ZG��ݑG���=��g
�[/i���ʊn\P���x���U;��j=�%4�F���S�N`�M/%e[z����G�g�N��>u���#�����l��L�����,��4���[�p�R��Lc�J���M�bΡ��@���c���kN�_B%V�(�wKA��Rb�<
ۑ_2���ˁ{.�C�ڃ���	�]�7�L%��/�-���� �(��x�Ƈ�8ϣ�$*@�7���Ϣ�v�ģ�Q&�h�
�1ٴ�!K����Q>������-M��+R�Br;D�Gp$���f"�������7�̜��/�r���$	~i�d��3V����,7c��
ך�"��e�A(8RZ����0D�~���1�`�d��	e�R�������ܔf��V���Ra�+o�&#lCLX�	����\����oP�u�z;O�)P������C� ��ʭ�94fXoy�=t��� �M�Dp�.�ګ���W���i��q�2���8����(�,�čsO(X9�`P�~��L��� ����X����&��G��%��'�p�����""e�w�����a��T�^̑�O������d�U��#k]_��!5��_ν���Ә�^IMwh,�6��S�L�Xk����&������쥷�$��D,;Y�i�9Y��|�W^�Z�z#{�ȏ��!��)�S�-�>���_,��/���z��hu@V p�i2��y�
y��%)�i��U�CT��X���^`��EA^��Nh�����Z̥����}%I�5;R�lP?~%�-��QV-٣wΤ��\k&�E�� ��I��+�������#h)z��t+��%�[�m�׾X9I��* �O�o3��Eb�K5�VH�{�?N�R;�Ojc������ �`M�=��~<�.)��'�0)�'^�L���?�#ZX��S�g���%�j,�I�G�ב�&��n�Z��<}(�\A�����q�I�>��pM�ZrY��s�G Ӡ��rX19����@t7�"��ͯ���e���`�D��*�82� <��%0ͳ'��䩁@B���;W��ˊR�i:c����	~lB�n=*�����9����${��nP�m,�z�$�J��OC�Nf]�#�,\o"eT�$]U���B ��y��_�ϾnؽF�@���D/���5��ٺ���:�d'`�S�2u(M'�5?u���Zh��-C��є6���JD�Ti=�'�ת'�p����.�;G`��^����Wj��I�f�y�����n�2j$F��b��<�;��Ǟ�W�Ԡ��dŔ�QtM�rKa�QAڱyQ]���
'��<��&R�C��9��X �����잲��;�Z��3�>2s��-���TR�I3�-ܝg�Z��!=j�o6MI�}DJZ�6KX�j|ܲ�����ċ������	VElN��d��׏��-�g�����]�]ʐ�\0��P��-Vh����'W��V� z���"�$`�]�{����T7E�=���̰�p�o���R��)[����d|� ��LY��a�ҭ�m���U(�h��v�S��+�S��&[��K����}��|�t��B����d���6oP�����fx
C�E���_��$�x=ud�Owt�L����S�ϯe�5���b)��͸�S#�S�ǘ=n�������� ԫ>������F«�C����N�o^ 0M od�*%��@������
�u�0��Qt�]?�,�}F�ض,C���o�>���mk��35��eokIr�1�`$���^^�uGfy����"}���4ǒ)u�B���"o�Y�� �ײG���m���Cc� �uje�0�t���-[�ķ��PM��ܚ&�I��%���%Ս~���Oч9  
� t!�    �!
������
�@��4��`��(2 �v��omf����%ַ��d�B�����X�| �z�օ
��o�j�|���)����?UU�P�@��IG�ھ��fjY>��;=�����sG�����B�E R���������k�,U��f�P֘��Z���N�qJ�*JsE�<@E����a��(%¢0��"��~y�*�Mn�8k)r�d��U�г���^~�~ߟV�|z�u�O���!g�:?���)�� �f��k��2Ot���~���	��{�����>���Q��o�E���[�n9]�~��L:x^��.���k|�G���O��c��ͬ�ݬ����9��>Ǖo���|� ̐WC�   d!�    �!
������"����d1TH�nJ�RD�7|����V��v��/��-]k��c����SEQ㐰�rO�t���-b�a�����W�*Q�'������XU�<�(f��P�&���%�����A��Cy�͈�5���,�0J)6�f��)��+��;�@�P.B�0��H�Db�]k3Y%y�[���n<͒{
�ǧѨ�p�/gވ|��g�Ux{:u��۶y���5�G
�z��3�Tonϳ/�xR�+�gz&�������8����/b\1�Ѥ�kt���t��4�%��Փ��]�f�S�ɒX ˌ'��2�ÖX0jy�S�X��b�8  o	 Y!�    '     P��"�X�+���}��q8��m)$F�7�����ލ���a�x�	I��Яd�*_ݜG��3�)L^��ҥY�H#�$u���_�ˣ�l����2�gM,�F��\��?M�(��W����S��ϰQ�TX����7����M�?���Y$F�_��І�^�t���䏣���`v�_�+�UQ]���+��V}
N3�T��BH̍,5�B~`P0*!�Ǥ� c�\��w�reحt���`'�Nqx��И߷���jD�B��
��0J�r*qbZ�uZ�)�!�^�|F �#�N��s��Ń|P�������m���C�t�b6Y6��.��B�]���&}N��7�`W�e������;;ʪ�o����#^9p=� V�[o�A�-}���E�t�T�~\l�:j|2H����<�S�0���!M'�lmɁG���Jj0��PD����=��a:LUw�kV���$�F�S��M���ļO�����L���ڠ@�rfйN~X�ɦ���o�F�2IB� Kd��k�ϩO��V���Kҁ���F�9�ϰ���E���Jj��V�ȌYA  d t!�    �!
������a@h0�� TH
�! �Z���+�d����q����ׇW�/y��t�kǗ�A �tT!� �x_-U�D��}
����A�8����Y�'���(rO�j)=���E˄ؽ�� p�2R0�̲��Ԗ[�lYA�/�PeS!%o��i�nL"`�	����(�B� �"��!q����o"�]�/�6�T��uu�Kg����~3���r�R}����0�J=��L��O�TY�O9������_�{<���@���������-�1�t���'��kNv=-���y|��ށ��%V���]���m[�j�� �U�Q��Ĺ�S����^i$���$�-��BD�   ~!�    �!
������à�h,D��`��(��&0�q��Y��8�-"��k#���Ϗ|n����z��q�o���9�"�UE��~;�_O�E�����oy�r8^��yņD0lmM���Y��NO+:���J�͉�Y���`�It��4K��m�����
�#�aUkZQ%tՉ-0|���v�a��P
D�P�X(R
¢�Lm�o�u�7���癗2UB�qng�m3��qi����u{�͓x�-���7r�M�#:w��v|�Y�>9��9��9�V��D�n�eC���7�M�PRSu85w/�y~� �K�/n��Hi�����8��m{Mz����o`�01o�Dw��� ��� ,
W� ~GG���U}��  �	 >!�    '     5�7"�h�mm�{"�������!�K>�	�_yg�o�4;��rC���i�腠�
͍��<q4��OR�`RD	ܭ�q�tݽ�`N�'\�{�וH��"J����~�6[ıy	��z�֝��:v�
of���N����M=v@0,S��|�GD��͐����+�-���Z�"(�fܡ�6�j�q�� -�۾1 ����~�b)���ٵBs[�WMi9.���M7�,�a�����]l�aZ,B��w�.��o]Tu����ӎ�F=�k�b��zg!Uγiv���5�����*67u]�_�F�Y�#�՗�{]g��h��73_P�b#�h�h��ó����Kbp��܋����{X��R3L���?�-/-�qa�xJ{,�;,U���UT��M�ptA�g4�kd�/�o�q�	g�6�{a�0͹�ŋ`˳1�g�b�/ÛcJE�����Wi�'py��8_������$��?;0vGd!��ܖ���c'�� 
7�ˇ
�MT9F�1���v��H�q��4�w�Ģ�+�Ė~�p��wkS>/�����ZM��]A  I i!     �!
������ƀ�h,�`�T(��_i���J��TZ�UD{�})������8ɳl�R�ٹ���;���E`���V����D�����8j*H���>�"�Gw�E�����>����)�����\.-�ʗ[�7�}���V3wx�N��i
�7
�T�bƹ
�p\�Z�nwB*����,4!��D	T&%qJ�7�N<:�J�T	�Je����m���=m_�񟓲�O�ߺ��o��ێ� T̞}�_�Y�Q�Χ6���M����J�������u�e]�����xn��nX��`6=ĩ����R�m�?A�DG.�}N�f-���U[����dx@��g��D ���7~�L��  t n!    �!
�����	�`�	�A8X*
�,\�7���-�g�늸���T˦���oe_����+G�y��.��&V�A��L���L��]R?������u���r@�
�O$�U.��������WT��VE3�_(ԝ�ue8�t������B���_ә���@5%��˄T��A0PL$D�! H((����[�wT�{�u�UER�ym|hW���:y~�N�/�����۳��˿�����@�o�x��7Gv�pc�݁��֖�����0��g�����G�^�S=K��%1'f��݋�x��v#�����3M�g�m8Y�Hz<Gm�w�: �;�����ATƏ�  y	 	�!'    '  ~  	�A�%��L)���S K�
b$,�j��.'��e�lKU!�C��"�+��w� їR�gZ�jg\�~H1�4	�`܉���0���!R�&�**�a��t�J��֋CD��F�����q/�65-����Ґ��n�f�\m�]rߦ�i#7$��H�;�,<w���tU/*}��r��3,z�)�%<<v\D'�jr��ͮV�o��_C9��l�:��GFp(���b������5&`���GM})X���[�Y4y�9\�E�u���/4�L����J�"{m/܆��1�'�039����B/�䆕���SR�N�m��f��T�O�D��!^�|Q�&Κ��_r!���u[CB��99�DU�br6�.����Ez� �r����/�F�������Ī��^�w�`	\�	G?#+?q資�HP��~�K׶
Y'%�1�G��S������<g�]�ĺ��$tf$=��sc�����n�Ũ('
�i�P�W����0�"��.�(�|��O��'�v�V%E�7M��s�^�N����_ ����=8@�J�C�yې��B���'��J&�@ݥn��)���ײ�͈·��FF�B���Γ"����������)��3TP��&�ks4U'�:
-8��Q=�����_(�ƗƏ�)�\}!s��\����|=[���O���/��uG%�1X
F�~��(��{Y�hD1���N1����q��,xA,38KM��G�A��WxC�@R�����;�OIC1}Z���4{O����rςr���+�]��K/�� ��{�6�+�u���d!��z)�t?�����z�1���sw�7�[�E1��Q]�
����$��A��
�0s��sN�����U�����'Z�Vi�.��U����,b@�c�ӲwE Lÿԕ!�1-�fO�"��t���&�N�gU*s�fa�T�w��#B��\��)c����02�.`f��K��'$�~|g\�N?m�"݄����_̎��+�U����;y���ʧE�����wY�K"�N\" �4G�.��}J��'.A&�!c3�b��X뒉��8��#�`�c�L��8.rU8&s��z�p��<����V�S��a�"	�CU���ϐX9�
�)��TarPA�Hȴ6�u���e�J�QR��ב�@�l!�΂�i
�[�v��#|���B�X�4�Q���V���ao,���WbQ��n���.��lp'��;����h�Nd�Z�Xҹ@ *��*�_i�f烐�n��KVԌ|	?.?���\Ђ�6�В�,�z��ǩ�#���iA ߡ�x�~���N���b�~�~6���A~]���x��Ed���z$��Z�9I���` )��f:�O��M8
�U� �		{�iKh!�"��lO{���guYw
!P
�Đ⛄�=��2�9}I��.)NX��!����Y�)�5�?�̳�"L��.T�.^�3�]Y�B(4nq��������cK��O62M��T���(-6���(	X�Ŝ�-�5��R3��t�y	:y�T�H�q>tIh\��ִu5�ʩ�����RZ��c�L�����oO� (�ϟ׈�D*�;:F$���t�ę�S(��c��G��H�6�_��ܶ����6|�k�0ؼ�}v�u�D��0�qN�4S��=��2��8�G����bz\2�Bq�*bQ���E�D����)�ɐ��<�l�����&�։�t�p�ڃ�a�D��ٿ��y8JzI�z~�k�@�\&�w��-��*C����1IO���B�[���5�IX���$��*�W�J�`d���^���&j0��a��mi�E_=�ժ��~�՞$���22U�>�[u��a��b'I~��d������
�ܻ�� S�Fl:>'s�Rח7��e���`v�mȲ�d$��E2���u�*�����?Nb�R��@�Jm�Zn��Q�u�Ħ�h��2¦��𥣻$�a�f���?j�IFsf�OB\�#�-:w�q��XJ|�e>?Z����?A��(LPy̒��9<Y���K���`ҸVp�W�&}%��b��W
�l>1��Sŗ����)Րh��*�{"�K�����X��݇f��PS���>���Z`�V�luV<%)�ڰ~|���#��6�J�}�v�t7�T�n����[��ʎ�Qd�Z��m��	VưÅCL�1o̱�7�3�C�w�e��I��kH��g~!�\��op��QI���h��,x�����0�J�7�N'���
��2��I�SgF�_�n���y�:G�=G�p#�'��6�v��,h3.������p���U%�(���k�zB���~�r�U/_�V��т��.ާ��NU��+]����9H��|���$��u���cƳ��'����-3��Tǋ%9j�c��*�T��S1�  	� j!+    �!
������Ƞ�h,B�`�TH"�i��;���]y�8]�&]R2�	����\Zn����ë��0}�c�3�������������~���e�A���v�b鄼�=����zD2�n�Y�Fd�:���l�^���($U
�����t^�
]q��FjTNL
,3� b@"�,#1F�`��*�Ba��Uֺ�-y5|ߟ{��T�|L��N���:_&�������7�d�O ��zz�L7m�k���*��V��-����U/��O�c�~!�zO�x%!�|���MU6��@|��Q�[�6M�3��v�� :/m�}fףux��[�:ONS�4����� �j
^+����E%�h���3\  u e!@    �!
������	��a@P0�`�X*�A�"�	��>��ݸ��WUWl�E� �����m�{��|'����'U���8��V侮�o�>`��p��9o[���G�@m���T�e{�����~.W�kI��xev���X����݉r�QQ<�$ײp-��y�"�J�R�RC0&�À�*D
�AA�L"SVe�o���ˢ�G������}�o�_?^�?��_��}��>�ەގ�5m���<�d%t�W�?K�|�@����� ��>���&7p�t���:�w��Ôu)<?�Y�+�O2�c�L@&���@�]��Q$��)�V�����K�>Q �vq0�I��  p	 ?!Q    '     6�7"�����IJ��cM��@خէ��)q��р�L�g���+cq��_U��j����٘�Ëǎ�>Oδ�!,Ʈ�ӥo��ś����5���i
A`|�z+Z���]!�l>%��G�D�,�s|`V�Á�_��uO���9yF�G}}h�];�jj��0�b�T��� ��.���T$q9&�߭�t�0��'t��br�Z�!�y<�zY���4��0�8bd_;�;a��v�&=$v7�c��c��E����$���?�(�?���ht�q���*��*�����r۩oW8��<����u�5tq������k�f��D;�M.l�����}kt����;�������1�����u�� �X�0D�Zϕu���ɹwegv���:8���ƌ��5��0/���C��)��t���mS�T��5R��t�5��!5������O��F�4�":�v�?M�*�Q�-�&���0[���k*���[a�!`^���~�A+�T��X���� fy&[݀N[ગm�~�k���s�8,&XI��_MH�*�Y�`��V�SaR:k%��$  J a!U    �!
?�����ÁPX0��p��(" �§������Ӭ����L�_C�|����O�o��n��y�@ �����Q����������F}ִ�^��MǙ���R������qWunw���ić&Qr���J?[�2��#YUI���|��r�3 N��g0�;� ��# ,(�@��*A@�"
�Da ���ߜ�r������L���q������һ�m�D����<�`��Cg�C[v����>�����|#�}�%A��I�£�d�qG���ͩ����C��R������<���&���~#4Q�w}�d��3���I������T� {����|h  l h!k    �!
��������@�0&��@��q[�~7]n��%�H������O��PZO��O�=~�]�<5���#�G�m���__��1�{�{Ez��Q�7���KM�U�>=���UI��e��4��H�]��+��_��ӥ%h�Fs`A)�E�l*BTN<�:YB+�+ "��H�P�L.
	B� �Ħ	t�.�8�S��mړ/5�ΆF�N�n��(����|���>��U`6��)���a�vvH�[7��/��q@_��+�ҧ����jJ&�-����#b��������y�sE��aٰ��/���{9�-��sr����U��d4��c`u>L{S+���@�w^�\�
Do!����  s	 !{    '     ��"�?�ߞEt��RV�-kbQy��,���� �F
b}m/�k��]�/Ԝ�3y;ne����y�,�S����k���Gnu�j?�� �5�fP��󅓤��7�1�q ������r 1��X$W�,8x�S7DL��*\*�HG�kUœ	�x��x�� Ra-��jȻ/[ĸa�Ў���Sj:x���+�����[�v��+��26�V.lh���&Ӈ�a���"���%����.����F�Y���xc[�{����۫�@�]�HH�k:�2��+]'���&�1�e���)D.������ar�O���0���~Sy����l�U�	]S�ړ�D�k��+9������V�n��S��_��VHo�MT@ʟ��c铹RHUS��K6�~_�-?w�L�����ɞx�k%���
�F�H�%�����\ @��|�C4o�z7�N��1lZ�DC��a�E�<Y��kje��K���a���5��N�]D��`�YoN�����1������rd1+ﻀ   j!�    �!
��������b@�,(
��P��$Ac�39��\ι��KRU����u���I�����D�'=+�cy���;��Av�;z�?㠄�{��'��>ĸ�)����&�9�kg��Z*ͥ���,�|օTu�Z��l�nY�,�y�N4)^�ѵS�
����>�gN��6
����&
D�P�X(
�� ��F�Ba��J���������犭�Uy<�|�=�Y~U}�w;�4b�yś;���l��Y�>	����:���_�Q9���^��~F������$4D.��u��:��io5��\�Q����%�;I��b�D͎uϺ��6��y&QR���)Rڮ�RIR�] ��W�P?�C�  u m!�    �!
������ȁP`,
��P�$c&�.n�]W[�n�IQ�+��Qsz���rx��������B=&�Կ*��xNѨ�j^�H_Ӳ�����!�i
Qϻ��D������W&��j����p�S8��I���lw��Q����q��e��y\Q^�B��uCJ�ƸfeT	�`�\,h� �(%��#1��/>w9I�N7���**��ݬA�|���ya�^��nϏ�����p�<D������>[8�����?�^�GCc�����������Q9i�!�z7���_v�v���hK���������J�bT=�n�g]�c؞����]m���0 ��y�cWyhw�|h�����  x	 	�!�    '  }  	�A����L)��sg�L8� ��X�bž�LçGp�eb#��k�¸��J\���ZrAv��&K���6�\�ݥ}��.Xa�{����}�qh f3| aW����W�V�0�Y�~�E��g{ ��V���㺎N���>�e{�!��'�2l�v��F��U�e29��D�+��/�W�v���f��nҴ�T��Vb	F`J!�9.6ř=k?���8�h�M��iTQe6���,���@���" K &g�Y��e�g,���1t5X��u���pV3�6���H�D$��S���um�vrM���r�Z�=8pզ��z_����'U�x�Bf~��B�2� ;�'i��R\I�����z޶��Pۉ�>��Y��8K�.]a��䮌X���V���6���>�*�V�v`��UZBC���a�"�����5N�@=.���tf���43yG��sh�`?a=A��/QL�i�ƴ�H� �iְ=�{��f��9�����j7���=��ߔ3�\b�����)����.w7���˃�y�/PsְVý���{.��
�7��w�|�����?�I��\�T��}j�guS$��3���#0�`]�9q�N��|niOTO�̭���W����^�*����׾�)���5����-���
~�H�����O4s����f�s>#3f��|�<Ji׊ I����Y�o3����Ez��g�;v4�f�M[�����R�ڲ�=��c�x�\d�nH�);r%՞�Py�|/_륒8[+3����b�ft�wV��xK�7�5�=6<wl�|�\3en�}�b�2}���D��q�NaL�~2!	ȵ<,Ti�	���[�m��k��9?�C�=�8���NN~��}k4}ֱ<m���_�$*໽6�A��gX�Ƨ�G��ի;a�$*������L�/�%��=��h����G�ܟ��?,6�����V��:����#Gy�o���;:�_)��w;��Q�_h{Cu@	-�3��H��)�L������n�s��X���r�
�
:»��klgJy�0�!�{�W�T� VI�0����/���y'�t$�j,��$졅 �]<n���&�Z�1��`�-Ss���|�M����c�,a9!;�]c�_ag���|��t3��N���^5�G	�X]<��9����B�r�k4�hٕ�"��hV����"b�������C��^�H�5�E��_M�L��ބ�㯺u�f���GT�X�XM��	5�|��J0��T�h}�ڡq��9�#郶��;�]��=�=u��6��O�m-�����&\��/Y�'�@��	\���G;��]��iBm,�������
������m ;LHJ� �ϤC����vE�k�q��4�Ġ�9�����>ɶj� �'�C�LO:�XӀ������@t�49}��t�#`b�d�1�����7��%ws��_i���^zF�������4���w*o�d7��N���:UD��Ϣ�+9!.}yF.83�ؓ͌�mC��*��i�������Mm� �A��z�q3{4mD2����&p��q��ל�@QB)�e�V���Ϯ�K��!�J�]86�'��N����Q�k5����Ą�����ۀ�(���B��o^'��+A�t���h��?�y�i�,4�ח��d?"�篌������jh~��B��##~9�Q�lЭ�g�AC�����Okg�i���(!�x�p�h����2��������ˍ] �n�I�y���c�Ǩ�FH�#�> ̈́�3azQ�Oqϧ�b,8�g�憔�%q��'�!~�<�����1��fr�d�����jJm�Sg@m?���u$<���NQ���Wh)�)�1#@dߒ��m�#��
U�ǒO�'چ��IR����Q�c	z��S�R!���-�~���8W3v[��4	�UKH�u:��<F�u��\�T�dW����y`ج<\u�r2^��Ch@ �c�{��9R����5Z
�I���u�{]���ꏕ(���s�u�����ck������6�3	�1�S��c0Ri��Ʌ}��u��JmL�$��w�H��p6���\6���F�EL�u�	J ���4��Ƿ��_�860�8��%�x����w��a�����?�ĳS�	��~�.�տ?�Vy���7�����$��	�X�+6�Z�'���-i?Ɣū'�i����&vL�	�J6L3K�|�4ԓ��R"e��v]�S׳'?�	���(�x�x�o�EJU��ʬ�����|P��9ë�7Ph~�2,�:��P��%J�/�&@T�ϐ�~���g�d5�2X�S�)w�(���X���;��3�k㜈��;����5�m"�Dѕɲ�񠨾���eY
�ða?�+,�=b��	{_�S����t�ZFi�`��  	� i!�    �!
�������āP�,	B�P��$Aa�)����W��DT��U�9�����ۨ�M�����ox�E7g<=���~�o=�t�V��@�������2�~w��߹G�:Ad�[�G�3/�M]x�:1I�*�4�~�I���Z̪�R��2A@V���XEY"TF(F��4i]����,$�@��(b
��2L"&q�sw:��ïZRV���J�:	��W�����_o�<]8�����h�����z+�~}��44�W�v��ᾓ����%������R����귂��7Q�_��U}�4g߼�2]��*�1�0�K'�.�P�nO쭈����� =/��'[��V��� P�*^�  t h!�    �!
�����s	�@��2���P�Pd#��,xM�q~�^qoMn@�ة�����۱�ǿ?���4n�����a���iB�wQ�`:Zis7���"2�S�:�y�9���O�;g��P|���]��y�L(=pI&�G���BJ-�HMQk��rc�C<u�D&=k���0"�L#�@�\L
B�P��J
�N��&�W���E~���ߎ��':�]�|��ߤM�3��7紮�_�G������d���"�A5���\8 -�~^��ӿf=�A�tnO@g��VQrvK�v�7�Y��V�׾�����Zy���M�d��28��EFX������Y���鑼�e%�}sNW��0  s	 �!�    '     ���"�|�� �}���x9� i�ˈj�z��(�eE��� 2��W�*�ݛ[�b���#b���`U"�)��CA�l�+2s�1K��i������8�r�ت�>�ӀD=l�CD��ݔ��"HS%�QZ����Ė��Vc�Z�ʏ�g�`��ad˅��t)���]�a6�<RT�a��n[�k�q�j��@k�q�&����+v<ob��ۦ������j>���`�I�F� �ܲ;_�8%��3�j+�&t���5G�h�����]y��t_Aw�˕��*��[mr\��\�3��(Ȅ�+:����y���*��+�%4���5j�S�����'o����w�ǜ	�~��B�����ܜ(���x����
S�YҐ���L�S�jw6�	����Z����\1j� ��re���U�hU�26�i�M�O�t��zR� w�H��#�	us���x�Bȥ݉�TN���>��V��3��O���V.IT   k!�    �!
������	�p�XPCA`�d("�� ����]�_\g�SU������o��.x�2�.�H�z����#/�)~�xG�E�7_R����}j{(��J)1����_��Ioz#�7ћ�t׋��i�R��+�H�5��]����"��z��P%��w��0@ؚÒ�U��; Z@���X0��`��.	�a �L(
�b���K�P��u�Ƿێ�srgG8�~Vwο����G���;�)�ь��S�_���Qe��>R�[�~�UP��r���|;�{������ӷ�������+���1���ݛ����.�]j�L�*xD��z��� _4=,��� �S7��h�D
_�Kp  v l!�    �!
����"B���(
��AT$1c�>��z�$���*KζI*eJ� |p��{?3?��j�t}6�W�nH�:�ֿ��.n��1���a��/���M'���#��|~�.,�߷�ܪ����m�!�)��-�Th��8�w-7J:�[A��ɗ$����2PZ�,w*iAay�a�	���X2�`��p�aATh"
�!1�"S�md�Uԯ��s�y��j\�wZ�'��W��[����|^���[�ҿ���X��A�R�R�~���v����?���� 
����7z}��'_Kl��wfü���>�溑�>���WkD�s���#���y��K���@ ~!l����6v}lj�À  w	 �!�    '     ��7"����8ff�(���3�Ԭ��0sLe�"�y牨M�zK)�_?���uUl��~��Q��o�&��֯#|6>e����= *�9�����6N�1ruK�ǩ`�SR��̠��B��=���SH���>obo5�'d�
Z$|���*�$@I��G���Yq��\���`=I��:,�.X���G��M��bW�-:la��4l�o�rL?�2�X'y�mwx��Հ���Ě�����.���>�DQcH2�s����l�0����Ӣ:�A����;P{�|�C'C5��݌~��1=�9
�NW!&�(��1G(2dANa��+��,?.AV�WzH$�9�����Vm�p�dǕ,v`c�נ�2�byn	�Y��N0��]�\9��/&�%�&S�W
�>{A�+�qbyꄙBKn?vG�(�D�CZ8k!�_h����	�j[;���f���c.����`  � `!     �!
������aA.BFR3�߬��J��Qj��� ��5;+�U���h��}Zr���M{(�aߙ��\u��g����A�<�:�+%��зw��.�}���qtRf��ž��h�`i,����[ƛ���6R��!㹉�ր����+� TB�Ie��.�I`7�x	�E@�,(�A0�*$�B�P�D$	�'0����׬�*5��}��6'��=�|���[���d��.�x���t򘔫�۳�Y�?2�g�)d�M������F����x=O����j��_$É)Ϊ��u-�/�6�|ח<�
��Gv�r`�K�t�#S-d O���=~N��D��g�V�2��8  k d!    �!
�������@� T(�aD$[�}��׉r��Û����k%�z���o։�6�{6�ՑRZ}� ���|��PQ��{�'��C^���S�v���~%���ھ�4�?1=�~Զ�]"Q���9ȟ��i|!�9�zfN�tR��c|Tf*A���N�ej"P6��`�XN
�aAL"C��޳:ε�Ӎs��pʫ�l�e��� y���)��5W�]��H��ؽ���ݣn���d���*���������
��߅`*��g�����A��8>��_���a������:'9c.Z�c�)�Y��Wjfk>+h��iD��^A�6�߇�������ML�ڇ  o	 	�!"    '  }  	{A�%��L)��:o#����,�g���N�{4�w.e!��y��[�Q�}2%�t6�Hc��u`vW]�ρ�`�\Ɨ1	��ȓ�w�
��T�&���p�6�0��6eU��w7.��:��)�cR�j2Z�hJ#�Z9T�H=��{��o�D�|8?�p���v[�KV�{�:�x%S���1�@@w�e9ws�s�~�eT�j�x}� ]VQ�^	�J���x�����{�o'�t�=��ɘ�"���$xG	}���VXO�J�����s�@��[��y
���F`���J3�Q^�6%����Aw��G1�H������Gԓ�����ā�[�i��u��&�����R���+c=k�m2�)��'��sD
���&!A�"bx�� ��0@�Q5V��> �,���p�p}ݽ ���A��>��z]}/�C�6ɞ�c��{y��ȺS�9Q����E�F�!�yf�u�t�ei_��Bq�t�G䴹����9��!����ȀT�X5�T��}�7J�������e���� E��:���7�
}��
L?�4N#>*Z�O�uW�]�R�I#�o��)�Y4@�f���!sr�����a�����	|X#�v�8j"ڣ��ܶ��s��6ê�@*��+\,���X��8B�_^�o��
.�o#��*��$�$wǴT���ΐ�1,O]x��
h�avRC���(V��g;9>�꺿&�(mLWuc򿵧�9�m�v-~Z`���pau���oS��ibb^������3�n������'�V��j�����6�7��Dƪ�.m<	O���- s<��:�pO�d]�H���l! ������`Q/��Ȅ�j�����wTX��U���S���0��:Cj�7��X��{���:8�Od@�@����3Aa�a8;Z�E��_\��*yt!��(Um�l�1�m�K���T�����܎]CI�S�J�6~�y{םpVr��rۧ�CQ�8ϙB�ɀ�o/1��`��N>v���S�b U�~��c��"1�$:�p����]����9p�s�2�g�[�),$"�C�_����2�1��i;�)��]�����=æcn�^T.a������~���w�a(�;�6p�ni,~���HFY�	>�=�*l�!H���f5�D)�B���fr���{u�R^}Y*��Y��t�x�1��$$�R�a;����2/����#?4nZ�ъ�]#����G̪<��+K��f��$	A+X���qvh����$.�O"��O ���Z�x����g)˞��a��/�P=�9z�-[3p:pƲ���?5���D4w����1��N��D��AF�=>��.�� V�|o��tI�f���uK��"[�uJ�j�yv�n#X��Ű$
�D=���̄����f�9��4��3��=^ВB���������X��U�)�? ט�-��-{�N�#�&�'S��x��u��a�T+�'�����n�TKJ��;PC��ΓD��m��$�-�3R܌�8*p��,�[�[��ՠ-y�`���d���T@�,��;@�X��r�T#���f�L�JM�:
ܑ��OVYr���y3ۧy����x����k�)�[fR���KG���6k�R&����͚�\�c�~ȁ�f+R��X���\�:K��ޘ�q�\�&�cd�d�����Ѹ���
�N�!�G$�%�(a�'߅��U��s8�0�����(T3���.b��'u�x���bC�4�Y�#��)8ݩZs��(
=���@���&2=̻����
�ЯՕ��ڐS����Z,},���-W�͏�T�������Ϊ�C<N����T&^|N���{�n19��:.!*�e���N�Pu��b�Q���ؼ
nЏ_�;&-�RI/�" ��r��ܼ����vFYw���I4k\�I��2��V1���?�L���FӪqm��)�y���
�4Y�*��m��p�E�rip{F ���fg)��`�1��}%;�h��0|����A}}��B�qչ.i5�A��EON�M�s�޾V]k��};o�`X�)'Đ*�f�]��d�r%����Dp�#O[�.��M�/b�
��㒪g���w��u ��R����
X	��jqnG�m��cXv����Δ�'hM��|��_�@B�e�G�jFQ>�\re�&���]�8g?}��}ӆP���-��/���j�K����7�� �C\≳�F�Y�M�����n�:E��<�ö3���H����l��T/�|��W��s�º/�j��v� z�]i���j�J]tQx� 5[<�ϑo��ii� =r|��p���rrO��+ye.��%:B��$�Φ����]M"�d
�#KZ�����~�W�ż�ܼ��D��R�!  	� T!+    �!
�����&Ba�XH
�-r�[޳wWsz��j��U)l�{
�o��;^ݙy�����zr�WW��`p��,w��a�ߐץ>e+�G4�]����{Cbs��ەJ�w��*T�z���9F��1V4��g�g�eb�Fj������P���䰌�g,()�
^� l(�@��JY�A0�E�ߩW���K��Y�K�^����}��4�>�Gg����vΫ~��ׅt�O^ɺ9�O�%�Sѷk6���8��~r��s�g^H[X 8.�*�
�W�P��2��.�K���?�|�Z1�\MI�����^k��/�o�=�pm��g��g��ܟ�X��&m��>#��@�  _ b!@    �!
��������A0P0*��a�TH�,a�9Ǫ����%"L�^��eL��na�C]��x��'TDBH]���h��M�O�a��3�Q�G�[�B��?����E9�l������Ȭ�r�Qƿ�)P!��ן�BY5NCDg�a(�t,IApƨ^DA��j��8 ��1L4"���P��D��ns�ĽnS��R�E]�jhQ����_�
�y�"��ifz^��2��w�>��[蝼NM��*�~6�Lg������K�����O��P���`O�*(w:N�Fy];��=n�үǻS�T��n
a_~�%\���V�Ob�w���ܴ���h�H'���w�@?��(��1�0� p  m	 '!K    '     �7"�^�[�}"�f�+�����jq�k͊*꿷�J˼�ݙ�]_-P�BV#-0+����,9��
�D�S�k0���uO�Ъ���k�u8���]wz熯�"E�M�Mm���C���mPu-e�;���70Bu�\����_K������r�{Cj��2�T��V#U���Թ���x!�m�B�~R��I��o����ŐP�M��V(��e_�Ka�H|W�DG�:%#ǑI��o�rgˋ#�#�:�f!��姓�7�2ñ?�]/vB�Ťi�N�`��S�g+�9fl�LO⃶ ��hԋbbַn���/����?bEe֛��j2�(�W�%j���ly�?*̯��O )z`�"�Xŀ)�V#�<oP�5*/Hx��F�-
Si֘�4�A�$b��W�_��0c.���g�<�`�Es��5ㄶ��_=1�Zϯ�M�|M�ё�h\�R���.��u?MbJR�,���2�_Pl� �Oɀ����V�V�5\X�v\��4�E��5X�l��Jy�  2 d!U    �!
������	��@�`,(
��(%	CEMd�w���%oS�����r���8���7����E᲏��'P�
M�]�YQ�+�C�[pM1�1G�ף80���̈�����_�L%�q�N��s�S.���;lZ��geu�ݚ
WC�Ψ��:�p(o�H)����j*} E����AA�P*C1Lb5O>/}eZI��k�*�2��5g��c����}�����w��~ ��῰��;K.��@xq�+�MQk�^��5i_�#MXjQ��k����ݫ�:�{����\�M&l�p�6�W]��������bv�ߴOo�!�@�?䥸�g�9�����
�	q�����  o Z!k    �!
�����`�X(
�@��*�B�!���nz�ۋ��{n��)�W�!��W�8������S��84}���e���I�O���!u�����?�)�1���U֪�^�jN��Xk������*L�^���p��c~�e�i+$��a����ҴHP
-EV�����@��0`,(�P��`
����"r��7��y�?{�ī�sz�8����R���?/_Q���:M1=�uYO�7�&{�}Y��ogO��p i��ڽXF���J�_� �Zn����j�o��{����s��t.)���\��>j��fC����<k(���>,Bη����X9�*�[�W  e	 �!u    '     ���"��@�>���ּ/��%J���Y�%�������a�P�$����$��_k��X4���?�ȷ"�ǹ���H#�f�B���N���s�&
��d\�JoI�9�Y/�955ڛ�%F�2y�\�f��=1�H9��dW8���?��Z@&&l��6"�-�j�p����������<8cw��~�Z	�rt�B_&�~=E�^��?�%O%8����&د\:�����g�7R���됖�m��D��dOvFfY�f��.ԹI��ּ*y��7 -bU*#(R<�p�o������F� ���Jo9s���K�����K���ep�����d���<�f�CM��
�Df#���GǙg���1��wO?V��D2���Է$I��4Z��{*��2���~�s��2�[-��t-�i�w"��Q6�_QxT0g�M�����5�  � Y!�    �!
w������a`�h2�a \(	" ���o�d��׮���B�2���W�������贷_��~���GԿ���{.���_�3D��ޢ�ûh)�ݒV ������j��,�\�+f��ȵ-9�G��a8̔�W"8D���&��)tT�� ��0�L(	�@�H*P�P*	Pan�U|��㼸q��۬/�jJ�N:�~���_/έ�����������|�v����]�v'��0���6�(::��M����}'_�Î��s���}.q��V1`kE{�~�T5G��ԈG��`������Se�#��t�FG4'���XN�p  d b!�    �!
������@��T
�Q H(%
�.\�;���\�%ַrn�L�}�|��׾������o��L�􈞌n�o��&Y���8�g�u�I����W����J+�ʫ��ԕ
��ަ&%�
FP�ĩ(鍡�H �Q6]�
���7N���l�a%�a@�P��`��$	�1 �$	H��x��Ǯ�^����j�U�k��������}�|V[���7����~��_b�w-��<����5o^�\��o�G���$#�wnZ��5[9r����<�����{t�'����u9kGֿ��E폰�K��=z��@ 
�����9&�&2L��[tK���1A�&  m	 	/!�    '  }  	&A����L)��@��f�t.�T��@:�$�����|�G�V ��D�դ��8g�=EH�yp��UYfd�2FL.9�)��t�(R��~�G���T�B���%�-�\�?'��D��<��d��s}��ݛ`N�T^�84��BE�z�S���o�,VX	���t���TԂͣsG��=�}�~ʊW1���#�$R�l+��_��������z�+�to��ݹ�վ�);���U�c�W�-� H�?�|�|���OJ+���%Y��m�XOM%����%�.N�Z�?��JX������`�'��m����Q��D���BG�� ȳ�$��Q�b��4n(.-�λ���O�r���\)�>o5?3�Ĝ��ΧS]�77g^k;��@��=��n��׆����4�AM�aE�����:��?��QZۇ3�$�4���ܺ��i\A�����_3_k��<?Sٲ�E��d���A�����nk�<QQ��!\ CR���p��l�р��ND�,R,�F�ʃ�"y>��G��yv�����IN��넎2%یƾ���Wm��L�<)�,'�V/{����_��$^?�eX�k˵�U�<�0mA.�]+G~��X2@��v�o^��r��BYۙ�O�`�BWeYa�]v�y��C�ҿ�l�A�ѲЎ�A��/�0Cw���4j�x0�^��;���L�ûMj�ǔ��u+�T�,�#�=�������g���x�췛��=�{=��k���I�؊v쏍zH}/��IT!�@�Z9G��$b�{Ghͼ[�$p�إ(�C���X �+Wx��y
��f�U�_��6���?A��Ĵ�0B��Im�&*J���։e���?c\�f�)�s7���Ä
��"���B󼉰a ��&�f3���+�ck�H�����Бm�T˅HTgC�lg��0�����F�ot�^6� �x�Eʸ[�|R�Z��j�@Ra�w�F��*d���1�̿����
=+[4Z�.7V����򝺆�̘��y:���s<�<��L��%��P�͘��$���� ���k~�jIM�����G��D�\�w����tƏf�����h������$�ܻno">���1����`�=�p���ԼИX�H����N�u���C	�0�ݓ���l֌�UM����`ٺ7��a9�hɅ������Y�)N<-�f��WwlB~=7���LC�߁�!��9J*��B�
ZB��=QUM2��N
}zK�r�Dn��d�	��g˚�"��Vj\�\�4Я>�ً{�mA�)��,5��N��K��1����MY������T��]��Q]��ah�s~u��F�/�*%�k��Łsc,Ma5��m7h<�S�5WF����G(;H�l�n�@�������'�Ô�ڌ j}H�؁���֬�
�{�D4x�l��NZ2�BW��̛#V�����a��B�l��c�K\�6�'N�1�B��Z�r�HY|>��nԄ�~�x���#ړ}���:o�_X�s��AW!}�'�ӭ�Y�'�l�g�tم|\YM�븪�>G2`Vף���l� iO�-��ʽ�T$P���K�{����ۺ��+������f~ڬzl��Y���&C$�4��o$q��n]:w��#%�(9x�ǞXv�������b��+����M�19�b���o�-\�΁�T&��2ڤ���
��[��>����K�����G���VD��V�: ����E� �]��+T�)$g����(m�j�];��/�ɔ�L��bF���/���1]�`��(o]l;6���Ѐ�$
�L�x"��Ѱ!P^!򪙢�":pߔ�+���:�4Q:m��U���PV�%N���^�.mVn����j{��
|��kz��!Tջ5�	�ܠ��  Q��g�LQ������A�پ�[b�K�#cqJ����|s8 �.`�e!J#K�84���6�s���B�O��VB���d��F�8�"�a��w���o`�z�I�ߙqF��{�D拾��E(���ꢧCς�K7�CY�j�t�6���y�B��+RK%��(�_Vȹ���H�aS	�/�{�����£�$�V�D��v44��bV��$,(rz��$	M���U�c��6�������h�`��V�@��Ѽ�g�]kX!�@�E8ϩ��N�c�k�����h��,�M�y�?%
s8|~8$u�xzc��*~���yX:)���y�<�W�qݕ��;gnV���'��8�����EuG�als0F�M�U�^;��t��s��:�$/X��wl��|W�o��M8k3&�gu�܀  	: c!�    �!
������&A`��*�0�HFa�J���u�u�˚Ĕ���΅�z�u_�Jxp�wOAz9��.6����e���˼��=ϯ=����e�����q��w��z���*�����X����L��a���!̶īv����/�nL�6F�sq7��2E[4 ���[��T�a X(%	�a"�LJ�AW������6���|�J�k����9�'C�j����::��O����t{<��s�%��>o�_/���o��P �a�w=^!�WN�d/�w���?��� ��0�6U/�j�dA������X}�N��D9���aO�Н�˂�)�Qz�'*E)�:mص�������]ϝ���  n u!�    �!
������ŁP`,�@�P*	Da���x��w�����5�T��/�����P�=�q짦�
��w�o�MY��پձ���p����*��?��N ˥��3���5�x�D/�����K�{۞u�>��$�)fD��s8�j}�A�X���rN�3"�� "�L
���`,#
��P�T(
 �LB3�­g����^y���W��3B8�g/Ky�>��4��k�v}����n=�ve��O�?���p�PR�X�2���Iؠ�Ϝ�_�����?��N��z9��z����y]�٨C��o����I�)��o�yy9���V�J�{�V�: ���"'�r�'OZ�b�$�p  �	 �!�    '     ���"��9Q<pj^a�`}��`��k��e���%��I h����_ʴ�+%��De��
M�P�c�j]�Lq��křX�4����`�ml�rޭgzP�t$��to�Q�A���,W��?k��
�N�:WbE#o2k�8��3�W�\5�\��Ohmq��p�:P^4��R�r���*lP�h�`��Y�#h:`��l�@��%i�'����Kݺ�.0!N��>m<Щ��K�%���H%�Orx���+�E2)�m;�?md�ǎMH�����Q�q\5�@ɚ_�3�ol�����{����s�b	'�Ẁ�޺!k�:f�+�M�p���t��F��|���}�L]-�����'!�wK��9�0�����A6�/G�ϥ}��ex��t�+���~��-�^91ķ�{D��H�2|�]W��J^�;�}�E�n��#��2=O)(PNYx����o?U��}uxpY�H lo8��tF[�ˏ��  	 `!�    �!
����ÁH`,d
�a!�U�������Ʀ�U�ԕ�V^���{k����v�E�g�v�B+=5��\�֬�~�NM}+���@vo�/(�*�z���NS>��ω�Oș=�*P��;�ۮ�B\�T鋠Y{N��VT[D�/Bs/���	"RW#rU�C� "ؐ6#���P�THBƢ��Z��7�N��y�6��y�^4=�og��������"Wk���χ%��m�}�~��nخ�+ᮍ���^��h�j� ���i'��b��{���W��= s��E�[��aC�r-�5:��(����6��9H�Uj��6�7Z
��g�E�B^�W�2�� ��ynE�S�  k ]!�    �!
������ �Xp�A@��$!rNnw��˴��3%�Uժ�#ȫYh�^�_T��p�f�>�������s�ԃa����		while ( bitSize > 0 )
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
