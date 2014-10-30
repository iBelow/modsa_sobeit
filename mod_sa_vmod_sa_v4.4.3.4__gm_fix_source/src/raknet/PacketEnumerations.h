/* -*- mode: c++; c-file-style: raknet; tab-always-indent: nil; -*- */
/**
 * @ingroup RALNET_MESSAGE_ID
 * @file 
 * @brief Define RakNet internal packet identifier 
 *
 * This file is part of RakNet Copyright 2003, 2004
 * Rakkarsoft LLC and Kevin Jenkins.
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
#ifndef __PACKET_ENUMERATIONS_H
#define __PACKET_ENUMERATIONS_H 
/**
 * @defgroup RAKNET_MESSAGE_ID Message Identifier 
 * 
 * You should not edit the file PacketEnumerations.h as it is a part of RakNet static library
 * To define your own message id, define an enum following the code example that follows. 
 *
 * @code
 * enum {
 *   ID_MYPROJECT_MSG_1 = ID_RESERVERD_9 + 1, 
 *   ID_MYPROJECT_MSG_2, 
 *    ... 
 * };
 * @endcode 
 *
 * @note RakNet define message ID as a 1 byte information. If you
 * require more than 256 message IDs do not reuse the function
 * Multiplayer::GetPacketIdentifier and replace the existing one by a
 * correct version of this function the version. In this case you can
 * integrate in the code of your project the file Multiplayer.h and
 * edit this file to fits your needs.
 */

enum
{
	ID_SET_RANDOM_NUMBER_SEED,
	ID_SECURED_CONNECTION_RESPONSE,
	ID_SECURED_CONNECTION_CONFIRMATION,
	ID_CONNECTION_REQUEST = 6,
	ID_AUTH_KEY,
	ID_CONNECTED_PONG = 9,
	ID_INTERNAL_PING = 10,
	ID_PING,
	ID_PING_OPEN_CONNECTIONS,
	ID_REQUEST_STATIC_DATA,
	ID_RPC = 16,
	ID_RPC_REPLY,
	ID_RPC_MAPPING,
	ID_BROADCAST_PINGS,
	ID_DETECT_LOST_CONNECTIONS,
	ID_OPEN_CONNECTION_REQUEST,
	ID_OPEN_CONNECTION_REPLY,
	ID_PAD1,
	ID_CONNECTION_REQUEST_ACCEPTED,
	ID_CONNECTION_ATTEMPT_FAILED,
	ID_NEW_INCOMING_CONNECTION,
	ID_NO_FREE_INCOMING_CONNECTIONS,
	ID_DISCONNECTION_NOTIFICATION,	
	ID_CONNECTION_LOST,
	ID_RSA_PUBLIC_KEY_MISMATCH,
	ID_CONNECTION_BANNED,
	ID_INVALID_PASSWORD,
	ID_MODIFIED_PACKET,
	ID_TIMESTAMP,
	ID_PONG,
	ID_RECEIVED_STATIC_DATA,
	ID_REMOTE_DISCONNECTION_NOTIFICATION,
	ID_REMOTE_CONNECTION_LOST,
	ID_REMOTE_NEW_INCOMING_CONNECTION,
	ID_REMOTE_EXISTING_CONNECTION,
	ID_REMOTE_STATIC_DATA,
	// ...
	ID_ADVERTISE_SYSTEM = 51,

	ID_UNOCCUPIED_SYNC = 0xD1,
	ID_WEAPONS_UPDATE,
	ID_PASSENGER_SYNC,
	ID_PLAYER_SYNC,
	ID_MARKERS_SYNC,
	ID_AIM_SYNC,
	ID_SPECTATOR_SYNC,
	ID_TRAILER_SYNC,
	ID_VEHICLE_SYNC,
	ID_RCON_COMMAND,
	ID_RCON_RESPONCE,
	ID_STATS_UPDATE,
};

#endif
