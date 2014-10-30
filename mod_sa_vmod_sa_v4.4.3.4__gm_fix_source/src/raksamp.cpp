#include "main.h"

int RPC_ServerJoin = 152;
int RPC_ServerQuit = 153;
int RPC_InitGame = 154;
int RPC_ClientJoin = 0x18;
int RPC_NPCJoin = 155;
int RPC_Death = 0x0C;
int RPC_RequestClass = 0x8A;
int RPC_RequestSpawn = 0x8B;
int RPC_SetInteriorId = 0x75;
int RPC_Spawn = 0x0B;
int RPC_Chat = 0x66;
int RPC_EnterVehicle = 0x19;
int RPC_ExitVehicle = 0x1A;
int RPC_DamageVehicle = 0x27;
int RPC_MenuSelect = 0x93;
int RPC_MenuQuit = 0x9B;
int RPC_ScmEvent = 0x90;
int RPC_AdminMapTeleport = 255;
int RPC_WorldPlayerAdd = 92;
int RPC_WorldPlayerDeath = 38;
int RPC_WorldPlayerRemove = 35;
int RPC_WorldVehicleAdd = 36;
int RPC_WorldVehicleRemove = 37;
int RPC_SetCheckpoint = 255;
int RPC_DisableCheckpoint = 255;
int RPC_SetRaceCheckpoint = 255;
int RPC_DisableRaceCheckpoint = 255;
int RPC_UpdateScoresPingsIPs = 0x1B;
int RPC_SvrStats = 255;
int RPC_GameModeRestart = 100;
int RPC_ConnectionRejected = 140;
int RPC_ClientMessage = 141;
int RPC_WorldTime = 106; //FOUND
int RPC_Pickup = 255;
int RPC_DestroyPickup = 255;
int RPC_DestroyWeaponPickup = 255;
int RPC_Weather = 19;
int RPC_SetTimeEx = 255;
int RPC_ToggleClock = 255;
int RPC_ServerCommand = 0x74;
int RPC_PickedUpPickup = 0x92;
int RPC_PickedUpWeapon = 255;
int RPC_VehicleDestroyed = 0x97;
int RPC_DialogResponse = 21;
int RPC_PlayAudioStream = 45;
int RPC_ClickPlayer = 0x16;
int RPC_PlayerUpdate = 255;
int RPC_ClickTextDraw = 0x52;
int RPC_MapMarker = 0x76;
int RPC_PlayerGiveTakeDamage = 0x54; //bool Give/Take, playerid, amount, weaponid
int RPC_EnterEditObject = 0x57;
int RPC_EditObject = 0x56;

int RPC_ScrSetSpawnInfo = 255;
int RPC_ScrSetPlayerTeam = 255;
int RPC_ScrSetPlayerSkin = 255;
int RPC_ScrSetPlayerName = 255;
int RPC_ScrSetPlayerPos = 255;
int RPC_ScrSetPlayerPosFindZ = 255;
int RPC_ScrSetPlayerHealth = 255;
int RPC_ScrPutPlayerInVehicle = 255;
int RPC_ScrRemovePlayerFromVehicle = 255;
int RPC_ScrSetPlayerColor = 255;
int RPC_ScrDisplayGameText = 72;
int RPC_ScrSetInterior = 255;
int RPC_ScrSetCameraPos = 255;
int RPC_ScrSetCameraLookAt = 255;
int RPC_ScrSetVehiclePos = 255;
int RPC_ScrSetVehicleZAngle = 255;
int RPC_ScrVehicleParams = 255;
int RPC_ScrSetCameraBehindPlayer = 255;
int RPC_ScrTogglePlayerControllable = 255;
int RPC_ScrPlaySound = 255;
int RPC_ScrSetWorldBounds = 255;
int RPC_ScrHaveSomeMoney = 255;
int RPC_ScrSetPlayerFacingAngle = 255;
int RPC_ScrResetMoney = 255;
int RPC_ScrResetPlayerWeapons = 255;
int RPC_ScrGivePlayerWeapon = 255;
int RPC_ScrRespawnVehicle = 255;
int RPC_ScrLinkVehicle = 255;
int RPC_ScrSetPlayerArmour = 255;
int RPC_ScrDeathMessage = 255;
int RPC_ScrSetMapIcon = 255;
int RPC_ScrDisableMapIcon = 255;
int RPC_ScrSetWeaponAmmo = 255;
int RPC_ScrSetGravity = 255;
int RPC_ScrSetVehicleHealth = 255;
int RPC_ScrAttachTrailerToVehicle = 255;
int RPC_ScrDetachTrailerFromVehicle = 255;
int RPC_ScrCreateObject = 255;
int RPC_ScrSetObjectPos = 255;
int RPC_ScrSetObjectRotation = 255;
int RPC_ScrDestroyObject = 255;
int RPC_ScrCreateExplosion = 255;
int RPC_ScrShowNameTag = 255;
int RPC_ScrMoveObject = 255;
int RPC_ScrStopObject = 255;
int RPC_ScrNumberPlate = 255;
int RPC_ScrTogglePlayerSpectating = 255;
int RPC_ScrSetPlayerSpectating = 255;
int RPC_ScrPlayerSpectatePlayer = 255;
int RPC_ScrPlayerSpectateVehicle = 255;
int RPC_ScrRemoveComponent = 255;
int RPC_ScrForceSpawnSelection = 255;
int RPC_ScrAttachObjectToPlayer = 255;
int RPC_ScrInitMenu = 75;
int RPC_ScrShowMenu = 76;
int RPC_ScrHideMenu = 77;
int RPC_ScrSetPlayerWantedLevel = 255;
int RPC_ScrShowTextDraw = 149; //FOUND
int RPC_ScrHideTextDraw = 255;
int RPC_ScrEditTextDraw = 255;
int RPC_ScrAddGangZone = 255;
int RPC_ScrRemoveGangZone = 255;
int RPC_ScrFlashGangZone = 255;
int RPC_ScrStopFlashGangZone = 255;
int RPC_ScrApplyAnimation = 255;
int RPC_ScrClearAnimations = 255;
int RPC_ScrSetSpecialAction = 255;
int RPC_ScrEnableStuntBonus = 255;
int RPC_ScrSetFightingStyle = 255;
int RPC_ScrSetPlayerVelocity = 255;
int RPC_ScrSetVehicleVelocity = 255;
int RPC_ScrToggleWidescreen = 255;
int RPC_ScrSetVehicleTireStatus = 255;
int RPC_ScrSetPlayerDrunkVisuals = 255;
int RPC_ScrSetPlayerDrunkHandling = 255;
int RPC_ScrDialogBox = 20;

int lastDialogID = 65535;
int lastDialogType = 65535;

//TODO: Give/Take damage func, ClickPlayer, ClickTextdraw, Menu

void SendWastedNotification(BYTE byteDeathReason, SHORT WhoWasResponsible)
{
	if (g_SAMP == NULL) return;
	//raknet = stGetRakNet();
	RakNet::BitStream bsPlayerDeath;
	bsPlayerDeath.Write(byteDeathReason);
	bsPlayerDeath.Write(WhoWasResponsible);
	g_SAMP->pRakClientInterface->RPC(&RPC_Death, &bsPlayerDeath, HIGH_PRIORITY, RELIABLE_ORDERED, 0, 0);
	//g_SAMP->pRakClientInterface->RPC(&RPC_Death, &bsPlayerDeath, HIGH_PRIORITY, RELIABLE_ORDERED, 0, 0);
}

void SendFakeUnoccupiedSyncData(USHORT VehicleID, float fPos[3])
{
	if ( g_SAMP == NULL ) return;
	raknet = stGetRakNet();
	RakNet::BitStream bs;
	UNOCCUPIED_SYNC_DATA sync;
	ZeroMemory(&sync, sizeof(sync));
	sync.vecTurnSpeed[0] = 9999999.99f;
	sync.vecTurnSpeed[1] = 9999999.99f;
	sync.vecTurnSpeed[2] = 9999999.99f;
	sync.fHealth = 0.0f;
	memcpy(sync.vecPos, fPos, sizeof(sync.vecPos));
	sync.VehicleID = VehicleID;
	bs.Write((BYTE)ID_UNOCCUPIED_SYNC);
	bs.Write((PCHAR)&sync, sizeof(UNOCCUPIED_SYNC_DATA));

	for ( int i = 0; i < 3; i++ )
		g_SAMP->pRakClientInterface->Send(&bs, HIGH_PRIORITY, UNRELIABLE_SEQUENCED, 0);
}
void SendFakeDriverSyncData(USHORT VehicleID, float fPos[3], float HealthCar, float Speed[3], WORD key)
{
	struct actor_info	*self = actor_info_get( ACTOR_SELF, ACTOR_ALIVE );	
		INCAR_SYNC_DATA picSync;
 memset(&picSync, 0, sizeof(INCAR_SYNC_DATA));
 RakNet::BitStream bsVehicleSync;
 picSync.VehicleID = VehicleID;
   picSync.vecPos[0] = fPos[0];
  picSync.vecPos[1] = fPos[1];
  picSync.vecPos[2] = fPos[2];
 picSync.fCarHealth = HealthCar;
 picSync.vecMoveSpeed[0] = Speed[0];
  picSync.vecMoveSpeed[1] = Speed[1];
   picSync.vecMoveSpeed[2] = Speed[2];
   picSync.wKeys = key;
 picSync.bytePlayerHealth = self->hitpoints;
 picSync.bytePlayerArmour = self->armor;
 bsVehicleSync.Write((BYTE)ID_VEHICLE_SYNC);
 bsVehicleSync.Write((PCHAR)&picSync,sizeof(INCAR_SYNC_DATA));
 g_SAMP->pRakClientInterface->Send(&bsVehicleSync, HIGH_PRIORITY, UNRELIABLE_SEQUENCED, 0);

}

void SendFakeTrailerToCar(USHORT TrailerID)
{
	vehicle_info	*vinfo = vehicle_info_get( VEHICLE_SELF, 0 );
	struct actor_info	*self = actor_info_get( ACTOR_SELF, ACTOR_ALIVE );	
		INCAR_SYNC_DATA picSync;
 memset(&picSync, 0, sizeof(INCAR_SYNC_DATA));
 RakNet::BitStream bsVehicleSync;
 picSync.VehicleID = g_Players->pLocalPlayer->inCarData.sVehicleID;
 float fPos[3];
 vect3_copy( &vinfo->base.matrix[4 * 3], fPos );
 
   picSync.vecPos[0] = fPos[0];
  picSync.vecPos[1] = fPos[1];
  picSync.vecPos[2] = fPos[2];
 picSync.fCarHealth = vinfo->hitpoints;
 picSync.vecMoveSpeed[0] = vinfo->speed[0];
  picSync.vecMoveSpeed[1] = vinfo->speed[1];
   picSync.vecMoveSpeed[2] = vinfo->speed[2];
 picSync.bytePlayerHealth = self->hitpoints;
 picSync.bytePlayerArmour = self->armor;
 picSync.TrailerID_or_ThrustAngle = TrailerID;
 bsVehicleSync.Write((BYTE)ID_VEHICLE_SYNC);
 bsVehicleSync.Write((PCHAR)&picSync,sizeof(INCAR_SYNC_DATA));
 g_SAMP->pRakClientInterface->Send(&bsVehicleSync, HIGH_PRIORITY, UNRELIABLE_SEQUENCED, 0);

}

void SendFakePassSyncData(USHORT VehicleID, float fPos[3], BYTE Seat)
{
		PASSENGER_SYNC_DATA picSync;
 memset(&picSync, 0, sizeof(PASSENGER_SYNC_DATA));
 RakNet::BitStream bsVehicleSync;
 picSync.VehicleID = VehicleID;
   picSync.vecPos[0] = fPos[0];
  picSync.vecPos[1] = fPos[1];
  picSync.vecPos[2] = fPos[2];
 picSync.byteSeatFlags = Seat;
 bsVehicleSync.Write((BYTE)ID_PASSENGER_SYNC);
 bsVehicleSync.Write((PCHAR)&picSync,sizeof(PASSENGER_SYNC_DATA));
 g_SAMP->pRakClientInterface->Send(&bsVehicleSync, HIGH_PRIORITY, UNRELIABLE_SEQUENCED, 0);

}
void SendFakeOnfootSyncData(float fPos[3], float Health, int byteCurrentWeapon, float speed[3])
{
 ONFOOT_SYNC_DATA picSync;
 memset(&picSync, 0, sizeof(ONFOOT_SYNC_DATA));
 RakNet::BitStream bsOnfootSync;
 picSync.byteHealth = Health;
 picSync.byteCurrentWeapon = byteCurrentWeapon;
 picSync.vecPos[0] = fPos[0];
 picSync.vecPos[1] = fPos[1];
 picSync.vecPos[2] = fPos[2];
 picSync.vecMoveSpeed[0] = speed[0];
 picSync.vecMoveSpeed[1] = speed[1];
 picSync.vecMoveSpeed[2] = speed[2];
 bsOnfootSync.Write((BYTE)ID_PLAYER_SYNC);
 bsOnfootSync.Write((PCHAR)&picSync,sizeof(ONFOOT_SYNC_DATA));
 g_SAMP->pRakClientInterface->Send(&bsOnfootSync, HIGH_PRIORITY, UNRELIABLE_SEQUENCED, 0);

}
void SendFakeSurfing(WORD VehicleID)
{
 ONFOOT_SYNC_DATA picSync;
 memset(&picSync, 0, sizeof(ONFOOT_SYNC_DATA));
 RakNet::BitStream bsOnfootSync;
 picSync.byteHealth = g_Players->pLocalPlayer->pSAMP_Actor->pGTA_Ped->hitpoints;
 picSync.byteCurrentWeapon = 0;
 picSync.vecPos[0] = g_Players->pLocalPlayer->onFootData.fPosition[0];
 picSync.vecPos[1] = g_Players->pLocalPlayer->onFootData.fPosition[1];
 picSync.vecPos[2] = g_Players->pLocalPlayer->onFootData.fPosition[2];
 picSync.vecMoveSpeed[0] = 0;
 picSync.vecMoveSpeed[1] = 0;
 picSync.vecMoveSpeed[2] = 0;
 picSync.vecSurfOffsets[0] = 1.0;
 picSync.vecSurfOffsets[1] = 1.0;
 picSync.vecSurfOffsets[2] = 1.0;
 picSync.wSurfInfo = VehicleID;
 bsOnfootSync.Write((BYTE)ID_PLAYER_SYNC);
 bsOnfootSync.Write((PCHAR)&picSync,sizeof(ONFOOT_SYNC_DATA));
 g_SAMP->pRakClientInterface->Send(&bsOnfootSync, HIGH_PRIORITY, UNRELIABLE_SEQUENCED, 0);

}
void SendEnterPlayerVehicle(USHORT VehicleID, BYTE seat)
{
	RakNet::BitStream VehicleEnter;

	VehicleEnter.Write(VehicleID);
	VehicleEnter.Write(seat);
	g_SAMP->pRakClientInterface->RPC(&RPC_EnterVehicle, &VehicleEnter, HIGH_PRIORITY, RELIABLE_ORDERED, 0, 0);
}
void SendFakeCarDeath(USHORT VehicleID)
{
	RakNet::BitStream VehicleBoom;
	VehicleBoom.Write(VehicleID);
	g_SAMP->pRakClientInterface->RPC(&RPC_VehicleDestroyed, &VehicleBoom, HIGH_PRIORITY, RELIABLE_ORDERED, 0, 0);
}
void SendFakeMenuSelectRow(BYTE RowID)
{
	RakNet::BitStream menu;
	menu.Write(RowID);
	g_SAMP->pRakClientInterface->RPC(&RPC_VehicleDestroyed, &menu, HIGH_PRIORITY, RELIABLE_ORDERED, 0, 0);
}
void SendClickPlayer(BYTE playerID, int source)
{
	RakNet::BitStream ClickPlayer;
	ClickPlayer.Write(playerID);
	ClickPlayer.Write(source);
	g_SAMP->pRakClientInterface->RPC(&RPC_ClickPlayer, &ClickPlayer, HIGH_PRIORITY, RELIABLE_ORDERED, 0, 0);
}
void SendDialogResponse(WORD wDialogID, BYTE bButtonID, WORD wListBoxItem, char *szInputResp)
{
		BYTE respLen = (BYTE)strlen(szInputResp);
	RakNet::BitStream bsSend;
	bsSend.Write(wDialogID);
	bsSend.Write(bButtonID);
	bsSend.Write(wListBoxItem);
	bsSend.Write(respLen);
	bsSend.Write(szInputResp, respLen);
	g_SAMP->pRakClientInterface->RPC(&RPC_DialogResponse, &bsSend, HIGH_PRIORITY, RELIABLE_ORDERED, 0, 0);
	//Log("Dialog ID: %d", wDialogID);
	
}
void SendExitPlayerVehicle(USHORT VehicleID)
{
	RakNet::BitStream bsSend;
	bsSend.Write(VehicleID);
	g_SAMP->pRakClientInterface->RPC(&RPC_ExitVehicle, &bsSend, HIGH_PRIORITY, RELIABLE_ORDERED, 0, 0);
}

void SendPickedUpPickup(int PickupID)
{
	RakNet::BitStream bsSend;
	bsSend.Write(PickupID);
	g_SAMP->pRakClientInterface->RPC(&RPC_PickedUpPickup, &bsSend, HIGH_PRIORITY, RELIABLE_ORDERED, 0, 0);
}
void SendPlayerDamage(USHORT playerid, float amountdam, int weaponid, bool takedam)
{
	RakNet::BitStream damage;
	damage.Write(takedam);
	damage.Write(playerid);
	damage.Write(amountdam);
	damage.Write(weaponid);
	g_SAMP->pRakClientInterface->RPC(&RPC_PlayerGiveTakeDamage, &damage, HIGH_PRIORITY, RELIABLE_ORDERED, 0, 0);

}