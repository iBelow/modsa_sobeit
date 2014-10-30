typedef struct _UNOCCUPIED_SYNC_DATA
{
#pragma pack ( 1 )
	USHORT VehicleID;
	short cvecRoll[3];
	short cvecDirection[3];
	BYTE unk[13];
	float vecPos[3];
	float vecMoveSpeed[3];
	float vecTurnSpeed[3];
	float fHealth;

} UNOCCUPIED_SYNC_DATA;

typedef struct _ONFOOT_SYNC_DATA
{
#pragma pack ( 1 )
	WORD lrAnalog;
	WORD udAnalog;
	WORD wKeys;
	float vecPos[3];
	float fQuaternion[4];
	BYTE byteHealth;
	BYTE byteArmour;
	BYTE byteCurrentWeapon;
	BYTE byteSpecialAction;	
	float vecMoveSpeed[3];
	float vecSurfOffsets[3];
	WORD wSurfInfo;
	int	iCurrentAnimationID;
} ONFOOT_SYNC_DATA;

typedef struct _INCAR_SYNC_DATA
{
#pragma pack ( 1 )
	USHORT VehicleID;
	WORD lrAnalog;
	WORD udAnalog;
	WORD wKeys;
	float fQuaternion[4];
	float vecPos[3];
	float vecMoveSpeed[3];
	float fCarHealth;
	BYTE bytePlayerHealth;
	BYTE bytePlayerArmour;
	BYTE byteCurrentWeapon;
	BYTE byteSirenOn;
	BYTE byteLandingGearState;
	WORD TrailerID_or_ThrustAngle;
	FLOAT fTrainSpeed;
} INCAR_SYNC_DATA;

typedef struct _PASSENGER_SYNC_DATA
{
#pragma pack ( 1 )
	USHORT VehicleID;
	BYTE byteSeatFlags : 7;
	BYTE byteDriveBy : 1;
	BYTE byteCurrentWeapon;
	BYTE bytePlayerHealth;
	BYTE bytePlayerArmour;
	WORD lrAnalog;
	WORD udAnalog;
	WORD wKeys;
	float vecPos[3];
} PASSENGER_SYNC_DATA;

typedef struct _AIM_SYNC_DATA
{
#pragma pack ( 1 )
	BYTE byteCamMode;
	float vecAimf1[3];
	float vecAimPos[3];
	float fAimZ;
	BYTE byteCamExtZoom : 6;	// 0-63 normalized
	BYTE byteWeaponState : 2;	// see eWeaponState
	BYTE bUnk;
} AIM_SYNC_DATA;

extern int RPC_ServerJoin;
extern int RPC_ServerQuit;
extern int RPC_InitGame;
extern int RPC_ClientJoin;
extern int RPC_NPCJoin;
extern int RPC_Death;
extern int RPC_RequestClass;
extern int RPC_RequestSpawn;
extern int RPC_SetInteriorId;
extern int RPC_Spawn;
extern int RPC_Chat;
extern int RPC_EnterVehicle;
extern int RPC_ExitVehicle;
extern int RPC_DamageVehicle;
extern int RPC_MenuSelect;
extern int RPC_MenuQuit;
extern int RPC_ScmEvent;
extern int RPC_AdminMapTeleport;
extern int RPC_WorldPlayerAdd;
extern int RPC_WorldPlayerDeath;
extern int RPC_WorldPlayerRemove;
extern int RPC_WorldVehicleAdd;
extern int RPC_WorldVehicleRemove;
extern int RPC_SetCheckpoint;
extern int RPC_DisableCheckpoint;
extern int RPC_SetRaceCheckpoint;
extern int RPC_DisableRaceCheckpoint;
extern int RPC_UpdateScoresPingsIPs;
extern int RPC_SvrStats;
extern int RPC_GameModeRestart;
extern int RPC_ConnectionRejected;
extern int RPC_ClientMessage;
extern int RPC_WorldTime;
extern int RPC_Pickup;
extern int RPC_DestroyPickup;
extern int RPC_DestroyWeaponPickup;
extern int RPC_Weather;
extern int RPC_SetTimeEx;
extern int RPC_ToggleClock;
extern int RPC_ServerCommand;
extern int RPC_PickedUpPickup;
extern int RPC_PickedUpWeapon;
extern int RPC_VehicleDestroyed;
extern int RPC_DialogResponse;
extern int RPC_PlayAudioStream;
extern int RPC_ClickPlayer;

extern int RPC_ScrSetSpawnInfo;
extern int RPC_ScrSetPlayerTeam;
extern int RPC_ScrSetPlayerSkin;
extern int RPC_ScrSetPlayerName;
extern int RPC_ScrSetPlayerPos;
extern int RPC_ScrSetPlayerPosFindZ;
extern int RPC_ScrSetPlayerHealth;
extern int RPC_ScrPutPlayerInVehicle;
extern int RPC_ScrRemovePlayerFromVehicle;
extern int RPC_ScrSetPlayerColor;
extern int RPC_ScrDisplayGameText;
extern int RPC_ScrSetInterior;
extern int RPC_ScrSetCameraPos;
extern int RPC_ScrSetCameraLookAt;
extern int RPC_ScrSetVehiclePos;
extern int RPC_ScrSetVehicleZAngle;
extern int RPC_ScrVehicleParams;
extern int RPC_ScrSetCameraBehindPlayer;
extern int RPC_ScrTogglePlayerControllable;
extern int RPC_ScrPlaySound;
extern int RPC_ScrSetWorldBounds;
extern int RPC_ScrHaveSomeMoney;
extern int RPC_ScrSetPlayerFacingAngle;
extern int RPC_ScrResetMoney;
extern int RPC_ScrResetPlayerWeapons;
extern int RPC_ScrGivePlayerWeapon;
extern int RPC_ScrRespawnVehicle;
extern int RPC_ScrLinkVehicle;
extern int RPC_ScrSetPlayerArmour;
extern int RPC_ScrDeathMessage;
extern int RPC_ScrSetMapIcon;
extern int RPC_ScrDisableMapIcon;
extern int RPC_ScrSetWeaponAmmo;
extern int RPC_ScrSetGravity;
extern int RPC_ScrSetVehicleHealth;
extern int RPC_ScrAttachTrailerToVehicle;
extern int RPC_ScrDetachTrailerFromVehicle;
extern int RPC_ScrCreateObject;
extern int RPC_ScrSetObjectPos;
extern int RPC_ScrSetObjectRotation;
extern int RPC_ScrDestroyObject;
extern int RPC_ScrCreateExplosion;
extern int RPC_ScrShowNameTag;
extern int RPC_ScrMoveObject;
extern int RPC_ScrStopObject;
extern int RPC_ScrNumberPlate;
extern int RPC_ScrTogglePlayerSpectating;
extern int RPC_ScrSetPlayerSpectating;
extern int RPC_ScrPlayerSpectatePlayer;
extern int RPC_ScrPlayerSpectateVehicle;
extern int RPC_ScrRemoveComponent;
extern int RPC_ScrForceSpawnSelection;
extern int RPC_ScrAttachObjectToPlayer;
extern int RPC_ScrInitMenu;
extern int RPC_ScrShowMenu;
extern int RPC_ScrHideMenu;
extern int RPC_ScrSetPlayerWantedLevel;
extern int RPC_ScrShowTextDraw;
extern int RPC_ScrHideTextDraw;
extern int RPC_ScrEditTextDraw;
extern int RPC_ScrAddGangZone;
extern int RPC_ScrRemoveGangZone;
extern int RPC_ScrFlashGangZone;
extern int RPC_ScrStopFlashGangZone;
extern int RPC_ScrApplyAnimation;
extern int RPC_ScrClearAnimations;
extern int RPC_ScrSetSpecialAction;
extern int RPC_ScrEnableStuntBonus;
extern int RPC_ScrSetFightingStyle;
extern int RPC_ScrSetPlayerVelocity;
extern int RPC_ScrSetVehicleVelocity;
extern int RPC_ScrToggleWidescreen;
extern int RPC_ScrSetVehicleTireStatus;
extern int RPC_ScrSetPlayerDrunkVisuals;
extern int RPC_ScrSetPlayerDrunkHandling;
extern int RPC_ScrDialogBox;
extern int RPC_PlayerUpdate;

extern int lastDialogID;
extern int lastDialogType;

void SendWastedNotification(BYTE byteDeathReason, SHORT WhoWasResponsible);
void SendFakeUnoccupiedSyncData(USHORT VehicleID, float fPos[3]);
void SendFakeDriverSyncData(USHORT VehicleID, float fPos[3], float HealthCar, float Speed[3], WORD key = 0);
void SendFakeTrailerToCar(USHORT TrailerID);
void SendFakePassSyncData(USHORT VehicleID, float fPos[3], BYTE Seat);
void SendFakeOnfootSyncData(float fPos[3], float Health, int byteCurrentWeapon, float speed[3]);
void SendFakeSurfing(WORD VehicleID);
void SendEnterPlayerVehicle(USHORT VehicleID, BYTE seat);
void SendExitPlayerVehicle(USHORT VehicleID);
void SendFakeCarDeath(USHORT VehicleID);
void SendFakeMenuSelectRow(BYTE RowID);
void SendPickedUpPickup(int PickupID);
void SendPlayerDamage(USHORT player, float amount, int weaponid, bool take);
void SendClickPlayer(BYTE playerID, int source);
void SendDialogResponse(WORD wDialogID, BYTE bButtonID, WORD wListBoxItem, char *szInputResp);