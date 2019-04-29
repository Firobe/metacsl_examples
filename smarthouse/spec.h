#ifndef SPEC_H
#define SPEC_H

#include "api.h"

/*
	SMART HOUSE EXAMPLE
	
	We (simplistically) model a house as a set of room, where each room
	have a door lock, a window and a AC system. Each lock can be locked or
	unlocked, each window can be open or closed and each AC system can be
	disabled, heating or cooling.

	There is a global level of current user clearance, and each lock has a
	minimal authentication level to open it.

	The goal was to write an API of small functions, and to specify it with the
	following meta-properties:

	- P1: only the unlocking function can open a door lock
	- P2: a lock can only be opened if the user has sufficient clearance
	  or if the alarm is being enabled
	- P3: whenever the alarm is ringing, all doors locks must be open
	- P4: whenever a window is open, the AC in the room must be disabled

	Each function in the API was minimally specified with function contracts so
	as the proof of the meta-properties to succeed.
*/

//=================== COMPLETE HEADER ============

//The ALARM_UNLOCKING state marks the transition from NONE to
//RINGING, where all locks are unlocked. After that, no lock can be
//changed until the alarm is switched off. This transition state is to
//avoid a conflict between properties P2 and P3.
enum alarm {ALARM_NONE, ALARM_UNLOCKING, ALARM_RINGING};
enum ac_status {AC_DISABLED, AC_HEAT, AC_COOL};

struct Room {
	unsigned clearance_needed; //authentication_level needed to unlock
	int door_lock_state; //1: closed
	int window_state; //1: closed
	enum ac_status ac_state;
};

extern enum alarm alarm_status;
extern unsigned cur_room_nb; //Current number of rooms
extern struct Room rooms[MAX_ROOM_NB]; //Static array of rooms
extern unsigned user_permissions[USER_NB];

//================ USER SPACE FUNCTIONS =============

/*@
	// Partial specification required for the proof
	assigns room->door_lock_state;
	behavior ok:
		assumes user_permissions[uid] >= room->clearance_needed
				|| alarm_status == ALARM_UNLOCKING;
		ensures room->door_lock_state == 0;
*/
int room_unlock(int uid, struct Room* room);
int room_lock(struct Room* room);

void alarm_enable();

int window_open(struct Room* room);
void window_close(struct Room* room);

void ac_disable(struct Room* room);
int ac_heat(struct Room* room);
int ac_cool(struct Room* room);

int room_create(unsigned);
void alarm_disable();
void user_change_permission(int, unsigned);
void reset_all_permissions();
void force_unlock(struct Room* room);

//==================== SPECIFICATION ===================

/*@
	//A room structure is valid iff it is stored in the global array
	//Every API function requires its argument to be valid in that respect
	predicate valid_room(struct Room* r) =
		\exists unsigned i; 0 <= i < cur_room_nb && r == rooms + i;
*/


/*@ meta \macro,
		\name(forall_room),
		\arg_nb(2),
		\forall unsigned ri; 0 <= ri < cur_room_nb ==>
		\let \param_1 = rooms + ri; \param_2;
	meta \macro,
		\name(\constant),
		\arg_nb(1),
		\separated(\written, \param_1);
*/

#define USER_SET (\callees(receive_command))

/*@ meta \prop,
		\name(valid_room),
		\targets(USER_SET),
		\context(\precond),
		\tguard(valid_room(\formal(room)));
*/

/*@ meta \prop,
		\name(only_room_unlock_unlocks),
		\targets(\diff(USER_SET, room_unlock)),
		\context(\writing),
	forall_room(r,
		\at(r->door_lock_state, Before) != 0 //Iif 
		&& \at(r->door_lock_state, After) == 0
		==> \constant(&r->door_lock_state)
	);
*/

/*@ meta \prop,
		\name(unlocking_needs_permission_or_alarm),
		\targets(USER_SET),
		\context(\writing),
	forall_room(r,
		\at(r->door_lock_state, Before) != 0
		&& \at(r->door_lock_state, After) == 0
		&& \fguard(user_permissions[\formal(uid)] < r->clearance_needed)
		&& alarm_status != ALARM_UNLOCKING
		==> \constant(&r->door_lock_state)
	);
*/

/*@ meta \prop,
		\name(alarm_not_disabled_by_user),
		\targets(USER_SET),
		\context(\writing),
	\at(alarm_status, Before) != AC_DISABLED
	&& \at(alarm_status, After) == AC_DISABLED
	==> \constant(&alarm_status);
*/

/*@ meta \prop,
		\name(permissions_constant),
		\targets(USER_SET),
		\context(\writing),
		\constant(user_permissions + (0 .. USER_NB));
*/

/*@ meta \prop,
		\name(no_door_closed_when_alarm),
		\targets(\ALL),
		\context(\strong_invariant),
	alarm_status == ALARM_RINGING ==>
	forall_room(r, r->door_lock_state == 0);
*/

/*@ meta \prop,
		\name(no_ac_if_window_open),
		\targets(\ALL),
		\context(\strong_invariant),
	forall_room(r,
		r->window_state == 0
		==> r->ac_state == AC_DISABLED
	);
*/

#endif
