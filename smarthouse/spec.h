#include <stdbool.h>

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

#define MAX_ROOM_NB 100
#define MAX_LOCK_NB 10
#define MAX_WINDOW_NB 10

//The ALARM_UNLOCKING state marks the transition from NONE to
//RINGING, where all locks are unlocked. After that, no lock can be
//changed until the alarm is switched off. This transition state is to
//avoid a conflict between properties P2 and P3.
enum alarm {ALARM_NONE, ALARM_UNLOCKING, ALARM_RINGING};
enum ac_status {AC_DISABLED, AC_HEAT, AC_COOL};

struct Room {
	unsigned clearance_needed; //authentication_level needed to unlock
	bool door_lock_state; //true: closed
	bool window_state; //true: closed
	enum ac_status ac_state;
};

extern unsigned user_clearance;
extern enum alarm alarm_status;

extern unsigned cur_room_nb; //Current number of rooms
struct Room rooms[MAX_ROOM_NB]; //Static array of rooms

struct Room* room_create();

/*@
	//A room structure is valid iff it is stored in the global array
	//Every API function requires its argument to be valid in that respect
	predicate valid_room(struct Room* r) =
		\exists unsigned i; 0 <= i < cur_room_nb && r == rooms + i;
*/

/*@ requires valid_room(room); */
bool room_lock(struct Room* room);

/*@
	requires valid_room(room);
	// Partial specification required for the proof
	assigns room->door_lock_state;
	behavior ok:
		assumes user_clearance >= room->clearance_needed
				|| alarm_status == ALARM_UNLOCKING;
		ensures room->door_lock_state == false;
*/
bool room_unlock(struct Room* room);

void alarm_enable();
void alarm_disable();

/*@ requires valid_room(room); */
bool window_open(struct Room* room);
/*@ requires valid_room(room); */
void window_close(struct Room* room);

/*@ requires valid_room(room); */
void ac_disable(struct Room* room);
/*@ requires valid_room(room); */
bool ac_heat(struct Room* room);
/*@ requires valid_room(room); */
bool ac_cool(struct Room* room);

void user_change_clearance(unsigned);

//====================== METAPROPERTIES =======================

/*@
	meta P1:
		//Suppose an instruction in any function except room_unlock
		//that writes into the memory
		\forall function f;
		!\subset(f, \f(room_unlock)) ==> \writing(f),
		\forall unsigned ri; 0 <= ri < cur_room_nb ==>
		//If there is a room
		\let r = rooms + ri;
		//For which the lock is closed before an instruction
		\at(r->door_lock_state, Before) != false //Iif 
		//And open after
		&& \at(r->door_lock_state, After) == false
		//Then it mustn't be because we are changing it directly
		==> \separated(\written, &r->door_lock_state);
*/

/*@
	meta P2: 
		//Suppose an instruction in any function writes into the memory
		\forall function f; \writing(f),
		\forall unsigned ri; 0 <= ri < cur_room_nb ==>
		//If there is a room
		\let r = rooms + ri;
		//For which the lock is closed before an instruction
		\at(r->door_lock_state, Before) != false
		//And open after
		&& \at(r->door_lock_state, After) == false
		//And the user has insufficient clearance
		&& user_clearance < r->clearance_needed
		//And the alarm is not being enabled
		&& alarm_status != ALARM_UNLOCKING
		//Then it mustn't be because we are changing it directly
		==> \separated(\written, &r->door_lock_state);
*/

/*@
	meta P3:
		//At every point of every function
		\forall function f; \strong_invariant(f),
		//If the alarm is ringing
		alarm_status == ALARM_RINGING ==>
		//Then every door must be unlocked
		\forall unsigned ri; 0 <= ri < cur_room_nb ==>
		rooms[ri].door_lock_state == false;
*/

/*@
	meta P4:
		//At every point of every function
		\forall function f; \strong_invariant(f),
		//For any room r
		\forall unsigned ri; 0 <= ri < cur_room_nb ==>
		\let r = rooms + ri;
		//If its window is open
		r->window_state == false
		//Then the AC must be disabled
		==> r->ac_state == AC_DISABLED;
*/
