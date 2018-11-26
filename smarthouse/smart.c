#include "spec.h"
#include <stdlib.h>

unsigned user_clearance = 0;
enum alarm alarm_status = ALARM_NONE;
unsigned cur_room_nb = 0;

//Add a room to the house and returns its handle
struct Room* room_create(int clearance_needed) {
	if(cur_room_nb >= MAX_ROOM_NB)
		return NULL;
	else {
		struct Room* rp = rooms + cur_room_nb;
		rp->clearance_needed = clearance_needed;
		rp->ac_state = AC_DISABLED;
		rp->door_lock_state = false;
		rp->window_state = false;
		++cur_room_nb;
		return rp;
	}
}

//Do not lock if the alarm is ringing
bool room_lock(struct Room* room) {
	if(alarm_status == ALARM_NONE) {
		room->door_lock_state = true;
		return true;
	} else return false;
}

//Unlock if the user have sufficient clearance or if the alarm is being enabled
bool room_unlock(struct Room* room) {
	if(user_clearance >= room->clearance_needed || alarm_status == ALARM_UNLOCKING) {
		room->door_lock_state = false;
		return true;
	} else return false;
}

//Open only if the AC is disabled
bool window_open(struct Room* room) {
	if(room->ac_state == AC_DISABLED) {
		room->window_state = false;
		return true;
	} else return false;
}

void window_close(struct Room* room) {
	room->window_state = true;
}

void ac_disable(struct Room* room) {
	room->ac_state = AC_DISABLED;
}

//Turn on only if the window is closed
bool ac_heat(struct Room* room) {
	if(room->window_state != false) {
		room->ac_state = AC_HEAT;
		return true;
	} else return false;
}

//Idem
bool ac_cool(struct Room* room) {
	if(room->window_state != false) {
		room->ac_state = AC_COOL;
		return true;
	} else return false;
}

//Open all the doors
void alarm_enable() {
	alarm_status = ALARM_UNLOCKING;
	/*@
		loop invariant 0 <= r <= cur_room_nb;
		loop invariant alarm_status == ALARM_UNLOCKING;
		loop invariant \forall unsigned rp; 0 <= rp < r
			==> rooms[rp].door_lock_state == false;
		loop variant cur_room_nb - r;
	*/
	for(unsigned r = 0 ; r < cur_room_nb ; ++r) {
		room_unlock(rooms + r);
	}
	alarm_status = ALARM_RINGING;
}

void alarm_disable() {
	alarm_status = ALARM_NONE;
}

//Supposed to be called from a real authentication process
void user_change_clearance(unsigned c) {
	user_clearance = c;
}
