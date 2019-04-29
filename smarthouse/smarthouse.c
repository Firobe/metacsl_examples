#include "spec.h"

enum alarm alarm_status = ALARM_NONE;
struct Room rooms[MAX_ROOM_NB]; //Static array of rooms
unsigned cur_room_nb = 0;
unsigned user_permissions[USER_NB] = {0};

//Do not lock if the alarm is ringing
int room_lock(struct Room* room) {
	if(alarm_status == ALARM_NONE) {
		room->door_lock_state = 1;
		return 1;
	} else return 0;
}

//Unlock if the user have sufficient clearance or if the alarm is being enabled
int room_unlock(int uid, struct Room* room) {
	int user_clearance = user_permissions[uid];
	if(user_clearance >= room->clearance_needed || alarm_status == ALARM_UNLOCKING) {
		room->door_lock_state = 0;
		return 1;
	} else return 0;
}

//Open only if the AC is disabled
int window_open(struct Room* room) {
	if(room->ac_state == AC_DISABLED) {
		room->window_state = 0;
		return 1;
	} else return 0;
}

void window_close(struct Room* room) {
	room->window_state = 1;
}

void ac_disable(struct Room* room) {
	room->ac_state = AC_DISABLED;
}

//Turn on only if the window is closed
int ac_heat(struct Room* room) {
	if(room->window_state != 0) {
		room->ac_state = AC_HEAT;
		return 1;
	} else return 0;
}

//Idem
int ac_cool(struct Room* room) {
	if(room->window_state != 0) {
		room->ac_state = AC_COOL;
		return 1;
	} else return 0;
}

//Open all the doors
void alarm_enable() {
	alarm_status = ALARM_UNLOCKING;
	/*@
		loop invariant 0 <= r <= cur_room_nb;
		loop invariant alarm_status == ALARM_UNLOCKING;
		loop invariant \forall unsigned rp; 0 <= rp < r
			==> rooms[rp].door_lock_state == 0;
		loop variant cur_room_nb - r;
	*/
	for(unsigned r = 0 ; r < cur_room_nb ; ++r) {
		room_unlock(0, rooms + r);
	}
	alarm_status = ALARM_RINGING;
}

/*@ requires 0 <= rid < cur_room_nb; */
int receive_command(int rid, int uid, enum api_func call) {
	struct Room* room = rooms + rid;
	if (call == F_ROOM_LOCK)
		return room_lock(room);
	else if (call == F_ROOM_UNLOCK)
		return room_unlock(uid, room);
	else if (call == F_WINDOW_OPEN)
		return window_open(room);
	else if (call == F_WINDOW_CLOSE) {
		window_close(room);
		return 1;
	}
	else if (call == F_AC_DISABLE) {
		window_close(room);
		return 1;
	}
	else if (call == F_AC_HEAT)
		return ac_heat(room);
	else if (call == F_AC_COOL)
		return ac_cool(room);
	else if (call == F_ALARM_ENABLE) {
		alarm_enable();
		return 1;
	}
	else return 0;
}

void alarm_disable() {
	alarm_status = ALARM_NONE;
}

void force_unlock(struct Room* room) {
	room->door_lock_state = 0;
}

//Add a room to the house and returns its handle
int room_create(unsigned clearance_needed) {
	if(cur_room_nb >= MAX_ROOM_NB)
		return -1;
	else {
		struct Room* rp = rooms + cur_room_nb;
		rp->clearance_needed = clearance_needed;
		rp->ac_state = AC_DISABLED;
		rp->door_lock_state = 0;
		rp->window_state = 0;
		return cur_room_nb++;
	}
}

void user_change_permission(int uid, unsigned level) {
	user_permissions[uid] = level;
}

void reset_all_permissions() {
	for(unsigned u = 0 ; u < USER_NB ; ++u)
		user_change_permission(u, 0);
}
