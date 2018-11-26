#include "spec.h"
#include <assert.h>

int main() {
	//Init
	struct Room* living_room = room_create(1);
	struct Room* entrance = room_create(10);
	struct Room* wc = room_create(2);

	room_lock(entrance);
	window_close(living_room);
	window_close(entrance);

	//Example
	assert(room_lock(wc));
	assert(ac_cool(entrance));
	assert(! window_open(entrance)); //Failure because the AC is enabled
	assert(window_open(living_room));
	assert(! ac_heat(living_room)); //Failure because a window is open
	window_close(living_room);
	assert(ac_heat(living_room));
	//The heating causes a fire
	alarm_enable();
	//All locks are unlocked
	assert(! room_lock(wc)); //Failure because the alarm is ringing
	alarm_disable();
	assert(room_lock(wc));
	assert(! room_unlock(wc)); //Insufficient clearance
	user_change_clearance(5);
	assert(room_unlock(wc));
}
