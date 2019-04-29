#include <assert.h>
#include "api.h"

// Discover some admin functions, for the purpose of the example
extern void user_change_permission(int, unsigned);
extern int room_create(unsigned);
extern void alarm_disable(void);

int main() {
	//Init (using admin functions)
	user_change_permission(42, 0);
	int living_room = room_create(1);
	int entrance = room_create(10);
	int wc = room_create(2);

	//Imaginary sequence of calls received from different terminals
	//(but from the same user)

	(receive_command(entrance, 42, F_ROOM_LOCK));
	(receive_command(living_room, 42, F_WINDOW_CLOSE));
	(receive_command(entrance, 42, F_WINDOW_CLOSE));
	(receive_command(wc, 42, F_ROOM_LOCK));
	(receive_command(entrance, 42, F_AC_COOL));
	//Failure because the AC is enabled
	(! receive_command(entrance, 42, F_WINDOW_OPEN));
	(receive_command(living_room, 42, F_WINDOW_OPEN));
	//Failure because a window is open
	(! receive_command(living_room, 42, F_AC_HEAT));
	(receive_command(living_room, 42, F_WINDOW_CLOSE));
	(receive_command(living_room, 42, F_AC_HEAT));
	//The heating causes a fire
	(receive_command(living_room, 42, F_ALARM_ENABLE));
	//Failure because the alarm is ringing
	(! receive_command(wc, 42, F_ROOM_LOCK));
	alarm_disable(); // Admin function used
	(receive_command(wc, 42, F_ROOM_LOCK));
	(! receive_command(wc, 42, F_ROOM_UNLOCK));
	user_change_permission(42, 5); //Admin function used
	(receive_command(wc, 42, F_ROOM_UNLOCK));
}
