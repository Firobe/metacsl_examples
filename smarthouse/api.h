#ifndef API_H
#define API_H
#define MAX_ROOM_NB 100
#define MAX_LOCK_NB 10
#define MAX_WINDOW_NB 10
#define USER_NB 100

enum api_func { F_ROOM_LOCK, F_ROOM_UNLOCK, F_WINDOW_OPEN,
				F_WINDOW_CLOSE, F_AC_DISABLE, F_AC_HEAT, F_AC_COOL,
				F_ALARM_ENABLE };

struct Room;

int receive_command(int rid, int uid, enum api_func call);

#endif
