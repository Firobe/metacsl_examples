/* Generated by Frama-C */
enum api_func {
    F_ROOM_LOCK = 0,
    F_ROOM_UNLOCK = 1,
    F_WINDOW_OPEN = 2,
    F_WINDOW_CLOSE = 3,
    F_AC_DISABLE = 4,
    F_AC_HEAT = 5,
    F_AC_COOL = 6,
    F_ALARM_ENABLE = 7
};
struct Room;
enum alarm {
    ALARM_NONE = 0,
    ALARM_UNLOCKING = 1,
    ALARM_RINGING = 2
};
enum ac_status {
    AC_DISABLED = 0,
    AC_HEAT = 1,
    AC_COOL = 2
};
struct Room {
   unsigned int clearance_needed ;
   int door_lock_state ;
   int window_state ;
   enum ac_status ac_state ;
};
int receive_command(int rid, int uid, enum api_func call);

enum alarm alarm_status;

unsigned int cur_room_nb;

struct Room rooms[100];
unsigned int user_permissions[100];

int room_unlock(int uid, struct Room *room);

int room_lock(struct Room *room);

void alarm_enable(void);

int window_open(struct Room *room);

void window_close(struct Room *room);

void ac_disable(struct Room *room);

int ac_heat(struct Room *room);

int ac_cool(struct Room *room);

int room_create(unsigned int clearance_needed);

void alarm_disable(void);

void user_change_permission(int uid, unsigned int level);

void reset_all_permissions(void);

void force_unlock(struct Room *room);

enum alarm alarm_status = ALARM_NONE;
unsigned int cur_room_nb = (unsigned int)0;
unsigned int user_permissions[100] = {(unsigned int)0};
#include "meta.h"
int room_lock(struct Room *room)
{
  int __retres;
  if (alarm_status == (unsigned int)ALARM_NONE) {
    room->door_lock_state = 1;
    __retres = 1;
    goto return_label;
  }
  else {
    __retres = 0;
    goto return_label;
  }
  return_label: return __retres;
}

/*@ assigns room->door_lock_state;
    
    behavior ok:
      assumes
        user_permissions[uid] >= room->clearance_needed ||
        alarm_status == ALARM_UNLOCKING;
      ensures \old(room)->door_lock_state == 0;
 */
int room_unlock(int uid, struct Room *room)
{
  int __retres;
  int user_clearance = (int)user_permissions[uid];
  if ((unsigned int)user_clearance >= room->clearance_needed) goto _LOR;
  else 
    if (alarm_status == (unsigned int)ALARM_UNLOCKING) {
      _LOR: room->door_lock_state = 0;
            __retres = 1;
            goto return_label;
    }
    else {
      __retres = 0;
      goto return_label;
    }
  return_label: return __retres;
}

int window_open(struct Room *room)
{
  int __retres;
  if (room->ac_state == (unsigned int)AC_DISABLED) {
    room->window_state = 0;
    __retres = 1;
    goto return_label;
  }
  else {
    __retres = 0;
    goto return_label;
  }
  return_label: return __retres;
}

void window_close(struct Room *room)
{
  room->window_state = 1;
  return;
}

void ac_disable(struct Room *room)
{
  room->ac_state = AC_DISABLED;
  return;
}

int ac_heat(struct Room *room)
{
  int __retres;
  if (room->window_state != 0) {
    room->ac_state = AC_HEAT;
    __retres = 1;
    goto return_label;
  }
  else {
    __retres = 0;
    goto return_label;
  }
  return_label: return __retres;
}

int ac_cool(struct Room *room)
{
  int __retres;
  if (room->window_state != 0) {
    room->ac_state = AC_COOL;
    __retres = 1;
    goto return_label;
  }
  else {
    __retres = 0;
    goto return_label;
  }
  return_label: return __retres;
}

void alarm_enable(void)
{
  alarm_status = ALARM_UNLOCKING;
  {
    unsigned int r = (unsigned int)0;
    /*@ loop invariant 0 <= r <= cur_room_nb;
        loop invariant alarm_status == ALARM_UNLOCKING;
        loop invariant
          \forall unsigned int rp;
            0 <= rp < r ==> rooms[rp].door_lock_state == 0;
        loop variant -((cur_room_nb - r) - 1);
    */
    while (r < cur_room_nb) {
      room_unlock(0,& rooms[r]);
      r ++;
    }
  }
  alarm_status = ALARM_RINGING;
  return;
}

/*@ requires 0 <= rid < cur_room_nb; */
int receive_command(int rid, int uid, enum api_func call)
{
  int __retres;
  struct Room *room = & rooms[rid];
  if (call == (unsigned int)F_ROOM_LOCK) {
    int tmp;
    tmp = room_lock(room);
    __retres = tmp;
    goto return_label;
  }
  else 
    if (call == (unsigned int)F_ROOM_UNLOCK) {
      int tmp_0;
      tmp_0 = room_unlock(uid,room);
      __retres = tmp_0;
      goto return_label;
    }
    else 
      if (call == (unsigned int)F_WINDOW_OPEN) {
        int tmp_1;
        tmp_1 = window_open(room);
        __retres = tmp_1;
        goto return_label;
      }
      else 
        if (call == (unsigned int)F_WINDOW_CLOSE) {
          window_close(room);
          __retres = 1;
          goto return_label;
        }
        else 
          if (call == (unsigned int)F_AC_DISABLE) {
            window_close(room);
            __retres = 1;
            goto return_label;
          }
          else 
            if (call == (unsigned int)F_AC_HEAT) {
              int tmp_2;
              tmp_2 = ac_heat(room);
              __retres = tmp_2;
              goto return_label;
            }
            else 
              if (call == (unsigned int)F_AC_COOL) {
                int tmp_3;
                tmp_3 = ac_cool(room);
                __retres = tmp_3;
                goto return_label;
              }
              else 
                if (call == (unsigned int)F_ALARM_ENABLE) {
                  alarm_enable();
                  __retres = 1;
                  goto return_label;
                }
                else {
                  __retres = 0;
                  goto return_label;
                }
  return_label: return __retres;
}

void alarm_disable(void)
{
  alarm_status = ALARM_NONE;
  return;
}

void force_unlock(struct Room *room)
{
  room->door_lock_state = 0;
  return;
}

int room_create(unsigned int clearance_needed)
{
  int __retres;
  if (cur_room_nb >= (unsigned int)100) {
    __retres = -1;
    goto return_label;
  }
  else {
    unsigned int tmp;
    struct Room *rp = & rooms[cur_room_nb];
    rp->clearance_needed = clearance_needed;
    rp->ac_state = AC_DISABLED;
    rp->door_lock_state = 0;
    rp->window_state = 0;
    tmp = cur_room_nb;
    cur_room_nb ++;
    ;
    __retres = (int)tmp;
    goto return_label;
  }
  return_label: return __retres;
}

void user_change_permission(int uid, unsigned int level)
{
  user_permissions[uid] = level;
  return;
}

void reset_all_permissions(void)
{
  unsigned int u = (unsigned int)0;
  while (u < (unsigned int)100) {
    user_change_permission((int)u,(unsigned int)0);
    u ++;
  }
  return;
}

