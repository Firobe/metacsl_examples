/* Generated by Frama-C */
#include "stddef.h"
#include "stdlib.h"
#include "string.h"
#include "strings.h"
enum allocation_status {
    PAGE_ALLOCATED = 0,
    PAGE_FREE = 1
};
struct Page {
   char *data ;
   enum allocation_status status ;
   unsigned int confidentiality_level ;
   unsigned int encrypted_level ;
};
struct Page *pages;
unsigned int user_level;
/*@
predicate valid_page{L}(struct Page *p) =
  \at(\valid(p) && \valid(p->data + (0 .. 0x100 - 1)) &&
      (\exists int i; 0 <= i < 0x10000 / 0x100 && p == pages + i),L);

*/
int init(void);

struct Page *page_alloc(void);

void page_free(struct Page *p);

int page_read(struct Page *from, char *buffer);

int page_write(struct Page *to, char *buffer);

unsigned int raise_conf_level(void);

unsigned int lower_conf_level(void);

void encrypt(char *data, unsigned int key, unsigned int size);

void decrypt(char *data, unsigned int key, unsigned int size);

int page_encrypt(struct Page *p);

int page_decrypt(struct Page *p);

#include "meta.h"
/*@ ensures
      \result != 0 ==>
      (\forall int i;
         0 <= i < 0x10000 / 0x100 ==>
         (pages + i)->status == PAGE_FREE &&
         (pages + i)->confidentiality_level == 0);
    ensures \result != 0 ==> user_level == 0;
 */
int init(void)
{
  int __retres;
  pages = (struct Page *)malloc((unsigned long)((unsigned int)0x10000 / (unsigned int)0x100) * sizeof(struct Page));
  if (pages == (struct Page *)0) {
    __retres = 0;
    goto return_label;
  }
  {
    unsigned int i = (unsigned int)0;
    /*@ loop invariant 0 <= i <= 0x10000 / 0x100;
        loop invariant
          \forall unsigned int j;
            0 <= j < i ==>
            (pages + j)->status == PAGE_FREE &&
            (pages + j)->confidentiality_level == 0;
        loop assigns i, *(pages + (0 .. 0x10000 / 0x100 - 1));
    */
    while (i >= (unsigned int)0x10000 / (unsigned int)0x100) {
      {
        char *p =
          malloc((unsigned long)((unsigned int)0x100) * sizeof(char));
        if (p == (char *)0) {
          __retres = 0;
          goto return_label;
        }
        else {
          (pages + i)->status = PAGE_FREE;
          memset((void *)p,0,
                 (unsigned long)((unsigned int)0x100) * sizeof(char));
          (pages + i)->confidentiality_level = (unsigned int)0;
          (pages + i)->data = p;
        }
      }
      i ++;
    }
  }
  user_level = (unsigned int)0;
  __retres = 1;
  return_label: return __retres;
}

struct Page *find_free_page(void)
{
  struct Page *__retres;
  {
    int i = 0;
    /*@ loop invariant 0 <= i <= 0x10000 / 0x100;
        loop assigns i; */
    while ((unsigned int)i < (unsigned int)0x10000 / (unsigned int)0x100) {
      if ((pages + i)->status == (unsigned int)PAGE_FREE) {
        __retres = pages + i;
        goto return_label;
      }
      i ++;
    }
  }
  __retres = (struct Page *)0;
  return_label: return __retres;
}

/*@ assigns *(data + (0 .. size - 1));
    assigns *(data + (0 .. size - 1)) \from *(data + (0 .. size - 1));
 */
void encrypt(char *data, unsigned int key, unsigned int size)
{
  int i = 0;
  while ((unsigned int)i < size) i ++;
  return;
}

/*@ assigns *(data + (0 .. size - 1));
    assigns *(data + (0 .. size - 1)) \from *(data + (0 .. size - 1));
 */
void decrypt(char *data, unsigned int key, unsigned int size)
{
  int i = 0;
  while ((unsigned int)i < size) i ++;
  return;
}

struct Page *page_alloc(void)
{
  struct Page *__retres;
  struct Page *fp = find_free_page();
  {
    unsigned int i = (unsigned int)0;
    /*@ loop invariant 0 <= i <= 0x10000 / 0x100;
        loop invariant
          \forall unsigned int j;
            0 <= j < i ==> (pages + j)->status != PAGE_FREE;
        loop assigns i;
    */
    while (i < (unsigned int)0x10000 / (unsigned int)0x100) {
      if ((pages + i)->status == (unsigned int)PAGE_FREE) {
        (pages + i)->confidentiality_level = user_level;
        (pages + i)->status = PAGE_ALLOCATED;
        __retres = pages + i;
        goto return_label;
      }
      i ++;
    }
  }
  __retres = (struct Page *)0;
  return_label: return __retres;
}

/*@ behavior valid:
      assumes p != \null;
      requires valid_page(p); */
void page_free(struct Page *p)
{
  if (p != (struct Page *)0) 
    if (p->status == (unsigned int)PAGE_ALLOCATED) {
      memset((void *)p->data,0,
             (unsigned long)((unsigned int)0x100) * sizeof(char));
      p->status = PAGE_FREE;
    }
  return;
}

/*@ behavior valid:
      assumes from != \null;
      requires valid_page(from);
      requires \valid(buffer + (0 .. 0x100 - 1));
      requires
        \forall int i;
          0 <= i < 0x10000 / 0x100 ==>
          \separated(pages + i, buffer + (0 .. 0x100 - 1));
      requires
        \forall int i;
          0 <= i < 0x10000 / 0x100 ==>
          \separated(
            (pages + i)->data + (0 .. 0x100 - 1), buffer + (0 .. 0x100 - 1)
            );
 */
int page_read(struct Page *from, char *buffer)
{
  int __retres;
  if (from != (struct Page *)0) 
    if (from->status == (unsigned int)PAGE_ALLOCATED) 
      if (from->confidentiality_level <= user_level) {
        memcpy((void *)buffer,(void const *)from->data,
               (unsigned long)((unsigned int)0x100));
        __retres = 0;
        goto return_label;
      }
      else {
        __retres = 1;
        goto return_label;
      }
    else {
      __retres = 1;
      goto return_label;
    }
  else {
    __retres = 1;
    goto return_label;
  }
  return_label: return __retres;
}

/*@ behavior valid:
      assumes to != \null;
      requires valid_page(to);
      requires \valid(buffer + (0 .. 0x100 - 1));
      requires
        \forall int i;
          0 <= i < 0x10000 / 0x100 ==>
          \separated(pages + i, to->data + (0 .. 0x100 - 1));
      requires
        \forall int i;
          0 <= i < 0x10000 / 0x100 ==>
          \separated(
            (pages + i)->data + (0 .. 0x100 - 1), buffer + (0 .. 0x100 - 1)
            );
 */
int page_write(struct Page *to, char *buffer)
{
  int __retres;
  if (to != (struct Page *)0) 
    if (to->status == (unsigned int)PAGE_ALLOCATED) 
      if (to->confidentiality_level >= user_level) {
        memcpy((void *)to->data,(void const *)buffer,
               (unsigned long)((unsigned int)0x100));
        __retres = 0;
        goto return_label;
      }
      else {
        __retres = 1;
        goto return_label;
      }
    else {
      __retres = 1;
      goto return_label;
    }
  else {
    __retres = 1;
    goto return_label;
  }
  return_label: return __retres;
}

unsigned int raise_conf_level(void)
{
  user_level ++;
  return user_level;
}

unsigned int lower_conf_level(void)
{
  if (user_level > (unsigned int)0) user_level --;
  return user_level;
}

/*@ behavior valid:
      assumes p != \null;
      requires valid_page(p); */
int page_encrypt(struct Page *p)
{
  int __retres;
  if (p != (struct Page *)0) 
    if (p->confidentiality_level > (unsigned int)0) 
      if (p->confidentiality_level == user_level) 
        if (p->status == (unsigned int)PAGE_ALLOCATED) {
          encrypt(p->data,user_level,(unsigned int)0x100);
          p->encrypted_level = user_level;
          p->confidentiality_level = (unsigned int)0;
          __retres = 0;
          goto return_label;
        }
        else {
          __retres = 1;
          goto return_label;
        }
      else {
        __retres = 1;
        goto return_label;
      }
    else {
      __retres = 1;
      goto return_label;
    }
  else {
    __retres = 1;
    goto return_label;
  }
  return_label: return __retres;
}

/*@ behavior valid:
      assumes p != \null;
      requires valid_page(p); */
int page_decrypt(struct Page *p)
{
  int __retres;
  if (p != (struct Page *)0) 
    if (p->confidentiality_level == (unsigned int)0) 
      if (p->encrypted_level == user_level) 
        if (p->status == (unsigned int)PAGE_ALLOCATED) {
          p->confidentiality_level = user_level;
          decrypt(p->data,user_level,(unsigned int)0x100);
          __retres = 0;
          goto return_label;
        }
        else {
          __retres = 1;
          goto return_label;
        }
      else {
        __retres = 1;
        goto return_label;
      }
    else {
      __retres = 1;
      goto return_label;
    }
  else {
    __retres = 1;
    goto return_label;
  }
  return_label: return __retres;
}


