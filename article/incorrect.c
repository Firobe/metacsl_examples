#include "specification.h"

struct Page* page_alloc() {
	struct Page* fp = find_free_page();
	if(fp != NULL) {
		fp->status = ALLOCATED;
		fp->level = user_level;
	}
	return fp;
}
void page_read(struct Page* from, char* buffer) {
	for(int i = 0 ; i < PAGE_LENGTH ; ++i)
		buffer[i] = from->data[i];
}
