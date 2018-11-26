#include "specification.h"

struct Page* page_alloc() {
	struct Page* fp = find_free_page();
	if(fp != NULL) {
		fp->level = user_level;
		fp->status = ALLOCATED;
	}
	return fp;
}
void page_read(struct Page* from, char* buffer) {
	/* Note: this requirement is too strong (forbids reading from PUBLIC page to
	 * PUBLIC agent), but with it the property becomes easily provable.
	 * A requirement such as (user_level == CONFIDENTIAL ||
	 * from.level == PUBLIC) is provable but requires a lot of additional
	 * specification.
	 */
	if(user_level == CONFIDENTIAL) {
		//@ loop invariant user_level != PUBLIC;
		for(int i = 0 ; i < PAGE_LENGTH ; ++i)
			buffer[i] = from->data[i];
	}
}
