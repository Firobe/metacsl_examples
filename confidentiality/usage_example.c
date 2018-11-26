#include "confidentiality.h"

void ex_correct_copy() {
	//Current level : 0
	char local_page[PAGE_SIZE];
	if(init()) {
		struct Page* p0 = page_alloc(); //Level 0
		if(p0 != NULL) {
			raise_conf_level(); //Current level : 1
			struct Page* p1 = page_alloc(); //Level 1
			if(p1 != NULL) {
				//Level 1 read from level 0
				assert(page_read(p0, local_page) == PAGE_OK);
				//Level 1 write to level 1
				assert(page_write(p1, local_page) == PAGE_OK);
				lower_conf_level();
				//Current level : 0
				//Level 0 read from level 0
				assert(page_read(p0, local_page) == PAGE_OK);
				//Level 0 write to level 1
				assert(page_write(p1, local_page) == PAGE_OK);

				page_free(p0);
				page_free(p1);
			}
		}
	}
}

void ex_incorrect_copy() {
	//Current level : 0
	char local_page[PAGE_SIZE];
	if(init()) {
		struct Page* p0 = page_alloc(); //Level 0
		raise_conf_level(); //Current level : 1
		struct Page* p1 = page_alloc(); //Level 1

		if(p0 != NULL && p1 != NULL) {
			//Level 1 read from level 1
			assert(page_read(p1, local_page) == PAGE_OK);
			//Level 1 write to level 0 : confidentiality error !
			assert(page_write(p0, local_page) == PAGE_ERROR);
			lower_conf_level(); //Current level : 1
			//Level 0 read from level 1 : confidentiality error !
			assert(page_read(p1, local_page) == PAGE_ERROR);
			//Level 0 write to level 1
			assert(page_write(p0, local_page) == PAGE_OK);

			page_free(p0);
			page_free(p1);
		}
	}
}

void ex_encrypt_read_decrypt() {
	char local_page[PAGE_SIZE];
	//Current level : 0
	if(init()) {
		raise_conf_level(); //Current level : 1
		struct Page* p = page_alloc(); //Level 1

		if(p != NULL) {
			//p goes from level 1 to 0
			assert(page_encrypt(p) == PAGE_OK);
			lower_conf_level(); //Current level : 0
			//Level 0 read from encrypted level 1
			assert(page_read(p, local_page) == PAGE_OK);
			//Level 0 cannot decrypt encrypted level 1
			assert(page_decrypt(p) == PAGE_ERROR);
			//Level 0 cannot reencrypt (modelization reasons)
			assert(page_encrypt(p) == PAGE_ERROR);
			raise_conf_level(); //Current level : 1
			//Level 1 can decrypt encrypted level 1
			assert(page_decrypt(p) == PAGE_OK);
			page_free(p);
		}
	}
}

void ex_encrypt_decrypt_read() {
	char local_page[PAGE_SIZE];
	if(init()) {
		raise_conf_level(); //Current level : 1
		struct Page* p = page_alloc(); //Level 1

		if(p != NULL) {
			//Superior encrypts and decrypts
			assert(page_encrypt(p) == PAGE_OK);
			assert(page_decrypt(p) == PAGE_OK);
			lower_conf_level(); //Current level : 0
			//Level 1 cannot read unencrypted level 1
			assert(page_read(p, local_page) == PAGE_ERROR);
			page_free(p);
		}
	}
}

int main() {
	ex_correct_copy();
	ex_incorrect_copy();
	ex_encrypt_read_decrypt();
	ex_encrypt_decrypt_read();
}
