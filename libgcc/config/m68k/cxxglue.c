#include "stabs.h"

extern void __register_frame_info(void *, void *);
extern void * _EH_FRAME_BEGINS__[];
extern void * _EH_FRAME_OBJECTS__[];

void __init_eh() {
    void ** frame = _EH_FRAME_BEGINS__;
    void ** object = _EH_FRAME_OBJECTS__;
    
    while (*frame) {
      __register_frame_info(*frame++, *object++);
    }
}

ADD2INIT(__init_eh,-5);
