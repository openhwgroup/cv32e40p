#include <stdio.h>
#include <stdlib.h>

#include "mem_stall.h"

int main(int argc, char *argv[])
{
#ifdef RANDOM_MEM_STALL
    activate_random_stall();
#endif
    /* write something to stdout */
    printf("hello world!\n");
    return EXIT_SUCCESS;
}
