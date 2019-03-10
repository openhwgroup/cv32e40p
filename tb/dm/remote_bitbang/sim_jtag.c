// See LICENSE.SiFive for license details.

#include <stdlib.h>
#include <stdio.h>
#include "remote_bitbang.h"

int init = 0;

jtag_tick(unsigned char *jtag_TCK, unsigned char *jtag_TMS,
          unsigned char *jtag_TDI, unsigned char *jtag_TRSTn,
          unsigned char jtag_TDO)

{
    if (!init) {
        // TODO: Pass in real port number
        init = rbs_init(0);
    }

    rbs_tick(jtag_TCK, jtag_TMS, jtag_TDI, jtag_TRSTn, jtag_TDO);
    fprintf(stderr,
            "Tick with: TCK=%hhd TMS=%hhd TDI=%hhd TRSTn=%hhd --> TDO=%hhd\n",
            *jtag_TCK, *jtag_TMS, *jtag_TDI, *jtag_TRSTn, jtag_TDO);

    return rbs_done() ? (rbs_exit_code() << 1 | 1) : 0;
}
