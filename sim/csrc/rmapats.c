// file = 0; split type = patterns; threshold = 100000; total count = 0.
#include <stdio.h>
#include <stdlib.h>
#include <strings.h>
#include "rmapats.h"

void  hsG_0__0 (struct dummyq_struct * I1390, EBLK  * I1385, U  I617);
void  hsG_0__0 (struct dummyq_struct * I1390, EBLK  * I1385, U  I617)
{
    U  I1653;
    U  I1654;
    U  I1655;
    struct futq * I1656;
    struct dummyq_struct * pQ = I1390;
    I1653 = ((U )vcs_clocks) + I617;
    I1655 = I1653 & ((1 << fHashTableSize) - 1);
    I1385->I663 = (EBLK  *)(-1);
    I1385->I664 = I1653;
    if (0 && rmaProfEvtProp) {
        vcs_simpSetEBlkEvtID(I1385);
    }
    if (I1653 < (U )vcs_clocks) {
        I1654 = ((U  *)&vcs_clocks)[1];
        sched_millenium(pQ, I1385, I1654 + 1, I1653);
    }
    else if ((peblkFutQ1Head != ((void *)0)) && (I617 == 1)) {
        I1385->I666 = (struct eblk *)peblkFutQ1Tail;
        peblkFutQ1Tail->I663 = I1385;
        peblkFutQ1Tail = I1385;
    }
    else if ((I1656 = pQ->I1293[I1655].I686)) {
        I1385->I666 = (struct eblk *)I1656->I684;
        I1656->I684->I663 = (RP )I1385;
        I1656->I684 = (RmaEblk  *)I1385;
    }
    else {
        sched_hsopt(pQ, I1385, I1653);
    }
}
#ifdef __cplusplus
extern "C" {
#endif
void SinitHsimPats(void);
#ifdef __cplusplus
}
#endif
