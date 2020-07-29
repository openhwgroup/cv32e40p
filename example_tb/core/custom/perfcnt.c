/*
**
** Copyright 2020 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*******************************************************************************
**
** Performance counter Sanity check
**
** Enables performance counters while executing a simple fibonacci test program.
** Read out the values and perform some simple sanity checks.
**
** Make sure to instantiate cv32e40p_wrapper with the parameter
** NUM_MHPMCOUNTERS = 29. (in core/cv32e40p_tb_subsystem.sv)
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int check(unsigned long long is, unsigned long long should)
{
  int err;
  err = is == should ? 0 : 1;
  if (err)
    printf("fail\n");
  else
    printf("pass\n");
  return err;
}

static int fib_rec(int i)
{
  return (i>1) ? fib_rec(i-1) + fib_rec(i-2) : i;
}

static int fib(int i)
{
  printf("starting fib(%d)...\n", i);
  for(int j=0; j<i; j++)
  {
    printf("fib(%d) = %d\n", j, fib_rec(j));
  }

  printf("finished fibonacci\n");
  return 0;
}

int main(int argc, char *argv[])
{
  int err_cnt = 0;

  unsigned int mhpmcounter[32];
  unsigned int mhpmcounterh[32];
	printf("\n\n");

  char txt [32][50];
  memset(txt, '\0', sizeof(txt));
  strcpy(txt [ 3], "mcycle");
  strcpy(txt [ 4], "mistret");
  strcpy(txt [ 5], "nr of load use hazards");
  strcpy(txt [ 6], "nr of jump register hazard");
  strcpy(txt [ 7], "cycles waiting for instruction fetches, excluding jumps and branches");
  strcpy(txt [ 8], "nr of loads");
  strcpy(txt [ 9], "nr of stores");
  strcpy(txt [10], "nr of jumps (unond)");
  strcpy(txt [11], "nr of branches (cond)");
  strcpy(txt [12], "nr of taken branches");
  strcpy(txt [13], "compressed instr counter");
  strcpy(txt [14], "extra cycles from elw");
  strcpy(txt [15], "APU smth");
  strcpy(txt [16], "APU smth");
  strcpy(txt [17], "APU smth");
  strcpy(txt [18], "APU smth");
  strcpy(txt [19], "mcycle | mistret = mcycle");
  strcpy(txt [20], "loads | stores = loads + stores");
  strcpy(txt [21], "branches | taken branches =  branches");
  strcpy(txt [22], "brnches | jumps < branches + jumps ");
  strcpy(txt [23], "mcycle");
  strcpy(txt [24], "minstret");
  strcpy(txt [25], "load hazards");
  strcpy(txt [26], "jump reg hazard");
  strcpy(txt [27], "fetch-wait");
  strcpy(txt [28], "loads");
  strcpy(txt [29], "stores");
  strcpy(txt [30], "jumps");
  strcpy(txt [31], "branches");

  // set event registers
  asm volatile("csrw 0x323, %0" :: "r" (0x1) );    // 3
  asm volatile("csrw 0x324, %0" :: "r" (0x2) );    // 4
  asm volatile("csrw 0x325, %0" :: "r" (0x4) );    // 5
  asm volatile("csrw 0x326, %0" :: "r" (0x8) );    // 6
  asm volatile("csrw 0x327, %0" :: "r" (0x10) );   // 7
  asm volatile("csrw 0x328, %0" :: "r" (0x20) );   // 8
  asm volatile("csrw 0x329, %0" :: "r" (0x40) );   // 9
  asm volatile("csrw 0x32a, %0" :: "r" (0x80) );   // 10
  asm volatile("csrw 0x32b, %0" :: "r" (0x100) );  // 11
  asm volatile("csrw 0x32c, %0" :: "r" (0x200) );  // 12
  asm volatile("csrw 0x32d, %0" :: "r" (0x400) );  // 13
  asm volatile("csrw 0x32e, %0" :: "r" (0x800) );  // 14
  asm volatile("csrw 0x32f, %0" :: "r" (0x1000) ); // 15
  asm volatile("csrw 0x330, %0" :: "r" (0x2000) ); // 16
  asm volatile("csrw 0x331, %0" :: "r" (0x4000) ); // 17
  asm volatile("csrw 0x332, %0" :: "r" (0x8000) ); // 18
  asm volatile("csrw 0x333, %0" :: "r" (0x0003) ); // 19
  asm volatile("csrw 0x334, %0" :: "r" (0x0030) ); // 20
  asm volatile("csrw 0x335, %0" :: "r" (0x0300) ); // 21
  asm volatile("csrw 0x336, %0" :: "r" (0x0180) ); // 22
  asm volatile("csrw 0x337, %0" :: "r" (0x0001) ); // 23
  asm volatile("csrw 0x338, %0" :: "r" (0x0002) ); // 24
  asm volatile("csrw 0x339, %0" :: "r" (0x0004) ); // 25
  asm volatile("csrw 0x33a, %0" :: "r" (0x0008) ); // 26
  asm volatile("csrw 0x33b, %0" :: "r" (0x0010) ); // 27
  asm volatile("csrw 0x33c, %0" :: "r" (0x0020) ); // 28
  asm volatile("csrw 0x33d, %0" :: "r" (0x0040) ); // 29
  asm volatile("csrw 0x33e, %0" :: "r" (0x0080) ); // 30
  asm volatile("csrw 0x33f, %0" :: "r" (0x0100) ); // 31

  // start counting (unset inhibit reg)
  asm volatile("csrw 0x320, %0" :: "r" (0x00000000) );

  fib(15);

  // stop counting (set inhibit reg)
  asm volatile("csrw 0x320, %0" :: "r" (0xffffffff) );

  asm volatile("csrr %0, 0xB00" : "=r"(mhpmcounter[0]));

  asm volatile("csrr %0, 0xB02" : "=r"(mhpmcounter[2]));
  asm volatile("csrr %0, 0xB03" : "=r"(mhpmcounter[3]));
  asm volatile("csrr %0, 0xB04" : "=r"(mhpmcounter[4]));
  asm volatile("csrr %0, 0xB05" : "=r"(mhpmcounter[5]));
  asm volatile("csrr %0, 0xB06" : "=r"(mhpmcounter[6]));
  asm volatile("csrr %0, 0xB07" : "=r"(mhpmcounter[7]));
  asm volatile("csrr %0, 0xB08" : "=r"(mhpmcounter[8]));
  asm volatile("csrr %0, 0xB09" : "=r"(mhpmcounter[9]));
  asm volatile("csrr %0, 0xB0A" : "=r"(mhpmcounter[10]));
  asm volatile("csrr %0, 0xB0B" : "=r"(mhpmcounter[11]));
  asm volatile("csrr %0, 0xB0C" : "=r"(mhpmcounter[12]));
  asm volatile("csrr %0, 0xB0D" : "=r"(mhpmcounter[13]));
  asm volatile("csrr %0, 0xB0E" : "=r"(mhpmcounter[14]));
  asm volatile("csrr %0, 0xB0F" : "=r"(mhpmcounter[15]));
  asm volatile("csrr %0, 0xB10" : "=r"(mhpmcounter[16]));
  asm volatile("csrr %0, 0xB11" : "=r"(mhpmcounter[17]));
  asm volatile("csrr %0, 0xB12" : "=r"(mhpmcounter[18]));
  asm volatile("csrr %0, 0xB13" : "=r"(mhpmcounter[19]));
  asm volatile("csrr %0, 0xB14" : "=r"(mhpmcounter[20]));
  asm volatile("csrr %0, 0xB15" : "=r"(mhpmcounter[21]));
  asm volatile("csrr %0, 0xB16" : "=r"(mhpmcounter[22]));
  asm volatile("csrr %0, 0xB17" : "=r"(mhpmcounter[23]));
  asm volatile("csrr %0, 0xB18" : "=r"(mhpmcounter[24]));
  asm volatile("csrr %0, 0xB19" : "=r"(mhpmcounter[25]));
  asm volatile("csrr %0, 0xB1A" : "=r"(mhpmcounter[26]));
  asm volatile("csrr %0, 0xB1B" : "=r"(mhpmcounter[27]));
  asm volatile("csrr %0, 0xB1C" : "=r"(mhpmcounter[28]));
  asm volatile("csrr %0, 0xB1D" : "=r"(mhpmcounter[29]));
  asm volatile("csrr %0, 0xB1E" : "=r"(mhpmcounter[30]));
  asm volatile("csrr %0, 0xB1F" : "=r"(mhpmcounter[31]));

  asm volatile("csrr %0, 0xB80" : "=r"(mhpmcounterh[0]));

  asm volatile("csrr %0, 0xB82" : "=r"(mhpmcounterh[2]));
  asm volatile("csrr %0, 0xB83" : "=r"(mhpmcounterh[3]));
  asm volatile("csrr %0, 0xB84" : "=r"(mhpmcounterh[4]));
  asm volatile("csrr %0, 0xB85" : "=r"(mhpmcounterh[5]));
  asm volatile("csrr %0, 0xB86" : "=r"(mhpmcounterh[6]));
  asm volatile("csrr %0, 0xB87" : "=r"(mhpmcounterh[7]));
  asm volatile("csrr %0, 0xB88" : "=r"(mhpmcounterh[8]));
  asm volatile("csrr %0, 0xB89" : "=r"(mhpmcounterh[9]));
  asm volatile("csrr %0, 0xB8A" : "=r"(mhpmcounterh[10]));
  asm volatile("csrr %0, 0xB8B" : "=r"(mhpmcounterh[11]));
  asm volatile("csrr %0, 0xB8C" : "=r"(mhpmcounterh[12]));
  asm volatile("csrr %0, 0xB8D" : "=r"(mhpmcounterh[13]));
  asm volatile("csrr %0, 0xB8E" : "=r"(mhpmcounterh[14]));
  asm volatile("csrr %0, 0xB8F" : "=r"(mhpmcounterh[15]));
  asm volatile("csrr %0, 0xB90" : "=r"(mhpmcounterh[16]));
  asm volatile("csrr %0, 0xB91" : "=r"(mhpmcounterh[17]));
  asm volatile("csrr %0, 0xB92" : "=r"(mhpmcounterh[18]));
  asm volatile("csrr %0, 0xB93" : "=r"(mhpmcounterh[19]));
  asm volatile("csrr %0, 0xB94" : "=r"(mhpmcounterh[20]));
  asm volatile("csrr %0, 0xB95" : "=r"(mhpmcounterh[21]));
  asm volatile("csrr %0, 0xB96" : "=r"(mhpmcounterh[22]));
  asm volatile("csrr %0, 0xB97" : "=r"(mhpmcounterh[23]));
  asm volatile("csrr %0, 0xB98" : "=r"(mhpmcounterh[24]));
  asm volatile("csrr %0, 0xB99" : "=r"(mhpmcounterh[25]));
  asm volatile("csrr %0, 0xB9A" : "=r"(mhpmcounterh[26]));
  asm volatile("csrr %0, 0xB9B" : "=r"(mhpmcounterh[27]));
  asm volatile("csrr %0, 0xB9C" : "=r"(mhpmcounterh[28]));
  asm volatile("csrr %0, 0xB9D" : "=r"(mhpmcounterh[29]));
  asm volatile("csrr %0, 0xB9E" : "=r"(mhpmcounterh[30]));
  asm volatile("csrr %0, 0xB9F" : "=r"(mhpmcounterh[31]));

  unsigned long long cnt [32];
  for (int i=0; i<32; i++)
  {
    if (i!=1)
      cnt[i] = mhpmcounter[i] + (mhpmcounterh[i]<<32);
  }

  // Print a summary to stdout
	printf("\n\n");
  printf("\nPerformance Counter Test\n");
  printf("------------------------\n");
  printf("\tmcycle        = %lld\n", cnt[0]);
  printf("\tminstret      = %lld\n", cnt[2]);
  for (int i=3; i<32; i++)
  {
    printf("\tmhpmcounter%d  = %lld - %s\n", i, cnt[i], txt[i]);
  }

	printf("\n\n");
  printf("checking...\n");

  printf("counter[3] = mcycle \t");
  err_cnt += check(cnt[0], cnt[3]);
  printf("counter[4] = minstret \t");
  err_cnt += check(cnt[2], cnt[4]);
  printf("counter[19]= mcycle \t");
  err_cnt += check(cnt[0], cnt[19]);
  printf("counter[20] = counter[7] + counter[8] \t");
  err_cnt += check(cnt[20], cnt[7]+ cnt[8]);
  printf("counter[21] = counter[11]\t");
  err_cnt += check(cnt[21],cnt[11]);
  printf("counter[22] = counter[10] + counter[11] \t");
  err_cnt += check(cnt[22], cnt[10]+ cnt[11]);
  printf("counter[23] = mcycle \t");
  err_cnt += check(cnt[23], cnt[0]);
  printf("counter[24] = minstret \t");
  err_cnt += check(cnt[24], cnt[2]);
  printf("counter[25] = counter[5] \t");
  err_cnt += check(cnt[25], cnt[5]);
  printf("counter[26] = counter[6] \t");
  err_cnt += check(cnt[26], cnt[6]);
  printf("counter[27] = counter[7] \t");
  err_cnt += check(cnt[27], cnt[7]);
  printf("counter[28] = counter[8] \t");
  err_cnt += check(cnt[28], cnt[8]);
  printf("counter[29] = counter[9] \t");
  err_cnt += check(cnt[29], cnt[9]);
  printf("counter[30] = counter[10] \t");
  err_cnt += check(cnt[30], cnt[10]);
  printf("counter[31] = counter[11] \t");
  err_cnt += check(cnt[31], cnt[11]);

  if (err_cnt)
    printf("FAILURE. %d errors\n\n", err_cnt);
  else
    printf("SUCCESS");

  return 0;

}
