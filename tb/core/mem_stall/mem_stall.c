/*
* Copyright 2020 ETH Zürich and University of Bologna
*
* Licensed under the Apache License, Version 2.0 (the "License");
* you may not use this file except in compliance with the License.
* You may obtain a copy of the License at
*
*     http://www.apache.org/licenses/LICENSE-2.0
*
* Unless required by applicable law or agreed to in writing, software
* distributed under the License is distributed on an "AS IS" BASIS,
* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
* See the License for the specific language governing permissions and
* limitations under the License.
*/

// This routine enables random stalls on both I-MEM and D-MEM
void activate_random_stall(void)
{
  // Address vector for rnd_stall_reg, to control memory stalls/interrupt
  volatile unsigned int *rnd_stall_reg_ptr[16];

  // Setup the address vector
  rnd_stall_reg_ptr[0] = (unsigned int *) 0x16000000;
  for (int i = 1; i < 16; i++) {
    rnd_stall_reg_ptr[i] = rnd_stall_reg_ptr[i-1] + 1; // It is a pointer to int ("+ 1" means "the next int")
  }

  /* The interposition of the stall generator between CPU and MEM should happen BEFORE the stall generetor is active */
  // Interpose the stall generator between CPU and D-MEM (rnd_stall_reg[1])
  *rnd_stall_reg_ptr[1] = 0x01;
  // Interpose the stall generator between CPU and I-MEM (rnd_stall_reg[0])
  *rnd_stall_reg_ptr[0] = 0x01;

  // DATA MEMORY
  // Set max n. stalls on both GNT and VALID for RANDOM mode (rnd_stall_reg[5])
  *rnd_stall_reg_ptr[5] = 0x0a;
  // Set n. stalls on  GNT (rnd_stall_reg[7])
  *rnd_stall_reg_ptr[7] = 0x00;
  // Set n. stalls on VALID (rnd_stall_reg[9])
  *rnd_stall_reg_ptr[9] = 0x00;

  // INSTRUCTION MEMORY
  // Set max n. stalls on both GNT and VALID for RANDOM mode (rnd_stall_reg[4])
  *rnd_stall_reg_ptr[4] = 0x0a;
  // Set n. stalls on  GNT (rnd_stall_reg[6])
  *rnd_stall_reg_ptr[6] = 0x00;
  // Set n. stalls on VALID (rnd_stall_reg[8])
  *rnd_stall_reg_ptr[8] = 0x00;

  /* Activating stalls on D and I Mem has to be done as last operation. Do not change the order. */
  // Set stall mode on D-MEM (off=0, standard=1, random=2) (rnd_stall_reg[3])
  *rnd_stall_reg_ptr[3] = 0x02;
  // Set stall mode on I-MEM (off=0, standard=1, random=2) (rnd_stall_reg[2])
  *rnd_stall_reg_ptr[2] = 0x02;
}
