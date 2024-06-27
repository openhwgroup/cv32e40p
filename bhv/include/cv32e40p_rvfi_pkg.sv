// Copyright 2024 Dolphin Design
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License");
// you may not use this file except in compliance with the License, or,
// at your option, the Apache License version 2.0.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////////
//                                                                                //
// Contributors: Davide Schiavone, OpenHW Group <davide@openhwgroup.org>          //
//               Halfdan Bechmann, Silicon Labs <halfdan.bechmann@silabs.com>     //
//               Yoann Pruvost, Dolphin Design <yoann.pruvost@dolphin.fr>         //
//                                                                                //
// Description:  Package to print info on RVFI interface                          //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////

package cv32e40p_rvfi_pkg;
  import cv32e40p_pkg::*;

  // RVFI only supports MHPMCOUNTER_WIDTH == 64
  parameter MHPMCOUNTER_WORDS = MHPMCOUNTER_WIDTH / 32;

  parameter STAGE_IF = 0;
  parameter STAGE_ID = 1;
  parameter STAGE_EX = 2;
  parameter STAGE_WB = 3;

  typedef enum logic [1:0] {  // Memory error types
    MEM_ERR_PMP      = 2'h2,
    MEM_ERR_ATOMIC   = 2'h1,
    MEM_ERR_IO_ALIGN = 2'h0
  } mem_err_t;

  typedef struct packed {  // Autonomously updated CSRs
    logic [31:0] mcycle;
    logic [31:0] mcycleh;
    logic [31:0] cycle;
    logic [31:0] cycleh;
    logic [31:0] mip;
    logic nmip;
  } rvfi_auto_csr_map_t;

  typedef struct packed {
    logic [31:0] jvt;
    logic [31:0] mstatus;
    logic [31:0] misa;
    logic [31:0] mie;
    logic [31:0] mtvec;
    logic [31:0] mstatush;
    logic [31:0] mtvt;
    logic [31:0] mcountinhibit;
    logic [31:0][31:0] mhpmevent;
    logic [31:0] mscratch;
    logic [31:0] mepc;
    logic [31:0] mcause;
    logic [31:0] mtval;
    logic [31:0] mip;
    logic [31:0] mnxti;
    logic [31:0] mintstatus;
    logic [31:0] mintthresh;
    logic [31:0] mscratchcsw;
    logic [31:0] mscratchcswl;
    logic [31:0] mclicbase;
    logic [31:0] tselect;
    logic [3:0][31:0] tdata;
    logic [31:0] tinfo;
    logic [31:0] mcontext;
    logic [31:0] scontext;
    logic [31:0] dcsr;
    logic [31:0] dpc;
    logic [1:0][31:0] dscratch;
    logic [31:0] mcycle;
    logic [31:0] minstret;
    logic [31:0][31:0] mhpmcounter;
    logic [31:0] mcycleh;
    logic [31:0] minstreth;
    logic [31:0][31:0] mhpmcounterh;
    logic [31:0] cycle;
    logic [31:0] instret;
    logic [31:0][31:0] hpmcounter;
    logic [31:0] cycleh;
    logic [31:0] instreth;
    logic [31:0][31:0] hpmcounterh;
    logic [31:0] mvendorid;
    logic [31:0] marchid;
    logic [31:0] mimpid;
    logic [31:0] mhartid;
    logic [31:0] mcounteren;
    logic [3:0][31:0] pmpcfg;
    logic [15:0][31:0] pmpaddr;
    logic [31:0] mseccfg;
    logic [31:0] mseccfgh;
    logic [31:0] mconfigptr;

  } rvfi_csr_map_t;

  typedef struct packed {
    logic [10:0] cause;
    logic debug;
    logic interrupt;
    logic wu;
  } rvfi_wu_t;

  typedef struct packed {
    logic [10:0] cause;
    logic interrupt;
    logic exception;
    logic intr;
  } rvfi_intr_t;

  typedef struct packed {
    logic [1:0] cause_type;
    logic [2:0] debug_cause;
    logic [5:0] exception_cause;
    logic debug;
    logic exception;
    logic trap;
  } rvfi_trap_t;

endpackage  // cv32e40p_rvfi_pkg
