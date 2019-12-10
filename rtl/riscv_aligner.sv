// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Pasquale Davide Schiavone - pschiavo@iis.ee.ethz.ch        //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@greenwaves-technologies.com            //
//                                                                            //
// Design Name:    Instrctuon Aligner                                         //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module riscv_aligner
(
  input  logic           clk,
  input  logic           rst_n,

  input  logic           fetch_valid_i,
  output logic           raw_instr_hold_o,

  input  logic [31:0]    mem_content_i,
  output logic [31:0]    instr_o,
  output logic           instr_valid_o,
  output logic           instr_compress_o,

  input  logic [31:0]    branch_addr_i,
  input  logic           branch_i,

  output logic [31:0]    pc_o
);

  enum logic [2:0]  {ALIGNED32, ALIGNED16, MISALIGNED32, MISALIGNED16, BRANCH_MISALIGNED} CS, NS;

  logic [15:0]       r_instr;
  logic [31:0]       pc_q, pc_n;

  assign pc_o = pc_q;

  always_ff @(posedge clk or negedge rst_n)
  begin : proc_SEQ_FSM
    if(~rst_n) begin
       CS        <= ALIGNED32;
       r_instr   <= '0;
       pc_q      <= '0;
    end else begin
        if(branch_i || instr_valid_o || fetch_valid_i) begin
          pc_q      <= pc_n;
          CS        <= NS;
          r_instr <= mem_content_i[31:16];
        end
    end
  end

  always_comb
  begin

    //default outputs
    pc_n             = pc_q;
    instr_valid_o    = fetch_valid_i;
    instr_o          = mem_content_i;
    instr_compress_o = 1'b0;
    raw_instr_hold_o = 1'b0;
    NS               = CS;

    case(CS)
      ALIGNED32:
      begin
            if(mem_content_i[1:0] == 2'b11) begin
                /*
                  Before we fetched a 32bit aligned instruction
                  Therefore, now the address is aligned too and it is 32bits
                */
                NS               = ALIGNED32;
                pc_n             = pc_q+4;
                instr_o          = mem_content_i;
                instr_compress_o = 1'b0;
            end else begin
                /*
                  Before we fetched a 32bit aligned instruction
                  Therefore, now the address is aligned too and it is 16bits
                */
                NS               = ALIGNED16;
                pc_n             = pc_q+2;
                instr_o          = {16'b0,mem_content_i[15:0]};
                instr_compress_o = 1'b1;
            end
      end

      ALIGNED16:
      begin
            if(r_instr[1:0] == 2'b11) begin
                /*
                  Before we fetched a 16bit aligned instruction
                  So now the beginning of the next instruction is the stored one
                  The istruction is 32bits so it is misaligned
                */
                NS               = MISALIGNED32;
                pc_n             = pc_q+4;
                instr_o          = {mem_content_i[15:0],r_instr[15:0]};
                instr_compress_o = 1'b0;
            end else begin
                /*
                  Before we fetched a 16bit aligned instruction
                  So now the beginning of the next instruction is the stored one
                  The istruction is 16bits so it is misaligned
                */
                instr_o          = {16'b0,r_instr[15:0]};
                NS               = MISALIGNED16;
                pc_n             = pc_q+2;
                instr_compress_o = 1'b1;
                //we cannot overwrite the 32bit instruction just fetched
                //so tell the IF stage to stall, the coming instruction goes to the FIFO
                raw_instr_hold_o = fetch_valid_i;
            end
      end

      MISALIGNED32:
      begin
            if(r_instr[1:0] == 2'b11) begin
                /*
                  Before we fetched a 32bit misaligned instruction
                  So now the beginning of the next instruction is the stored one
                  The istruction is 32bits so it is misaligned again
                */
                NS               = MISALIGNED32;
                pc_n             = pc_q+4;
                instr_o          = {mem_content_i[15:0],r_instr[15:0]};
                instr_compress_o = 1'b0;
            end else begin
                /*
                  Before we fetched a 32bit misaligned instruction
                  So now the beginning of the next instruction is the stored one
                  The istruction is 16bits misaligned
                */
                instr_o          = {16'b0,r_instr[15:0]};
                NS               = MISALIGNED16;
                pc_n             = pc_q+2;
                instr_compress_o = 1'b1;
                //we cannot overwrite the 32bit instruction just fetched
                //so tell the IF stage to stall, the coming instruction goes to the FIFO
                raw_instr_hold_o = fetch_valid_i;
            end
      end

      MISALIGNED16:
      begin
            //this is 1 as we holded the value before with raw_instr_hold_o
            instr_valid_o    = 1'b1;
            if(mem_content_i[1:0] == 2'b11) begin
                /*
                  Before we fetched a 16bit misaligned instruction
                  So now the beginning of the next instruction is the new one
                  The istruction is 32bits so it is aligned
                */
                NS               = ALIGNED32;
                pc_n             = pc_q+4;
                instr_o          = mem_content_i;
                instr_compress_o = 1'b0;
            end else begin
                /*
                  Before we fetched a 16bit misaligned  instruction
                  So now the beginning of the next instruction is the new one
                  The istruction is 16bit aligned
                */
                NS               = ALIGNED16;
                pc_n             = pc_q+2;
                instr_o          = {16'b0,mem_content_i[15:0]};
                instr_compress_o = 1'b1;
            end
      end

      BRANCH_MISALIGNED:
      begin
            //this is 1 as we holded the value before with raw_instr_hold_o
            if(mem_content_i[17:16] == 2'b11) begin
                /*
                  We jumped to a misaligned location that contains 32bits instruction
                */
                NS               = MISALIGNED32;
                instr_valid_o    = 1'b0;
                pc_n             = pc_q;
                instr_o          = mem_content_i;
                instr_compress_o = 1'b0;
            end else begin
                /*
                  We jumped to a misaligned location that contains 16bits instruction
                */
                NS               = ALIGNED32;
                pc_n             = pc_q+2;
                instr_o          = {16'b0,mem_content_i[15:0]};
                instr_compress_o = 1'b1;
            end
      end
    endcase // CS

    if(branch_i) begin
      pc_n  = branch_addr_i;
      NS    = branch_addr_i[1] ? BRANCH_MISALIGNED : ALIGNED32;
    end

  end

endmodule