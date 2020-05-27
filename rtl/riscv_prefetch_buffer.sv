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
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Prefetcher Buffer for 32 bit memory interface              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Prefetch Buffer that caches instructions. This cuts overly //
//                 long critical paths to the instruction cache               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// input port: send address one cycle before the data
// clear_i clears the FIFO for the following cycle. in_addr_i can be sent in
// this cycle already

module riscv_prefetch_buffer
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        req_i,

  input  logic        branch_i,
  input  logic [31:0] addr_i,

  input  logic        hwlp_branch_i,
  input  logic [31:0] hwloop_target_i,

  input  logic        ready_i,
  output logic        valid_o,
  output logic [31:0] rdata_o,

  // goes to instruction memory / instruction cache
  output logic        instr_req_o,
  input  logic        instr_gnt_i,
  output logic [31:0] instr_addr_o,
  input  logic [31:0] instr_rdata_i,
  input  logic        instr_rvalid_i,
  input  logic        instr_err_pmp_i,
  output logic        fetch_failed_o,

  // Prefetch Buffer Status
  output logic        busy_o
);

  localparam FIFO_DEPTH                     = 2; //must be greater or equal to 2 //Set at least to 3 to avoid stalls compared to the master branch
  localparam int unsigned FIFO_ADDR_DEPTH   = $clog2(FIFO_DEPTH);
  localparam int unsigned FIFO_ALM_FULL_TH  = FIFO_DEPTH-1;    // almost full threshold (when to assert alm_full_o)

  enum logic [3:0] {IDLE, WAIT_GNT_LAST_HWLOOP, WAIT_RVALID_LAST_HWLOOP, WAIT_GNT, WAIT_RVALID, WAIT_ABORTED, WAIT_JUMP, JUMP_HWLOOP, WAIT_VALID_ABORTED_HWLOOP, WAIT_POP_ABORTED_HWLOOP, WAIT_POP_FLUSH} CS, NS;

  logic [FIFO_ADDR_DEPTH-1:0] fifo_usage;

  logic [31:0] instr_addr_q, fetch_addr;
  logic        fetch_is_hwlp;
  logic        addr_valid;

  logic        fifo_valid;
  logic        fifo_ready;
  logic        fifo_flush;

  logic        out_fifo_empty, alm_full;

  logic [31:0] fifo_rdata;
  logic        fifo_push;
  logic        fifo_pop;

  logic        save_hwloop_target;
  // When HWLP_END-4 stalls in the ID stage, hwlp_branch_i remains asserted. This signal tells the prefetcher
  // if we have already jumped to HWLP_BEGIN
  logic        hwlp_already_jumped;

  //////////////////////////////////////////////////////////////////////////////
  // prefetch buffer status
  //////////////////////////////////////////////////////////////////////////////

  assign busy_o = (CS != IDLE) || instr_req_o;

  //////////////////////////////////////////////////////////////////////////////
  // fetch addr
  //////////////////////////////////////////////////////////////////////////////

  assign fetch_addr    = {instr_addr_q[31:2], 2'b00} + 32'd4;

  //////////////////////////////////////////////////////////////////////////////
  // hwlp_branch mask
  // To deal with D-MEM stalls when HWLP_END-4 is stuck in the ID stage
  // The prefetcher reacts immediately to hwlp_branch_i, so mask it after one clock
  //////////////////////////////////////////////////////////////////////////////

  assign hwlp_branch_masked = (hwlp_branch_i && !hwlp_already_jumped);

  //////////////////////////////////////////////////////////////////////////////
  // instruction fetch FSM
  // deals with instruction memory / instruction cache
  //////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    instr_req_o    = 1'b0;
    instr_addr_o   = fetch_addr;
    addr_valid     = 1'b0;
    fetch_is_hwlp  = 1'b0;
    fetch_failed_o = 1'b0;
    fifo_push      = 1'b0;
    NS             = CS;
    fifo_flush     = 1'b0;

    save_hwloop_target = 1'b0;

    unique case(CS)
      // default state, not waiting for requested data
      IDLE:
      begin

          instr_req_o  = 1'b0;
          instr_addr_o = fetch_addr;

          if (branch_i) begin
            instr_addr_o = addr_i;
          end else if (hwlp_branch_masked && fifo_valid) begin
            // We are hwlp-branching and HWLP_END is in the FIFO: we can request HWLP_BEGIN
            instr_addr_o = hwloop_target_i;
          end

          if (req_i & (fifo_ready | branch_i | hwlp_branch_masked)) begin
              instr_req_o = 1'b1;
              addr_valid = 1'b1;

              /*
              If we received the hwlp_branch_i and there are different possibilities

              1) the last instruction of the HWLoop is in the FIFO
              In this case the FIFO is not empty
              We first POP the last instruction of the HWLoop and then we abort the coming instruction
              Note that the abort is done by the fifo_flush signal as if the FIFO is not empty, i.e.
              fifo_valid is 1, we would store the coming data into the FIFO.
              Flush and Push will be active at the same time, but FLUSH has higher priority

              2) The FIFO is empty, so we did not ask yet for the last instruction of the HWLoop
              So first ask for it and then fetch the HWLoop
              */


              if(instr_gnt_i) begin
                if(!hwlp_branch_masked) NS= WAIT_RVALID; //branch_i || !hwlp_branch_i should always be true
                else begin
                  if(!fifo_valid) begin
                    //FIFO is empty, ask for PC_END
                    NS = WAIT_RVALID_LAST_HWLOOP;
                  end else begin
                    //FIFO is not empty, wait for POP then jump to PC_BEGIN
                    //last instruction consumed, so wait for the current instruction and then JUMP
                    if (fifo_pop) begin
                      //FIFO is popping HWLP_END now, flush the FIFO and wait for the VALID of HWLP_BEGIN
                      //Flush now because if we do not flush and move to WAIT_RVALID_JUMP_HWLOOP
                      //we will pop PC_END+4 in the next state
                      fifo_flush = 1'b1;
                      NS=WAIT_RVALID;
                    end else begin
                      //FIFO contains HWLP_END and is not popping now, so wait for the POP and flush before jumping
                      NS= WAIT_POP_FLUSH;
                    end
                  end
                end
              end else begin //~> got a request but no grant
                if(!hwlp_branch_masked) NS= WAIT_GNT; //branch_i || !hwlp_branch_i should always be true
                else begin
                  if(!fifo_valid) begin
                    //FIFO is empty, ask for PC_END
                    NS = WAIT_GNT_LAST_HWLOOP;
                  end else begin
                    //FIFO contains HWLP_END
                    if (fifo_pop) begin
                      //If HWLP_end is being popped, flush the FIFO and keep the hwlp-request alive until GNT
                      fifo_flush = 1'b1;
                      NS = JUMP_HWLOOP;
                    end else begin
                      // Wait for the POP, then JUMP to HWLP_BEGIN
                      NS= WAIT_POP_FLUSH;
                    end
                  end
                end
              end

              if(instr_err_pmp_i)
              NS = WAIT_JUMP;

          end
      end // case: IDLE

      WAIT_JUMP:
      begin

        instr_req_o  = 1'b0;

        fetch_failed_o = valid_o == 1'b0;

        if (branch_i) begin
          instr_addr_o = addr_i;
          addr_valid   = 1'b1;
          instr_req_o  = 1'b1;
          fetch_failed_o = 1'b0;

          if(instr_gnt_i)
            NS = WAIT_RVALID;
          else
            NS = WAIT_GNT;
        end
      end

      WAIT_GNT_LAST_HWLOOP:
      begin
        // We are waiting for the GRANT of HWLP_END
        instr_addr_o = instr_addr_q;
        instr_req_o  = 1'b1;

        if (branch_i) begin
          instr_addr_o = addr_i;
          addr_valid   = 1'b1;
        end

        if(instr_gnt_i) begin
           NS = branch_i ? WAIT_RVALID : WAIT_RVALID_LAST_HWLOOP;
        end

      end


      WAIT_RVALID_LAST_HWLOOP: begin
        // We are waiting for the VALID of HWLP_END
        instr_addr_o = hwloop_target_i;

        if (branch_i)
          instr_addr_o = addr_i;

        if (req_i & (fifo_ready | branch_i)) begin
          // prepare for next request

          if (instr_rvalid_i) begin
            // RVALID of HWLP_END. Jump to HWLP_BEGIN
            instr_req_o = 1'b1;
            fifo_push   = ~ready_i;
            addr_valid  = 1'b1;

            if (instr_gnt_i) begin
              NS = WAIT_RVALID;
            end else begin
              NS = WAIT_GNT;
            end
            if(instr_err_pmp_i)
              NS = WAIT_JUMP;
          end

        end else begin
          // just wait for rvalid and go back to IDLE, no new request

          if (instr_rvalid_i) begin
            fifo_push   = fifo_valid | ~ready_i;
            NS          = IDLE;
          end
        end
      end // case: WAIT_RVALID

      // we sent a request but did not yet get a grant
      WAIT_GNT:
      begin
        instr_req_o  = 1'b1;

        if (branch_i) begin
          addr_valid = 1'b1;
          instr_addr_o = addr_i;
        end else if (hwlp_branch_masked && fifo_valid) begin
          addr_valid = 1'b1;
          instr_addr_o = hwloop_target_i;
        end else begin
          instr_addr_o = instr_addr_q;
        end

        if(instr_gnt_i) begin

          NS = WAIT_RVALID;

          if(hwlp_branch_masked) begin

            //We are waiting a GRANT, we do not know if this grant is for the last instruction of the HWLoop or even after
            //If the FIFO is empty, then we are waiting for PC_END of HWLOOP, otherwise we are just waiting for another instruction after the PC_END
            //so we have to wait for a POP and then FLUSH the FIFO and jump to the target
            if(fifo_valid) begin
              //the fifo is not empty, so the first element is PC_END
              if (fifo_pop) begin
                //FIFO is popping HWLP_END now, flush the FIFO and wait for the VALID of HWLP_BEGIN
                //Flush now because if we do not flush and move to WAIT_RVALID_JUMP_HWLOOP
                //we will pop PC_END+4 in the next state
                fifo_flush = 1'b1;
                NS               = WAIT_RVALID;
              end else begin
                NS               = WAIT_POP_FLUSH;
              end
            end else begin
              //the fifo is empty, so we are receiving the grant of PC_END. Go to wait for PC_END valid
              NS                 = WAIT_RVALID_LAST_HWLOOP;
            end
          end

        end else begin
          if(hwlp_branch_masked) begin

            //We are waiting a GRANT, we do not know if this grant is for the last instruction of the HWLoop or even after
            //If the FIFO is empty, then we are waiting for PC_END of HWLOOP, otherwise we are just waiting for another instruction after the PC_END
            //so we will wait for a POP and then FLUSH the FIFO and jump to the target
            if(fifo_valid) begin
              //FIFO contains HWLP_END
              if (fifo_pop) begin
                //If HWLP_end is being popped, flush the FIFO and keep the hwlp-request alive until GNT
                fifo_flush = 1'b1;
                NS               = JUMP_HWLOOP;
              end else begin
                // Wait for the POP, then flush and JUMP to HWLP_BEGIN
                NS               = WAIT_POP_FLUSH;
              end
            end else begin
              //the fifo is empty, so we are waiting for the PC_END grant
              NS                 = WAIT_GNT_LAST_HWLOOP;
            end
          end
        end
      end // case: WAIT_GNT

      // we wait for rvalid, after that we are ready to serve a new request
      WAIT_RVALID: begin

        if (branch_i) begin
          instr_addr_o = addr_i;
        end else if (hwlp_branch_masked) begin
          instr_addr_o = hwloop_target_i;
        end else begin
          instr_addr_o = fetch_addr;
        end

        if (req_i & (fifo_ready | branch_i | hwlp_branch_masked)) begin
          // prepare for next request

          if (instr_rvalid_i) begin
            instr_req_o = 1'b1;
            fifo_push   = fifo_valid | ~ready_i;
            addr_valid  = 1'b1;

            if(hwlp_branch_masked) begin
              /*
                We received the rvalid and there are different possibilities

                1) the RVALID is the last instruction of the HWLoop
                   In this case the FIFO is empty, and we won't abort the coming data

                2) the RVALID is of an instruction after the end of the HWLoop
                   In this case the FIFO is not empty

                   We first POP the last instruction of the HWLoop and the we abort the coming instruction
                   Note that the abord is done by the fifo_flush signal as if the FIFO is not empty, i.e.
                   fifo_valid is 1, we would store the coming data into the FIFO.
                   Flush and Push will be active at the same time, but FLUSH has higher priority
              */
              if(fifo_valid) begin
                //the FIFO is not empty, so if we pop, we pop the PC_END. so next VALID should flush all away
                //We are also requesting HWLP_BEGIN in this cycle
                if (fifo_pop) begin
                  // We are popping HWLP_END, we can flush the FIFO and the incoming data, which is trash
                  fifo_flush = 1'b1;
                  if (instr_gnt_i) begin
                    // This is the grant of our HWLP_begin
                    NS = WAIT_RVALID;
                  end else begin
                    // Keep on requesting HWLP_begin until grant
                    NS = JUMP_HWLOOP;
                  end
                end else begin
                  // Wait for the pop, then flush, then request HWLP_begin
                  NS= WAIT_POP_FLUSH;
                end
              end else begin
                //The fifo is empty and we are saving the target address
                if (instr_gnt_i) begin
                  NS = WAIT_RVALID;
                end else begin
                  NS = JUMP_HWLOOP; // Since we are saving the target address, it's ok also WAIT_GNT
                end
              end


            end
            else begin
              if (instr_gnt_i) begin
                NS = WAIT_RVALID;
              end else begin
                NS = WAIT_GNT;
              end
              if(instr_err_pmp_i)
                NS = WAIT_JUMP;
            end
          end else begin
            // we are still waiting for rvalid
            // check if we should abort the previous request
            if (branch_i) begin
              addr_valid  = 1'b1;
              NS = WAIT_ABORTED;
            end else if (hwlp_branch_masked) begin
              addr_valid  = 1'b1;
              /*
                We cannot have received any grant here.
                Will the next RVALID be associated to HWLP_END?
                1) Empty FIFO: yes
                2) Non-empty FIFO: no
                Anyway, our request (HWLP_BEGIN) should be postponed.
              */
              if(fifo_valid) begin
                //the FIFO is not empty
                if (fifo_pop) begin
                  // The next cycle FIFO will contain nothing or trash
                  NS = WAIT_VALID_ABORTED_HWLOOP;
                end else begin
                  // The FIFO contains HWLP_END and possibly trash
                  NS = WAIT_POP_ABORTED_HWLOOP;
                end
              end else begin
                //The fifo is empty and the next RVALID will be with HWLP_END
                  NS = WAIT_RVALID_LAST_HWLOOP;
              end
            end
          end
        end else begin
          // just wait for rvalid and go back to IDLE, no new request

          if (instr_rvalid_i) begin
            fifo_push   = fifo_valid | ~ready_i;
            NS          = IDLE;
          end
        end
      end // case: WAIT_RVALID

      WAIT_VALID_ABORTED_HWLOOP:
      begin
        // We are waiting a sterile RVALID to jump to HWLP_BEGIN
        instr_req_o  = 1'b1;
        instr_addr_o = hwloop_target_i;
        NS = instr_gnt_i ? WAIT_RVALID : WAIT_VALID_ABORTED_HWLOOP;
      end

      WAIT_POP_ABORTED_HWLOOP:
      begin
        // We are waiting a sterile RVALID to jump to HWLP_BEGIN,
        // and we should flush when HWLP_END is consumed
        fifo_flush = fifo_pop;
        if (fifo_pop && instr_rvalid_i) begin
          NS = JUMP_HWLOOP;
        end else if (!fifo_pop && instr_rvalid_i) begin
          NS = WAIT_POP_FLUSH;
        end else if (fifo_pop && !instr_rvalid_i) begin
          NS = WAIT_VALID_ABORTED_HWLOOP;
        end
      end

      WAIT_POP_FLUSH:
      begin
        // Wait for the FIFO to POP HWLP_END, then flush and JUMP
        instr_addr_o = hwloop_target_i;
        fifo_flush   = fifo_pop;
        NS           = fifo_pop ? JUMP_HWLOOP : WAIT_POP_FLUSH;
      end

      JUMP_HWLOOP:
      begin
          instr_req_o  = 1'b1;
          instr_addr_o = hwloop_target_i;
          addr_valid   = 1'b1;

          if (instr_gnt_i) begin
              NS = WAIT_RVALID;
            end else begin
              NS = WAIT_GNT;
          end
      end //~ JUMP_HWLOOP

      // our last request was aborted, but we didn't yet get a rvalid and
      // there was no new request sent yet
      // we assume that req_i is set to high
      WAIT_ABORTED: begin
        instr_addr_o = instr_addr_q;

        if (branch_i) begin
          instr_addr_o = addr_i;
          addr_valid   = 1'b1;
        end

        if (instr_rvalid_i) begin
          instr_req_o  = 1'b1;
          // no need to send address, already done in WAIT_RVALID

          if (instr_gnt_i) begin
            NS = WAIT_RVALID;
          end else begin
            NS = WAIT_GNT;
          end
          if(instr_err_pmp_i)
            NS = WAIT_JUMP;
        end
      end

      default:
      begin
        NS          = IDLE;
        instr_req_o = 1'b0;
      end
    endcase
  end

  //////////////////////////////////////////////////////////////////////////////
  // registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      CS              <= IDLE;
      instr_addr_q    <= '0;
      hwlp_already_jumped   <= 1'b0;
    end
    else
    begin
      CS              <= NS;
      hwlp_already_jumped <= hwlp_branch_i;
      if (hwlp_branch_masked & branch_i) $display("NO BRANCH AND hwlp_branch_i 1 at the same time %t",$time);
      if (addr_valid) begin
        instr_addr_q    <= instr_addr_o;
      end
    end
  end

  assign alm_full = (fifo_usage >= FIFO_ALM_FULL_TH[FIFO_ADDR_DEPTH-1:0]);

  riscv_fifo
  #(
      .FALL_THROUGH ( 1'b0                 ),
      .DATA_WIDTH   ( 32                   ),
      .DEPTH        ( FIFO_DEPTH           )
  )
  instr_buffer_i
  (
      .clk_i       ( clk                   ),
      .rst_ni      ( rst_n                 ),
      .flush_i     ( branch_i | fifo_flush ),
      .testmode_i  ( 1'b0                  ),

      .full_o      ( fifo_full             ),
      .empty_o     ( out_fifo_empty        ),
      .usage_o     ( fifo_usage            ),
      .data_i      ( instr_rdata_i         ),
      .push_i      ( fifo_push             ),
      .data_o      ( fifo_rdata            ),
      .pop_i       ( fifo_pop              )
  );

   assign fifo_valid = ~out_fifo_empty;
   assign fifo_ready = ~(alm_full | fifo_full);

   always_comb
   begin
      fifo_pop = 1'b0;
      valid_o  = 1'b0;
      rdata_o  = instr_rdata_i & {32{instr_rvalid_i}};
      if(fifo_valid) begin
        rdata_o  = fifo_rdata;
        fifo_pop = ready_i;
        valid_o  = 1'b1;
      end else begin
        valid_o  = instr_rvalid_i & (CS != WAIT_ABORTED) & (CS != WAIT_VALID_ABORTED_HWLOOP); // Todo: check this, maybe add some other states
        rdata_o  = instr_rdata_i  & {32{instr_rvalid_i}};
      end
   end

endmodule

/*
  The FSM was modified to be more responsive when executing an HW loop.
  When hwlp_branch_i is high, the FSM tries to perform the jump immediately if it can.
  Therefore, the address is combinatorially set to hwloop_target_i in the same cycle.
  In this way, after hwlp_branch_i was high we always wait for HWLP_BEGIN.
  On the contrary, it is possible to delay this choice to another state.
*/