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
  input  logic [31:0] hwloop_target_reg_i,

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

  localparam FIFO_DEPTH                     = 2; //must be greater or equal to 2
  localparam int unsigned FIFO_ADDR_DEPTH   = $clog2(FIFO_DEPTH);
  localparam int unsigned FIFO_ALM_FULL_TH  = FIFO_DEPTH-1;    // almost full threshold (when to assert alm_full_o)

  enum logic [2:0] {IDLE, WAIT_GNT, WAIT_RVALID, WAIT_ABORTED, WAIT_JUMP, WAIT_GNT_HWLOOP, WAIT_RVALID_HWLOOP, WAIT_ABORTED_HWLOOP} CS, NS;


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
  logic [31:0] r_hwloop_target;


  //////////////////////////////////////////////////////////////////////////////
  // prefetch buffer status
  //////////////////////////////////////////////////////////////////////////////

  assign busy_o = (CS != IDLE) || instr_req_o;

  //////////////////////////////////////////////////////////////////////////////
  // fetch addr
  //////////////////////////////////////////////////////////////////////////////

  assign fetch_addr    = {instr_addr_q[31:2], 2'b00} + 32'd4;

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
        instr_addr_o = fetch_addr;
        instr_req_o  = 1'b0;

          if (branch_i)
            instr_addr_o = addr_i;

          if (req_i & (fifo_ready | branch_i | hwlp_branch_i)) begin
              instr_req_o = 1'b1;
              addr_valid = 1'b1;

              if(hwlp_branch_i) begin

              /*
              We received the hwlp_branch_i and there are different possibilities

              1) the last instruction of the HWLoop is in the FIFO
              In this case the FIFO is empty, and we won't abort the coming data
              We first POP the last instruction of the HWLoop and the we abort the coming instruction
              Note that the abord is done by the fifo_flush signal as if the FIFO is not empty, i.e.
              fifo_valid is 1, we would store the coming data into the FIFO.
              Flush and Push will be active at the same time, but FLUSH has higher priority

              2) The FIFO is empty, so we did not ask yet for the last instruction of the HWLoop
              So first ask for it and then fetch the HWLoop
              */

              save_hwloop_target = 1'b1;

              if(fifo_valid) begin
                fifo_flush = 1'b1;
                instr_addr_o = hwloop_target_i;
              end
          end

          if(instr_gnt_i) //~> granted request
              if(hwlp_branch_i)
                  NS = WAIT_RVALID_HWLOOP; // We are not waiting any response (no pending) so there is nothing to KILL
              else
                  NS = WAIT_RVALID;
          else begin //~> got a request but no grant

              if(hwlp_branch_i)
                NS = WAIT_GNT_HWLOOP;
              else
                NS = WAIT_GNT;
          end

          if(instr_err_pmp_i)
          NS = WAIT_JUMP;

          end
      end // case: IDLE


      WAIT_ABORTED_HWLOOP: begin
        instr_addr_o = r_hwloop_target;

        if (branch_i) begin
          instr_addr_o = addr_i;
          addr_valid   = 1'b1;
        end

        if (instr_rvalid_i) begin
          instr_req_o  = 1'b1;
          addr_valid   = 1'b1;
          // no need to send address, already done in WAIT_RVALID

          if (instr_gnt_i) begin
            NS = WAIT_RVALID;
          end else begin
            NS = WAIT_GNT;
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


      // we sent a request but did not yet get a grant
      WAIT_GNT:
      begin
        instr_addr_o = instr_addr_q;
        instr_req_o  = 1'b1;

        if (branch_i) begin
          instr_addr_o = addr_i;
          addr_valid   = 1'b1;
        end
        if(instr_gnt_i) begin
          NS = WAIT_RVALID;
          if(hwlp_branch_i & ~branch_i) begin
            NS                 = WAIT_RVALID_HWLOOP;
            save_hwloop_target = 1'b1;
          end
        end else begin
          NS = WAIT_GNT;
          if(hwlp_branch_i & ~branch_i) begin
            NS                 = WAIT_GNT_HWLOOP;
            save_hwloop_target = 1'b1;
          end
        end
      end // case: WAIT_GNT

      // we sent a request but did not yet get a grant
      WAIT_GNT_HWLOOP:
      begin
        instr_addr_o = instr_addr_q;
        instr_req_o  = 1'b1;

        if (branch_i) begin
          instr_addr_o = addr_i;
          addr_valid   = 1'b1;
        end
        if(instr_gnt_i) begin
          NS = WAIT_RVALID;
          if(~branch_i) begin
            NS = WAIT_RVALID_HWLOOP;
          end
        end else begin
          NS = WAIT_GNT;
          if(~branch_i) begin
            NS = WAIT_GNT_HWLOOP;
          end
        end
      end // case: WAIT_GNT_HWLOOP

      // we wait for rvalid, after that we are ready to serve a new request
      WAIT_RVALID: begin
        instr_addr_o = fetch_addr;

        if (branch_i)
          instr_addr_o = addr_i;

        if (req_i & (fifo_ready | branch_i | hwlp_branch_i)) begin
          // prepare for next request

          if (instr_rvalid_i) begin
            instr_req_o = 1'b1;
            fifo_push   = fifo_valid | ~ready_i;
            addr_valid  = 1'b1;

            if(hwlp_branch_i) begin
              instr_addr_o = hwloop_target_i;

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
              if(fifo_valid) fifo_flush = 1'b1;

            end

            if (instr_gnt_i) begin
              NS = WAIT_RVALID;
            end else begin
              NS = WAIT_GNT;
            end
            if(instr_err_pmp_i)
              NS = WAIT_JUMP;

          end else begin
            // we are requested to abort our current request
            // we didn't get an rvalid yet, so wait for it
            if (branch_i) begin
              addr_valid = 1'b1;
              NS         = WAIT_ABORTED;
            end else if(hwlp_branch_i) begin

              /*
                We are waiting for the rvalid and there are different possibilities

                1) We are waiting for the RVALID of the last instruction of the HWLoop
                   In this case the FIFO is empty, we need to wait the RVALID before jumping
                   and emit the instruction to the ID stage

                2) We are waiting for the RVALID of an instruction after the end of the HWLoop
                   In this case the FIFO is not empty:

                   We first POP the last instruction of the HWLoop and the we abort the coming instruction
                   simply by flushing as written in the comment above
              */
              if(fifo_valid) fifo_flush = 1'b1; //TODO: probably just if (fifo_valid) as ready_i should be 1

              NS = fifo_valid ? WAIT_ABORTED_HWLOOP : WAIT_RVALID_HWLOOP;
              addr_valid         = 1'b1;
              save_hwloop_target = 1'b1;
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



      WAIT_RVALID_HWLOOP:
      begin
         if(instr_rvalid_i)
         begin
           instr_req_o  = 1'b1;
           fifo_push    = 1'b0;
           addr_valid   = 1'b1;
           instr_addr_o = r_hwloop_target;

          /*
            We received the rvalid and there are different possibilities

            1) the RVALID is the last instruction of the HWLoop
               In this case the FIFO is empty, and we won't abort the coming data

            2) the RVALID is of an instruction after the end of the HWLoop
               In this case the FIFO is not empty

               We first POP the last instruction of the HWLoop and the we abort the coming instruction
               simply by flushing as written in the comment above
          */

           if(fifo_valid)
            fifo_flush   = 1'b1;

           if(instr_gnt_i)
             NS = WAIT_RVALID;
           else
             NS = WAIT_GNT;

         end
      end //~ WAIT_RVALID_HWLOOP


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
    end
    else
    begin
      CS              <= NS;

      if (addr_valid) begin
        instr_addr_q    <= instr_addr_o;
      end

      if(save_hwloop_target)
        r_hwloop_target = hwloop_target_i;
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
        valid_o  = instr_rvalid_i & (CS != WAIT_ABORTED) & ( CS != WAIT_ABORTED_HWLOOP);
        rdata_o  = instr_rdata_i  & {32{instr_rvalid_i}};
      end
   end

endmodule
