/// Description: Governs atomic memory oeprations. This module needs to be instantiated
/// in front of an SRAM. It needs to have exclusive access over it.

/// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
module amo_shim #(
    parameter  int unsigned AddrMemWidth = 32
) (
    input   logic                     clk_i,
    input   logic                     rst_ni,
    // master side
    input   logic                     in_req_i,     // Bank request
    output  logic                     in_gnt_o,     // Bank grant
    input   logic [AddrMemWidth-1:0]  in_add_i,     // Address
    input   logic [3:0]               in_amo_i,     // Atomic Memory Operation
    input   logic                     in_wen_i,     // 1: Store, 0: Load
    input   logic [63:0]              in_wdata_i,   // Write data
    input   logic [7:0]               in_be_i,      // Byte enable
    output  logic [63:0]              in_rdata_o,   // Read data
    // slave side
    output  logic                     out_req_o,    // Bank request
    output  logic [AddrMemWidth-1:0]  out_add_o,    // Address
    output  logic                     out_wen_o,    // 1: Store, 0: Load
    output  logic [63:0]              out_wdata_o,  // Write data
    output  logic [7:0]               out_be_o,     // Byte enable
    input   logic [63:0]              out_rdata_i   // Read data
);

    typedef enum logic [3:0] {
        AMONone = 4'h0,
        AMOSwap = 4'h1,
        AMOAdd  = 4'h2,
        AMOAnd  = 4'h3,
        AMOOr   = 4'h4,
        AMOXor  = 4'h5,
        AMOMax  = 4'h6,
        AMOMaxu = 4'h7,
        AMOMin  = 4'h8,
        AMOMinu = 4'h9,
        AMOCAS  = 4'hA,
        AMOLr   = 4'hB, // TODO: works only for single core right now
        AMOSc   = 4'hC
    } amo_op_t;

    enum logic {
        Idle, DoAMO
    } state_q;

    amo_op_t     amo_op_q;

    logic        load_amo;

    logic [AddrMemWidth-1:0] addr_q;

    logic [31:0] amo_operand_a;
    logic [31:0] amo_operand_b_q;
    // requested amo should be performed on upper 32 bit
    logic        upper_word_q;
    logic [31:0] swap_value_q;
    logic [31:0] amo_result; // result of atomic memory operation

    logic [AddrMemWidth-1:0] reserv_q, reserv_d; // lrsc reservation
    logic                    reserv_valid_q, reserv_valid_d;
    logic                    sc_ok;

    assign amo_operand_a = upper_word_q ? out_rdata_i[63:32] : out_rdata_i[31:0];

    assign sc_ok = reserv_valid_q && (reserv_q == addr_q);

    always_comb begin
        // feed-through
        out_req_o   = in_req_i;
        in_gnt_o    = in_req_i;
        out_add_o   = in_add_i;
        out_wen_o   = in_wen_i;
        out_wdata_o = in_wdata_i;
        out_be_o    = in_be_i;
        in_rdata_o  = out_rdata_i;

        load_amo = 1'b0;
        reserv_d = reserv_q;
        reserv_valid_d = reserv_valid_q;

        unique case (state_q)
            Idle: begin
                if (in_req_i && amo_op_t'(in_amo_i) == AMOLr) begin
                    // reserve address
                    // load_amo = 1'b1; // we don't need to go to this state, it's like a regular read
                    // out_wen_o = 1'b0; // we already read
                    reserv_d = in_add_i;
                    reserv_valid_d = 1'b1;

                end else if (in_req_i && amo_op_t'(in_amo_i) != AMONone) begin
                    load_amo = 1'b1;
                    out_wen_o = 1'b0; // TODO: we have to force this, since
                                      // RI5CY keeps wen high during atomics
                end
            end

            // Claim the memory interface
            DoAMO: begin
                in_gnt_o    = 1'b0;
                // Commit AMO
                if (amo_op_q != AMOLr) begin
                    out_req_o   = 1'b1;
                    out_add_o   = addr_q;
                    out_wen_o   = 1'b1;
                    // shift up if the address was pointing to the upper 32 bits
                    out_be_o    = upper_word_q ?  8'b1111_0000 : 8'b0000_1111;
                    out_wdata_o = upper_word_q ? {amo_result, 32'b0} : {32'b0, amo_result};
                end

                if (amo_op_q == AMOSc) begin // AMOSc needs to signal success/failure through rdata
                    in_rdata_o = upper_word_q ? {{31{1'b0}}, ~sc_ok, 32'b0} : {{63{1'b0}}, ~sc_ok};
                    reserv_valid_d = 1'b0;
                end else begin
                    in_rdata_o = upper_word_q ? {amo_operand_a, 32'b0} : {32'b0, amo_operand_a};
                end

            end
            default:;
        endcase
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            state_q         <= Idle;
            amo_op_q        <= amo_op_t'('0);
            addr_q          <= '0;
            amo_operand_b_q <= '0;
            swap_value_q    <= '0;
            upper_word_q    <= '0;
            reserv_q        <= '0;
            reserv_valid_q  <= '0;
        end else begin
            reserv_q       <= reserv_d;
            reserv_valid_q <= reserv_valid_d;

            if (load_amo) begin
                amo_op_q        <= amo_op_t'(in_amo_i);
                addr_q          <= in_add_i;
                amo_operand_b_q <= in_be_i[0] ? in_wdata_i[31:0]  : in_wdata_i[63:32];
                // swap value is located in the upper word
                swap_value_q    <= in_be_i[0] ? in_wdata_i[63:32] : in_wdata_i[63:32];
                state_q         <= DoAMO;
                upper_word_q    <= in_be_i[4];
            end else begin
                amo_op_q        <= AMONone;
                state_q         <= Idle;
            end
        end
    end

    // ----------------
    // AMO ALU
    // ----------------
    logic [33:0] adder_sum;
    logic [32:0] adder_operand_a, adder_operand_b;

    assign adder_sum = adder_operand_a + adder_operand_b;
    /* verilator lint_off WIDTH */
    always_comb begin : amo_alu

        adder_operand_a = 33'($signed(amo_operand_a));
        adder_operand_b = 33'($signed(amo_operand_b_q));

        amo_result = amo_operand_b_q; // will be written, wdata

        unique case (amo_op_q)
            // the default is to output operand_b
            AMOSwap:;
            AMOLr:;
            AMOAdd: amo_result = adder_sum[31:0];
            AMOAnd: amo_result = amo_operand_a & amo_operand_b_q;
            AMOOr:  amo_result = amo_operand_a | amo_operand_b_q;
            AMOXor: amo_result = amo_operand_a ^ amo_operand_b_q;
            AMOMax: begin
                adder_operand_b = -$signed(amo_operand_b_q);
                amo_result = adder_sum[32] ? amo_operand_b_q : amo_operand_a;
            end
            AMOMin: begin
                adder_operand_b = -$signed(amo_operand_b_q);
                amo_result = adder_sum[32] ? amo_operand_a : amo_operand_b_q;
            end
            AMOMaxu: begin
                adder_operand_a = 33'($unsigned(amo_operand_a));
                adder_operand_b = -$unsigned(amo_operand_b_q);
                amo_result = adder_sum[32] ? amo_operand_b_q : amo_operand_a;
            end
            AMOMinu: begin
                adder_operand_a = 33'($unsigned(amo_operand_a));
                adder_operand_b = -$unsigned(amo_operand_b_q);
                amo_result = adder_sum[32] ? amo_operand_a : amo_operand_b_q;
            end
            AMOCAS: begin
                adder_operand_b = -$signed(amo_operand_b_q);
                // values are equal -> update
                if (adder_sum == '0) begin
                    amo_result =  swap_value_q;
                // values are not equal -> don't update
                end else begin
                    amo_result =  upper_word_q ? out_rdata_i[63:32] : out_rdata_i[31:0];
                end
            end
            AMOSc: begin
                if (sc_ok) begin
                    amo_result = amo_operand_b_q; // update
                end else begin
                    amo_result = upper_word_q ? out_rdata_i[63:32] : out_rdata_i[31:0]; // keep
                end
            end
            default: amo_result = '0;
        endcase
    end
    /* verilator lint_on WIDTH */
endmodule
