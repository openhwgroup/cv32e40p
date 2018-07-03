`define RULE_0  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_xxxxxxx0
`define RULE_1  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_xxxxxx01
`define RULE_2  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_xxxxx011
`define RULE_3  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_xxxx0111
`define RULE_4  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_xxx01111
`define RULE_5  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_xx011111
`define RULE_6  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_x0111111
`define RULE_7  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_01111111
`define RULE_8  32'bxxxxxxxx_xxxxxxxx_xxxxxxx0_11111111
`define RULE_9  32'bxxxxxxxx_xxxxxxxx_xxxxxx01_11111111
`define RULE_10 32'bxxxxxxxx_xxxxxxxx_xxxxx011_11111111
`define RULE_11 32'bxxxxxxxx_xxxxxxxx_xxxx0111_11111111
`define RULE_12 32'bxxxxxxxx_xxxxxxxx_xxx01111_11111111
`define RULE_13 32'bxxxxxxxx_xxxxxxxx_xx011111_11111111
`define RULE_14 32'bxxxxxxxx_xxxxxxxx_x0111111_11111111
`define RULE_15 32'bxxxxxxxx_xxxxxxxx_01111111_11111111
`define RULE_16 32'bxxxxxxxx_xxxxxxx0_11111111_11111111
`define RULE_17 32'bxxxxxxxx_xxxxxx01_11111111_11111111
`define RULE_18 32'bxxxxxxxx_xxxxx011_11111111_11111111
`define RULE_19 32'bxxxxxxxx_xxxx0111_11111111_11111111
`define RULE_20 32'bxxxxxxxx_xxx01111_11111111_11111111
`define RULE_21 32'bxxxxxxxx_xx011111_11111111_11111111
`define RULE_22 32'bxxxxxxxx_x0111111_11111111_11111111
`define RULE_23 32'bxxxxxxxx_01111111_11111111_11111111
`define RULE_24 32'bxxxxxxx0_11111111_11111111_11111111
`define RULE_25 32'bxxxxxx01_11111111_11111111_11111111
`define RULE_26 32'bxxxxx011_11111111_11111111_11111111
`define RULE_27 32'bxxxx0111_11111111_11111111_11111111
`define RULE_28 32'bxxx01111_11111111_11111111_11111111
`define RULE_29 32'bxx011111_11111111_11111111_11111111
`define RULE_30 32'bx0111111_11111111_11111111_11111111
`define RULE_31 32'b01111111_11111111_11111111_11111111


`define ENABLE_NAPOT


`define EN_NAPOT_RULE_8B       /* 0  */
`define EN_NAPOT_RULE_16B      /* 1  */
`define EN_NAPOT_RULE_32B      /* 2  */
`define EN_NAPOT_RULE_64B      /* 3  */
`define EN_NAPOT_RULE_128B     /* 4  */
`define EN_NAPOT_RULE_256B     /* 5  */
`define EN_NAPOT_RULE_512B     /* 6  */
`define EN_NAPOT_RULE_1KB      /* 7  */
`define EN_NAPOT_RULE_2KB      /* 8  */
`define EN_NAPOT_RULE_4KB      /* 9  */
`define EN_NAPOT_RULE_8KB      /* 10 */
`define EN_NAPOT_RULE_16KB     /* 11 */
`define EN_NAPOT_RULE_32KB     /* 12 */
`define EN_NAPOT_RULE_64KB     /* 13 */
`define EN_NAPOT_RULE_128KB    /* 14 */
`define EN_NAPOT_RULE_256KB    /* 15 */
`define EN_NAPOT_RULE_512KB    /* 16 */
`define EN_NAPOT_RULE_1MB      /* 17 */
`define EN_NAPOT_RULE_2MB      /* 18 */
`define EN_NAPOT_RULE_4MB      /* 19 */
`define EN_NAPOT_RULE_8MB      /* 20 */
`define EN_NAPOT_RULE_16MB     /* 21 */
`define EN_NAPOT_RULE_32MB     /* 22 */
`define EN_NAPOT_RULE_64MB     /* 23 */
`define EN_NAPOT_RULE_128MB    /* 24 */
`define EN_NAPOT_RULE_256MB    /* 25 */
`define EN_NAPOT_RULE_512MB    /* 26 */
`define EN_NAPOT_RULE_1GB      /* 27 */
`define EN_NAPOT_RULE_2GB      /* 28 */
`define EN_NAPOT_RULE_4GB      /* 29 */
`define EN_NAPOT_RULE_8GB      /* 30 */
`define EN_NAPOT_RULE_16GB     /* 31 */

`define DEBUG_RULE

module decoder_MPU_RV32
#(
   parameter N_PMP_ENTRIES = 16
)
(
   input logic                             clk,
   input logic                             rst_n,

   input logic                             pmp_privil_mode_i,  // 0 --> User, 1-->Machine

   input logic  [N_PMP_ENTRIES-1:0] [31:0] pmp_addr_i,
   input logic  [N_PMP_ENTRIES-1:0] [7:0]  pmp_cfg_i,


   // data side : if TO pipeline
   input  logic                            data_req_i,
   input  logic [31:0]                     data_addr_i,
   input  logic                            data_we_i,
   output logic                            data_gnt_o,
   // if to Memory
   output logic                            data_req_o,
   input  logic                            data_gnt_i,
   output logic [31:0]                     data_addr_o,
   output logic                            data_err_o,


   // fetch side : if TO pipeline
   input  logic                            instr_req_i,
   input  logic [31:0]                     instr_addr_i,
   output logic                            instr_gnt_o,
   // fetch to PF buffer
   output logic                            instr_req_o,
   input  logic                            instr_gnt_i,
   output logic [31:0]                     instr_addr_o,
   output logic                            instr_err_o
);


   logic [N_PMP_ENTRIES-1:0]      EN_rule;
   logic [N_PMP_ENTRIES-1:0]      R_rule;
   logic [N_PMP_ENTRIES-1:0]      W_rule;
   logic [N_PMP_ENTRIES-1:0]      X_rule;
   logic [N_PMP_ENTRIES-1:0][1:0] MODE_rule;
   logic [N_PMP_ENTRIES-1:0][1:0] WIRI_rule;
   logic [N_PMP_ENTRIES-1:0][1:0] LOCK_rule;

   logic [N_PMP_ENTRIES-1:0][31:0] start_addr;
   logic [N_PMP_ENTRIES-1:0][31:0] stop_addr;
   logic [N_PMP_ENTRIES-1:0]       data_match_region;
   logic [N_PMP_ENTRIES-1:0]       instr_match_region;

   genvar i;
   int unsigned j,k;


   ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // ██████╗ ██╗   ██╗██╗     ███████╗    ███████╗██╗  ██╗██████╗  █████╗ ███╗   ██╗███████╗██╗ ██████╗ ███╗   ██╗ //
   // ██╔══██╗██║   ██║██║     ██╔════╝    ██╔════╝╚██╗██╔╝██╔══██╗██╔══██╗████╗  ██║██╔════╝██║██╔═══██╗████╗  ██║ //
   // ██████╔╝██║   ██║██║     █████╗      █████╗   ╚███╔╝ ██████╔╝███████║██╔██╗ ██║███████╗██║██║   ██║██╔██╗ ██║ //
   // ██╔══██╗██║   ██║██║     ██╔══╝      ██╔══╝   ██╔██╗ ██╔═══╝ ██╔══██║██║╚██╗██║╚════██║██║██║   ██║██║╚██╗██║ //
   // ██║  ██║╚██████╔╝███████╗███████╗    ███████╗██╔╝ ██╗██║     ██║  ██║██║ ╚████║███████║██║╚██████╔╝██║ ╚████║ //
   // ╚═╝  ╚═╝ ╚═════╝ ╚══════╝╚══════╝    ╚══════╝╚═╝  ╚═╝╚═╝     ╚═╝  ╚═╝╚═╝  ╚═══╝╚══════╝╚═╝ ╚═════╝ ╚═╝  ╚═══╝ //
   ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   generate
      for(i=0;i<N_PMP_ENTRIES;i++)
      begin : CFG_EXP
         assign {LOCK_rule[i],WIRI_rule[i],MODE_rule[i],X_rule[i], W_rule[i], R_rule[i] } = pmp_cfg_i[i];
      end

      // address Expansion
      
      for(i=0;i<N_PMP_ENTRIES;i++)
      begin : ADDR_EXP
         always @(*)
         begin
            start_addr[i] = '0;
            stop_addr[i]  = '0;

            case (MODE_rule[i])
               2'b00:
               begin : DISABLED
                  EN_rule[i] = 1'b0;
                  `ifdef DEBUG_RULE $display(" DISABLED[%d]", i ); `endif
               end

               2'b01: 
               begin : TOR_MODE
                  EN_rule[i] = 1'b1;
                  if(i==0)
                  begin
                     start_addr[i] = 0;
                  end
                  else
                  begin
                     start_addr[i] = pmp_addr_i[i-1];
                  end

                  stop_addr[i] = pmp_addr_i[i];
                  `ifdef DEBUG_RULE $display(" TOR[%d]: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
               end

               2'b10:
               begin : NA4_MODE
                  EN_rule[i] = 1'b1;
                  stop_addr[i]  = pmp_addr_i[i];
                  start_addr[i] = pmp_addr_i[i];
                  `ifdef DEBUG_RULE $display(" NA4[%d]  %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
               end

`ifdef ENABLE_NAPOT
               2'b11:
               begin : NAPOT_MODE
                  EN_rule[i] = 1'b1;

                  casex(pmp_addr_i[i])

      `ifdef EN_NAPOT_RULE_8B
                     `RULE_0:
                     begin: BYTE_ALIGN_8B
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_FFFE;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_8B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_16B
                     `RULE_1:
                     begin: BYTE_ALIGN_16B
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_FFFC;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_16B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_32B
                     `RULE_2:
                     begin: BYTE_ALIGN_32B
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_FFF8;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_32B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_64B                     
                     `RULE_3:
                     begin: BYTE_ALIGN_64B
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_FFF0;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_64B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif



      `ifdef EN_NAPOT_RULE_128B
                     `RULE_4:
                     begin: BYTE_ALIGN_128B
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_FFE0;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_128B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_256B                     
                     `RULE_5:
                     begin: BYTE_ALIGN_256B
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_FFC0;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_256B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_512B                     
                     `RULE_6:
                     begin: BYTE_ALIGN_512B
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_FF80;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_512B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_1KB                     
                     `RULE_7:
                     begin: BYTE_ALIGN_1KB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_FF00;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_1KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif



      `ifdef EN_NAPOT_RULE_2KB
                     `RULE_8:
                     begin: BYTE_ALIGN_2KB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_FE00;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_2K: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_4KB                     
                     `RULE_9:
                     begin: BYTE_ALIGN_4KB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_FC00;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_4KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_8KB                     
                     `RULE_10:
                     begin: BYTE_ALIGN_8KB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_F800;
                        stop_addr[i]  = pmp_addr_i[i];
                     `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_8KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_16KB                     
                     `RULE_11:
                     begin: BYTE_ALIGN_16KB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_F000;
                        stop_addr[i]  = pmp_addr_i[i];
                     `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_16KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif



      `ifdef EN_NAPOT_RULE_32KB
                     `RULE_12:
                     begin: BYTE_ALIGN_32KB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_E000;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_32KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_64KBB                     
                     `RULE_13:
                     begin: BYTE_ALIGN_64KB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_C000;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_64KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_128KB                     
                     `RULE_14:
                     begin: BYTE_ALIGN_128KB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_8000;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_128KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_256KB                     
                     `RULE_15:
                     begin: BYTE_ALIGN_256KB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_256KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif



      `ifdef EN_NAPOT_RULE_512KB
                     `RULE_16:
                     begin: BYTE_ALIGN_512KB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFE_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_512KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_1MB                     
                     `RULE_17:
                     begin: BYTE_ALIGN_1MB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFC_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_1MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_2MB                        
                     `RULE_18:
                     begin: BYTE_ALIGN_2MB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFF8_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_2MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_4MB                        
                     `RULE_19:
                     begin: BYTE_ALIGN_4MB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFF0_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_4MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif


      `ifdef EN_NAPOT_RULE_8MB   
                     `RULE_20:
                     begin: BYTE_ALIGN_8MB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFE0_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_8MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_16MB
                     `RULE_21:
                     begin: BYTE_ALIGN_16MB
                        start_addr[i] = pmp_addr_i[i] & 32'hFFC0_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_16MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_32MB                        
                     `RULE_22:
                     begin: BYTE_ALIGN_32MB
                        start_addr[i] = pmp_addr_i[i] & 32'hFF80_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_32MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_64MB                        
                     `RULE_23:
                     begin: BYTE_ALIGN_64MB
                        start_addr[i] = pmp_addr_i[i] & 32'hFF00_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_64MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif



      `ifdef EN_NAPOT_RULE_128MB   
                     `RULE_24:
                     begin: BYTE_ALIGN_128MB
                        start_addr[i] = pmp_addr_i[i] & 32'hFE00_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif
      `ifdef EN_NAPOT_RULE_256MB                        
                     `RULE_25:
                     begin: BYTE_ALIGN_256MB
                        start_addr[i] = pmp_addr_i[i] & 32'hFC00_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif
      `ifdef EN_NAPOT_RULE_512MB                        
                     `RULE_26:
                     begin: BYTE_ALIGN_512MB
                        start_addr[i] = pmp_addr_i[i] & 32'hF800_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif
      `ifdef EN_NAPOT_RULE_1GB                        
                     `RULE_27:
                     begin: BYTE_ALIGN_1GB
                        start_addr[i] = pmp_addr_i[i] & 32'hF000_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif



      `ifdef EN_NAPOT_RULE_2GB   
                     `RULE_28:
                     begin: BYTE_ALIGN_2GB
                        start_addr[i] = pmp_addr_i[i] & 32'hE000_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif

      `ifdef EN_NAPOT_RULE_4GB
                     `RULE_29:
                     begin: BYTE_ALIGN_4GB
                        start_addr[i] = pmp_addr_i[i] & 32'hC000_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif

      `ifdef EN_NAPOT_RULE_8GB
                     `RULE_30:
                     begin: BYTE_ALIGN_8GB
                        start_addr[i] = pmp_addr_i[i] & 32'h8000_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif

      `ifdef EN_NAPOT_RULE_16MB
                     `RULE_31:
                     begin: BYTE_ALIGN_16GB
                        start_addr[i] = pmp_addr_i[i] & 32'h0000_0000;
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif
                     default:
                     begin: INVALID_RULE
                        EN_rule[i]    = 1'b0;
                        start_addr[i] = '0;
                        stop_addr[i]  = '0;
                     end

                  endcase
               end
`endif
            default:
            begin: DEFAULT_DISABLED
               EN_rule[i]    = 1'b0;
               start_addr[i] = '0;
               stop_addr[i]  = '0;
            end

            endcase
         end
      end
   endgenerate


   ///////////////////////////////////////////////////////////////////////////////////////////////
   // ██████╗ ██╗   ██╗██╗     ███████╗         ██████╗██╗  ██╗███████╗ ██████╗██╗  ██╗███████╗ //
   // ██╔══██╗██║   ██║██║     ██╔════╝        ██╔════╝██║  ██║██╔════╝██╔════╝██║ ██╔╝██╔════╝ //
   // ██████╔╝██║   ██║██║     █████╗          ██║     ███████║█████╗  ██║     █████╔╝ ███████╗ //
   // ██╔══██╗██║   ██║██║     ██╔══╝          ██║     ██╔══██║██╔══╝  ██║     ██╔═██╗ ╚════██║ //
   // ██║  ██║╚██████╔╝███████╗███████╗███████╗╚██████╗██║  ██║███████╗╚██████╗██║  ██╗███████║ //
   // ╚═╝  ╚═╝ ╚═════╝ ╚══════╝╚══════╝╚══════╝ ╚═════╝╚═╝  ╚═╝╚══════╝ ╚═════╝╚═╝  ╚═╝╚══════╝ //
   ///////////////////////////////////////////////////////////////////////////////////////////////




   always_comb
   begin
      for(j=0;j<N_PMP_ENTRIES;j++)
      begin

         if( EN_rule[j] & ((~data_we_i & R_rule[j]) | (data_we_i & W_rule[j])) )
         begin
             if ( ( data_addr_i[31:2] >= start_addr[j])  &&  ( data_addr_i[31:2] <= stop_addr[j])  )
             begin
                data_match_region[j] = 1'b1;
                `ifdef DEBUG_RULE
                  $display("HIT on RULE %d: [%8h] <= data_addr_i [%8h] <= [%8h], RULE=%2h, X=%b, W=%b, R=%d", j, (start_addr[j])>>2 , data_addr_i , (stop_addr[j])>>2, pmp_cfg_i[j][4:3], X_rule[j], W_rule[j], R_rule[j]);
                `endif                
             end
             else 
             begin
                data_match_region[j] = 1'b0;
             end
         end
         else
         begin
               data_match_region[j] = 1'b0;
         end

      end
   end

   assign data_addr_o  = data_addr_i;
   
   always_comb 
   begin
      if(pmp_privil_mode_i)
      begin
         data_req_o   = data_req_i;
         data_gnt_o   = data_gnt_i;
         data_err_o   = 1'b0;

      end
      else
      begin
            if(|data_match_region == 1'b0)
            begin
               data_req_o   = 1'b0;
               data_err_o   = data_req_i; 
               data_gnt_o   = 1'b0; 
            end
            else
            begin
               data_req_o   =  data_req_i;
               data_err_o   =  1'b0;
               data_gnt_o   =  data_gnt_i;
            end
      end
   end






   always_comb
   begin
      for(k=0;k<N_PMP_ENTRIES;k++)
      begin

         if(EN_rule[k] & X_rule[k])
         begin
             if ( ( instr_addr_i[31:2] >= start_addr[k])  &&  ( instr_addr_i[31:2] <= stop_addr[k])  )
             begin
                instr_match_region[k] = 1'b1;
             end
             else 
             begin
                instr_match_region[k] = 1'b0;
             end
         end
         else
         begin
            instr_match_region[k] = 1'b0;
         end
         

      end
   end

   assign instr_addr_o  = instr_addr_i;
   
   always_comb 
   begin
      if(pmp_privil_mode_i)
      begin
         instr_req_o   = instr_req_i;
         instr_gnt_o   = instr_gnt_i;
         instr_err_o   = 1'b0;

      end
      else
      begin
            if(|instr_match_region == 1'b0)
            begin
               instr_req_o   = 1'b0;
               instr_err_o   = instr_req_i; 
               instr_gnt_o   = 1'b0; 
            end
            else
            begin
               instr_req_o   =  instr_req_i;
               instr_err_o   =  1'b0;
               instr_gnt_o   =  instr_gnt_i;
            end
      end
   end


endmodule
