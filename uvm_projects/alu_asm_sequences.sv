// Copyright 2024 ChipAgents
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// Assembly-Driven UVM Sequences for CV32E40P ALU Verification               //
//                                                                            //
// Description: UVM sequences that read assembly programs and execute them   //
//              on the ALU for systematic instruction-level testing          //
////////////////////////////////////////////////////////////////////////////////

`include "uvm_macros.svh"

import uvm_pkg::*;
import cv32e40p_pkg::*;
import cv32e40p_alu_pkg::*;

////////////////////////////////////////////////////////////////////////////////
// Assembly Instruction Parser and Executor
////////////////////////////////////////////////////////////////////////////////

typedef struct {
    string opcode;
    string operands[$];
    string description;
    cv32e40p_pkg::alu_opcode_e alu_op;
    logic [31:0] operand_a;
    logic [31:0] operand_b;
    logic [31:0] operand_c;
} asm_instruction_t;

class asm_parser;
    
    // Register file simulation (for operand resolution)
    logic [31:0] registers[32];
    
    // Instruction to ALU operation mapping
    static cv32e40p_pkg::alu_opcode_e opcode_map[string] = '{
        "add":   ALU_ADD,
        "addi":  ALU_ADD,
        "sub":   ALU_SUB,
        "subi":  ALU_SUB,
        "and":   ALU_AND,
        "andi":  ALU_AND,
        "or":    ALU_OR,
        "ori":   ALU_OR,
        "xor":   ALU_XOR,
        "xori":  ALU_XOR,
        "sll":   ALU_SLL,
        "slli":  ALU_SLL,
        "srl":   ALU_SRL,
        "srli":  ALU_SRL,
        "sra":   ALU_SRA,
        "srai":  ALU_SRA,
        "slt":   ALU_LTS,
        "slti":  ALU_LTS,
        "sltu":  ALU_LTU,
        "sltiu": ALU_LTU,
        "lui":   ALU_ADD,
        "auipc": ALU_ADD
    };
    
    function new();
        // Initialize register file (x0 = 0, others random)
        registers[0] = 32'h0;
        for (int i = 1; i < 32; i++) begin
            registers[i] = $urandom();
        end
    endfunction
    
    function int parse_register(string reg_str);
        // Parse register name (x0-x31)
        if (reg_str.substr(0, 0) == "x") begin
            string num_str = reg_str.substr(1, reg_str.len()-1);
            return num_str.atoi();
        end
        return 0; // Default to x0
    endfunction
    
    function logic [31:0] parse_immediate(string imm_str);
        // Parse immediate value (decimal or hex)
        if (imm_str.substr(0, 1) == "0x") begin
            // Hexadecimal
            return imm_str.substr(2, imm_str.len()-1).atohex();
        end else begin
            // Decimal (signed)
            return imm_str.atoi();
        end
    endfunction
    
    function asm_instruction_t parse_instruction(string asm_line);
        asm_instruction_t inst;
        string tokens[$];
        string operand_str;
        int comma_pos, comment_pos, space_pos;
        
        // Remove comments
        comment_pos = asm_line.search("//");
        if (comment_pos >= 0) begin
            inst.description = asm_line.substr(comment_pos+2, asm_line.len()-1);
            asm_line = asm_line.substr(0, comment_pos-1);
        end
        
        // Extract opcode (first token) - simplified parsing
        space_pos = asm_line.search(" ");
        if (space_pos >= 0) begin
            inst.opcode = asm_line.substr(0, space_pos-1);
            operand_str = asm_line.substr(space_pos+1, asm_line.len()-1);
            
            // Parse operands (comma-separated) - simplified
            comma_pos = operand_str.search(",");
            if (comma_pos >= 0) begin
                inst.operands.push_back(operand_str.substr(0, comma_pos-1));
                inst.operands.push_back(operand_str.substr(comma_pos+1, operand_str.len()-1));
            end else begin
                inst.operands.push_back(operand_str);
            end
        end else begin
            inst.opcode = asm_line;
        end
        
        // Map to ALU operation
        if (opcode_map.exists(inst.opcode)) begin
            inst.alu_op = opcode_map[inst.opcode];
        end else begin
            inst.alu_op = ALU_ADD; // Default
        end
        
        // Resolve operands
        if (inst.operands.size() >= 2) begin
            int rs1, rs2;
            // Source operand A
            rs1 = parse_register(inst.operands[1]);
            inst.operand_a = registers[rs1];
            
            if (inst.operands.size() >= 3) begin
                // Source operand B (register or immediate)
                if (inst.opcode.substr(inst.opcode.len()-1, inst.opcode.len()-1) == "i" || 
                    inst.opcode == "lui" || inst.opcode == "auipc") begin
                    // Immediate instruction
                    inst.operand_b = parse_immediate(inst.operands[2]);
                end else begin
                    // Register instruction
                    rs2 = parse_register(inst.operands[2]);
                    inst.operand_b = registers[rs2];
                end
            end
        end
        
        return inst;
    endfunction
    
    function void update_register(string reg_str, logic [31:0] value);
        int reg_num = parse_register(reg_str);
        if (reg_num != 0) begin // x0 is always 0
            registers[reg_num] = value;
        end
    endfunction
    
endclass

////////////////////////////////////////////////////////////////////////////////
// Assembly-Driven Sequence
////////////////////////////////////////////////////////////////////////////////

class alu_assembly_sequence extends uvm_sequence #(alu_sequence_item);
    `uvm_object_utils(alu_assembly_sequence)
    
    string assembly_file;
    asm_parser parser;
    asm_instruction_t instructions[$];
    
    function new(string name = "alu_assembly_sequence");
        super.new(name);
        assembly_file = "alu_targeted_coverage.s";
        parser = new();
    endfunction
    
    function void set_assembly_file(string filename);
        assembly_file = filename;
    endfunction
    
    function bit load_assembly_program();
        int file_handle;
        string line;
        asm_instruction_t inst;
        
        file_handle = $fopen(assembly_file, "r");
        if (file_handle == 0) begin
            `uvm_error("ASM_SEQ", $sformatf("Cannot open assembly file: %s", assembly_file))
            return 0;
        end
        
        `uvm_info("ASM_SEQ", $sformatf("Loading assembly program: %s", assembly_file), UVM_MEDIUM)
        
        while (!$feof(file_handle)) begin
            $fgets(line, file_handle);
            
            // Skip empty lines, comments, and directives
            if (line.len() == 0 || line.getc(0) == "#" || 
                line.getc(0) == "." || line.getc(line.len()-1) == ":") begin
                continue;
            end
            
            // Skip system calls and non-ALU instructions
            if (line.search("ecall") >= 0) begin
                continue;
            end
            
            inst = parser.parse_instruction(line);
            if (inst.opcode != "") begin
                instructions.push_back(inst);
            end
        end
        
        $fclose(file_handle);
        `uvm_info("ASM_SEQ", $sformatf("Loaded %0d instructions", instructions.size()), UVM_MEDIUM)
        return 1;
    endfunction
    
    virtual task body();
        alu_sequence_item req;
        asm_instruction_t inst;
        
        if (!load_assembly_program()) begin
            `uvm_error("ASM_SEQ", "Failed to load assembly program")
            return;
        end
        
        `uvm_info("ASM_SEQ", "Starting assembly program execution", UVM_MEDIUM)
        
        foreach (instructions[i]) begin
            inst = instructions[i];
            
            req = alu_sequence_item::type_id::create("req");
            start_item(req);
            
            // Configure ALU transaction based on assembly instruction
            req.operator = inst.alu_op;
            req.operand_a = inst.operand_a;
            req.operand_b = inst.operand_b;
            req.operand_c = inst.operand_c;
            req.enable = 1'b1;
            req.vector_mode = VEC_MODE32;
            req.ex_ready = 1'b1;
            
            // Set other fields to reasonable defaults
            req.bmask_a = 5'h0;
            req.bmask_b = 5'h0;
            req.imm_vec_ext = 2'b00;
            req.is_clpx = 1'b0;
            req.is_subrot = 1'b0;
            req.clpx_shift = 2'b00;
            
            finish_item(req);
            
            `uvm_info("ASM_SEQ", $sformatf("Executed: %s %s (ALU_OP=%s, A=0x%08x, B=0x%08x)", 
                     inst.opcode, inst.description, inst.alu_op.name(), 
                     inst.operand_a, inst.operand_b), UVM_HIGH)
            
            // Update destination register with result (for dependent instructions)
            if (inst.operands.size() >= 1) begin
                parser.update_register(inst.operands[0], req.result);
            end
        end
        
        `uvm_info("ASM_SEQ", "Assembly program execution completed", UVM_MEDIUM)
    endtask
    
endclass

////////////////////////////////////////////////////////////////////////////////
// Weighted Random Assembly Sequence
////////////////////////////////////////////////////////////////////////////////

class alu_weighted_random_sequence extends uvm_sequence #(alu_sequence_item);
    `uvm_object_utils(alu_weighted_random_sequence)
    
    // Instruction distribution weights (matching assembly generator)
    int arithmetic_weight = 40;
    int logic_weight = 25;
    int shift_weight = 15;
    int comparison_weight = 10;
    int other_weight = 10;
    
    rand int num_instructions;
    
    constraint num_inst_c {
        num_instructions inside {[50:300]};
    }
    
    function new(string name = "alu_weighted_random_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        alu_sequence_item req;
        int total_weight;
        int rand_val;
        cv32e40p_pkg::alu_opcode_e selected_op;
        
        total_weight = arithmetic_weight + logic_weight + shift_weight + comparison_weight + other_weight;
        
        `uvm_info("WEIGHTED_SEQ", $sformatf("Starting weighted random sequence with %0d instructions", num_instructions), UVM_MEDIUM)
        
        repeat(num_instructions) begin
            req = alu_sequence_item::type_id::create("req");
            start_item(req);
            
            // Select operation based on weights
            rand_val = $urandom_range(0, total_weight-1);
            
            if (rand_val < arithmetic_weight) begin
                // Arithmetic operations
                selected_op = cv32e40p_pkg::alu_opcode_e'($urandom_range(int'(ALU_ADD), int'(ALU_SUB)));
            end else if (rand_val < arithmetic_weight + logic_weight) begin
                // Logic operations  
                selected_op = cv32e40p_pkg::alu_opcode_e'($urandom_range(int'(ALU_AND), int'(ALU_XOR)));
            end else if (rand_val < arithmetic_weight + logic_weight + shift_weight) begin
                // Shift operations
                selected_op = cv32e40p_pkg::alu_opcode_e'($urandom_range(int'(ALU_SLL), int'(ALU_SRA)));
            end else if (rand_val < arithmetic_weight + logic_weight + shift_weight + comparison_weight) begin
                // Comparison operations
                if ($urandom_range(0, 1)) begin
                    selected_op = ALU_LTS;
                end else begin
                    selected_op = ALU_LTU;
                end
            end else begin
                // Other operations (use ADD as default)
                selected_op = ALU_ADD;
            end
            
            if (!req.randomize() with {
                operator == selected_op;
                enable == 1'b1;
                ex_ready == 1'b1;
                vector_mode == VEC_MODE32;
            }) begin
                `uvm_error("WEIGHTED_SEQ", "Randomization failed")
            end
            
            finish_item(req);
        end
        
        `uvm_info("WEIGHTED_SEQ", "Weighted random sequence completed", UVM_MEDIUM)
    endtask
    
endclass

////////////////////////////////////////////////////////////////////////////////
// Combined Assembly and Random Test
////////////////////////////////////////////////////////////////////////////////

// Assembly-driven sequences are defined above and can be used in test classes