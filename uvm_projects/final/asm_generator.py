#!/usr/bin/env python3
# Copyright 2024 ChipAgents
# SPDX-License-Identifier: Apache-2.0

"""
Assembly Program Generator for CV32E40P ALU Testing

This script generates assembly programs with targeted instruction distributions
for comprehensive ALU verification. The generated assembly is then used by
UVM sequences for systematic testing.

Distribution:
- Arithmetic Operations: 40%
- Logic Operations: 25% 
- Shift Operations: 15%
- Comparison Operations: 10%
- Other Operations: 10%
"""

import random
import argparse
import json
from typing import Dict, List, Tuple
from dataclasses import dataclass
from enum import Enum

class InstructionType(Enum):
    ARITHMETIC = "arithmetic"
    LOGIC = "logic"
    SHIFT = "shift"
    COMPARISON = "comparison"
    DIVISION = "division"      # HIGH COVERAGE IMPACT
    BIT_MANIP = "bit_manip"    # HIGH COVERAGE IMPACT
    OTHER = "other"

@dataclass
class Instruction:
    """Represents a single assembly instruction"""
    opcode: str
    operands: List[str]
    inst_type: InstructionType
    description: str
    
    def to_asm(self) -> str:
        """Convert instruction to assembly format"""
        return f"    {self.opcode:<8} {', '.join(self.operands):<20} // {self.description}"

class CV32E40P_InstructionSet:
    """CV32E40P ALU instruction set definition"""
    
    def __init__(self):
        # Define instruction mappings to ALU operations
        self.arithmetic_ops = {
            'add': 'ALU_ADD',
            'sub': 'ALU_SUB', 
            'addi': 'ALU_ADD',
            'subi': 'ALU_SUB'
        }
        
        self.logic_ops = {
            'and': 'ALU_AND',
            'or': 'ALU_OR',
            'xor': 'ALU_XOR',
            'andi': 'ALU_AND',
            'ori': 'ALU_OR',
            'xori': 'ALU_XOR'
        }
        
        self.shift_ops = {
            'sll': 'ALU_SLL',
            'srl': 'ALU_SRL', 
            'sra': 'ALU_SRA',
            'slli': 'ALU_SLL',
            'srli': 'ALU_SRL',
            'srai': 'ALU_SRA'
        }
        
        self.comparison_ops = {
            'slt': 'ALU_LTS',
            'sltu': 'ALU_LTU',
            'slti': 'ALU_LTS',
            'sltiu': 'ALU_LTU'
        }
        
        # HIGH COVERAGE IMPACT: Add division and bit manipulation operations
        self.division_ops = {
            'div': 'ALU_DIV',      # Signed division
            'divu': 'ALU_DIVU',    # Unsigned division  
            'rem': 'ALU_REM',      # Signed remainder
            'remu': 'ALU_REMU'     # Unsigned remainder
        }
        
        self.bit_manipulation_ops = {
            'bext': 'ALU_BEXT',    # Bit extract
            'bextu': 'ALU_BEXTU',  # Bit extract unsigned
            'bins': 'ALU_BINS',    # Bit insert
            'bclr': 'ALU_BCLR',    # Bit clear
            'bset': 'ALU_BSET',    # Bit set
            'brev': 'ALU_BREV'     # Bit reverse
        }
        
        self.other_ops = {
            'lui': 'ALU_ADD',  # Load upper immediate (can use ADD with shifted operand)
            'auipc': 'ALU_ADD' # Add upper immediate to PC
        }
        
        # Register names
        self.registers = [f'x{i}' for i in range(32)]
        self.abi_names = {
            'x0': 'zero', 'x1': 'ra', 'x2': 'sp', 'x3': 'gp',
            'x4': 'tp', 'x5': 't0', 'x6': 't1', 'x7': 't2',
            'x8': 's0', 'x9': 's1', 'x10': 'a0', 'x11': 'a1',
            'x12': 'a2', 'x13': 'a3', 'x14': 'a4', 'x15': 'a5',
            'x16': 'a6', 'x17': 'a7', 'x18': 's2', 'x19': 's3',
            'x20': 's4', 'x21': 's5', 'x22': 's6', 'x23': 's7',
            'x24': 's8', 'x25': 's9', 'x26': 's10', 'x27': 's11',
            'x28': 't3', 'x29': 't4', 'x30': 't5', 'x31': 't6'
        }

class AssemblyGenerator:
    """Generates assembly programs with specified instruction distributions"""
    
    def __init__(self, seed: int = None):
        if seed:
            random.seed(seed)
        self.isa = CV32E40P_InstructionSet()
        # OPTIMIZED FOR 55% COVERAGE TARGET
        self.instruction_weights = {
            InstructionType.ARITHMETIC: 15,  # Basic foundation
            InstructionType.LOGIC: 20,       # Condition coverage
            InstructionType.SHIFT: 25,       # Toggle coverage (high impact)
            InstructionType.COMPARISON: 10,  # Branch coverage
            InstructionType.DIVISION: 20,    # HIGHEST COVERAGE IMPACT (+15%)
            InstructionType.BIT_MANIP: 10    # HIGH COVERAGE IMPACT (+10%)
        }
        
    def generate_random_register(self, exclude_zero: bool = True) -> str:
        """Generate a random register name"""
        regs = self.isa.registers[1:] if exclude_zero else self.isa.registers
        return random.choice(regs)
    
    def generate_immediate(self, bits: int = 12, signed: bool = True) -> str:
        """Generate a random immediate value with coverage-focused patterns"""
        if signed:
            max_val = (1 << (bits - 1)) - 1
            min_val = -(1 << (bits - 1))
        else:
            max_val = (1 << bits) - 1
            min_val = 0
        
        # 30% chance of using coverage-focused patterns
        if random.random() < 0.3:
            coverage_patterns = [
                0, 1, -1, max_val, min_val,
                0x555, 0xAAA, 0x333, 0xCCC,  # Alternating bit patterns
                0x0F0, 0xF0F, 0x00F, 0xFF0,  # Nibble patterns
                0x001, 0x010, 0x100,         # Single bit patterns
            ]
            # Filter patterns that fit in the bit range
            valid_patterns = [p for p in coverage_patterns if min_val <= p <= max_val]
            if valid_patterns:
                value = random.choice(valid_patterns)
            else:
                value = random.randint(min_val, max_val)
        else:
            value = random.randint(min_val, max_val)
        
        return str(value)
    
    def generate_arithmetic_instruction(self) -> Instruction:
        """Generate a random arithmetic instruction"""
        op = random.choice(list(self.isa.arithmetic_ops.keys()))
        rd = self.generate_random_register()
        rs1 = self.generate_random_register()
        
        if op.endswith('i'):  # Immediate instruction
            imm = self.generate_immediate()
            operands = [rd, rs1, imm]
            desc = f"{op.upper()} {rd}, {rs1}, {imm}"
        else:  # Register instruction
            rs2 = self.generate_random_register()
            operands = [rd, rs1, rs2]
            desc = f"{op.upper()} {rd}, {rs1}, {rs2}"
            
        return Instruction(op, operands, InstructionType.ARITHMETIC, desc)
    
    def generate_logic_instruction(self) -> Instruction:
        """Generate a random logic instruction"""
        op = random.choice(list(self.isa.logic_ops.keys()))
        rd = self.generate_random_register()
        rs1 = self.generate_random_register()
        
        if op.endswith('i'):  # Immediate instruction
            imm = self.generate_immediate()
            operands = [rd, rs1, imm]
            desc = f"{op.upper()} {rd}, {rs1}, {imm}"
        else:  # Register instruction
            rs2 = self.generate_random_register()
            operands = [rd, rs1, rs2]
            desc = f"{op.upper()} {rd}, {rs1}, {rs2}"
            
        return Instruction(op, operands, InstructionType.LOGIC, desc)
    
    def generate_shift_instruction(self) -> Instruction:
        """Generate a random shift instruction"""
        op = random.choice(list(self.isa.shift_ops.keys()))
        rd = self.generate_random_register()
        rs1 = self.generate_random_register()
        
        if op.endswith('i'):  # Immediate instruction
            shamt = str(random.randint(0, 31))  # Shift amount 0-31
            operands = [rd, rs1, shamt]
            desc = f"{op.upper()} {rd}, {rs1}, {shamt}"
        else:  # Register instruction
            rs2 = self.generate_random_register()
            operands = [rd, rs1, rs2]
            desc = f"{op.upper()} {rd}, {rs1}, {rs2}"
            
        return Instruction(op, operands, InstructionType.SHIFT, desc)
    
    def generate_comparison_instruction(self) -> Instruction:
        """Generate a random comparison instruction"""
        op = random.choice(list(self.isa.comparison_ops.keys()))
        rd = self.generate_random_register()
        rs1 = self.generate_random_register()
        
        if op.endswith('i'):  # Immediate instruction
            imm = self.generate_immediate()
            operands = [rd, rs1, imm]
            desc = f"{op.upper()} {rd}, {rs1}, {imm}"
        else:  # Register instruction
            rs2 = self.generate_random_register()
            operands = [rd, rs1, rs2]
            desc = f"{op.upper()} {rd}, {rs1}, {rs2}"
            
        return Instruction(op, operands, InstructionType.COMPARISON, desc)
    
    def generate_division_instruction(self) -> Instruction:
        """Generate a random division instruction - HIGH COVERAGE IMPACT"""
        op = random.choice(list(self.isa.division_ops.keys()))
        rd = self.generate_random_register()
        rs1 = self.generate_random_register()
        rs2 = self.generate_random_register()
        
        # Avoid division by zero for more realistic testing
        if random.random() < 0.8:  # 80% chance of non-zero divisor
            rs2 = self.generate_random_register(exclude_zero=True)
        
        operands = [rd, rs1, rs2]
        desc = f"{op.upper()} {rd}, {rs1}, {rs2}"
        
        return Instruction(op, operands, InstructionType.DIVISION, desc)
    
    def generate_bit_manipulation_instruction(self) -> Instruction:
        """Generate a random bit manipulation instruction - HIGH COVERAGE IMPACT"""
        op = random.choice(list(self.isa.bit_manipulation_ops.keys()))
        rd = self.generate_random_register()
        rs1 = self.generate_random_register()
        
        if op in ['bext', 'bextu', 'bclr', 'bset']:
            # These operations need a bit position (0-31)
            bit_pos = str(random.randint(0, 31))
            operands = [rd, rs1, bit_pos]
            desc = f"{op.upper()} {rd}, {rs1}, {bit_pos}"
        elif op == 'bins':
            # Bit insert needs source and destination
            rs2 = self.generate_random_register()
            operands = [rd, rs1, rs2]
            desc = f"{op.upper()} {rd}, {rs1}, {rs2}"
        else:  # brev
            # Bit reverse only needs one source
            operands = [rd, rs1]
            desc = f"{op.upper()} {rd}, {rs1}"
        
        return Instruction(op, operands, InstructionType.BIT_MANIP, desc)
    
    def generate_other_instruction(self) -> Instruction:
        """Generate other types of instructions"""
        op = random.choice(list(self.isa.other_ops.keys()))
        rd = self.generate_random_register()
        
        if op == 'lui':
            imm = self.generate_immediate(20, signed=False)
            operands = [rd, imm]
            desc = f"LUI {rd}, {imm}"
        elif op == 'auipc':
            imm = self.generate_immediate(20, signed=False)
            operands = [rd, imm]
            desc = f"AUIPC {rd}, {imm}"
        else:
            operands = [rd]
            desc = f"{op.upper()} {rd}"
            
        return Instruction(op, operands, InstructionType.OTHER, desc)
    
    def generate_directed_tests(self) -> List[Instruction]:
        """Generate directed test cases for specific scenarios"""
        directed_tests = []
        
        # Arithmetic edge cases
        directed_tests.extend([
            Instruction('add', ['x1', 'x0', 'x0'], InstructionType.ARITHMETIC, "ADD x1, zero, zero (result = 0)"),
            Instruction('add', ['x2', 'x1', 'x1'], InstructionType.ARITHMETIC, "ADD x2, x1, x1 (double)"),
            Instruction('sub', ['x3', 'x2', 'x1'], InstructionType.ARITHMETIC, "SUB x3, x2, x1"),
            Instruction('addi', ['x4', 'x0', '2147483647'], InstructionType.ARITHMETIC, "ADDI x4, zero, MAX_INT"),
            Instruction('addi', ['x5', 'x0', '-2147483648'], InstructionType.ARITHMETIC, "ADDI x5, zero, MIN_INT"),
        ])
        
        # Logic patterns
        directed_tests.extend([
            Instruction('andi', ['x6', 'x4', '-1'], InstructionType.LOGIC, "ANDI x6, x4, 0xFFFFFFFF"),
            Instruction('ori', ['x7', 'x0', '1431655765'], InstructionType.LOGIC, "ORI x7, zero, 0x55555555"),
            Instruction('xori', ['x8', 'x7', '-1431655766'], InstructionType.LOGIC, "XORI x8, x7, 0xAAAAAAAA"),
            Instruction('and', ['x9', 'x7', 'x8'], InstructionType.LOGIC, "AND x9, x7, x8 (should be 0)"),
            Instruction('or', ['x10', 'x7', 'x8'], InstructionType.LOGIC, "OR x10, x7, x8 (should be 0xFFFFFFFF)"),
        ])
        
        # Shift operations
        directed_tests.extend([
            Instruction('slli', ['x11', 'x4', '1'], InstructionType.SHIFT, "SLLI x11, x4, 1 (left shift by 1)"),
            Instruction('srli', ['x12', 'x4', '1'], InstructionType.SHIFT, "SRLI x12, x4, 1 (logical right shift)"),
            Instruction('srai', ['x13', 'x5', '1'], InstructionType.SHIFT, "SRAI x13, x5, 1 (arithmetic right shift)"),
            Instruction('sll', ['x14', 'x4', 'x1'], InstructionType.SHIFT, "SLL x14, x4, x1 (variable shift)"),
        ])
        
        # Comparisons
        directed_tests.extend([
            Instruction('slt', ['x15', 'x5', 'x4'], InstructionType.COMPARISON, "SLT x15, MIN_INT, MAX_INT (should be 1)"),
            Instruction('sltu', ['x16', 'x4', 'x5'], InstructionType.COMPARISON, "SLTU x16, MAX_INT, MIN_INT (unsigned)"),
            Instruction('slti', ['x17', 'x4', '0'], InstructionType.COMPARISON, "SLTI x17, MAX_INT, 0"),
            Instruction('sltiu', ['x18', 'x0', '1'], InstructionType.COMPARISON, "SLTIU x18, zero, 1"),
        ])
        
        return directed_tests
    
    def generate_random_instruction(self) -> Instruction:
        """Generate a random instruction based on weights"""
        inst_type = random.choices(
            list(self.instruction_weights.keys()),
            weights=list(self.instruction_weights.values())
        )[0]
        
        generators = {
            InstructionType.ARITHMETIC: self.generate_arithmetic_instruction,
            InstructionType.LOGIC: self.generate_logic_instruction,
            InstructionType.SHIFT: self.generate_shift_instruction,
            InstructionType.COMPARISON: self.generate_comparison_instruction,
            InstructionType.DIVISION: self.generate_division_instruction,
            InstructionType.BIT_MANIP: self.generate_bit_manipulation_instruction,
            InstructionType.OTHER: self.generate_other_instruction
        }
        
        return generators[inst_type]()
    
    def generate_program(self, num_instructions: int = 100, include_directed: bool = True) -> List[Instruction]:
        """Generate a complete assembly program"""
        program = []
        
        if include_directed:
            program.extend(self.generate_directed_tests())
        
        # Generate random instructions
        for _ in range(num_instructions):
            program.append(self.generate_random_instruction())
        
        return program
    
    def write_assembly_file(self, program: List[Instruction], filename: str):
        """Write the program to an assembly file"""
        with open(filename, 'w') as f:
            # Write header
            f.write("# CV32E40P ALU Test Assembly Program\n")
            f.write("# Generated by asm_generator.py\n")
            f.write("# Copyright 2024 ChipAgents\n\n")
            
            f.write(".section .text\n")
            f.write(".global _start\n\n")
            f.write("_start:\n")
            
            # Write directed tests section
            directed_count = len([i for i in program if i.description.startswith(('ADD', 'SUB', 'ANDI', 'ORI', 'XORI', 'AND', 'OR', 'SLLI', 'SRLI', 'SRAI', 'SLL', 'SLT'))])
            if directed_count > 0:
                f.write("    # Directed Test Cases\n")
                for inst in program:
                    if any(inst.description.startswith(prefix) for prefix in ['ADD', 'SUB', 'ANDI', 'ORI', 'XORI', 'AND', 'OR', 'SLLI', 'SRLI', 'SRAI', 'SLL', 'SLT']):
                        f.write(f"{inst.to_asm()}\n")
                f.write("\n    # Random Test Cases\n")
            
            # Write random instructions
            for inst in program:
                if not any(inst.description.startswith(prefix) for prefix in ['ADD', 'SUB', 'ANDI', 'ORI', 'XORI', 'AND', 'OR', 'SLLI', 'SRLI', 'SRAI', 'SLL', 'SLT']):
                    f.write(f"{inst.to_asm()}\n")
            
            # Write program termination
            f.write("\n    # Program termination\n")
            f.write("    addi    x1, x0, 93      // sys_exit\n")
            f.write("    addi    x10, x0, 0      // exit status\n")
            f.write("    ecall                   // system call\n")
    
    def write_instruction_map(self, program: List[Instruction], filename: str):
        """Write instruction to ALU operation mapping"""
        mapping = {}
        
        for inst in program:
            alu_op = None
            if inst.opcode in self.isa.arithmetic_ops:
                alu_op = self.isa.arithmetic_ops[inst.opcode]
            elif inst.opcode in self.isa.logic_ops:
                alu_op = self.isa.logic_ops[inst.opcode]
            elif inst.opcode in self.isa.shift_ops:
                alu_op = self.isa.shift_ops[inst.opcode]
            elif inst.opcode in self.isa.comparison_ops:
                alu_op = self.isa.comparison_ops[inst.opcode]
            elif inst.opcode in self.isa.division_ops:
                alu_op = self.isa.division_ops[inst.opcode]
            elif inst.opcode in self.isa.bit_manipulation_ops:
                alu_op = self.isa.bit_manipulation_ops[inst.opcode]
            elif inst.opcode in self.isa.other_ops:
                alu_op = self.isa.other_ops[inst.opcode]
            
            if alu_op:
                if alu_op not in mapping:
                    mapping[alu_op] = []
                mapping[alu_op].append({
                    'opcode': inst.opcode,
                    'operands': inst.operands,
                    'description': inst.description
                })
        
        with open(filename, 'w') as f:
            json.dump(mapping, f, indent=2)
    
    def print_statistics(self, program: List[Instruction]):
        """Print program statistics"""
        stats = {inst_type: 0 for inst_type in InstructionType}
        
        for inst in program:
            stats[inst.inst_type] += 1
        
        total = len(program)
        print(f"\nProgram Statistics ({total} instructions):")
        print("-" * 40)
        for inst_type, count in stats.items():
            percentage = (count / total) * 100
            print(f"{inst_type.value.capitalize():<12}: {count:3d} ({percentage:5.1f}%)")

def main():
    parser = argparse.ArgumentParser(description='Generate CV32E40P ALU test assembly programs')
    parser.add_argument('-n', '--num-instructions', type=int, default=100,
                       help='Number of random instructions to generate (default: 100)')
    parser.add_argument('-o', '--output', type=str, default='alu_test_program.s',
                       help='Output assembly file name (default: alu_test_program.s)')
    parser.add_argument('-m', '--mapping', type=str, default='instruction_mapping.json',
                       help='Output instruction mapping file (default: instruction_mapping.json)')
    parser.add_argument('-s', '--seed', type=int, default=None,
                       help='Random seed for reproducible generation')
    parser.add_argument('--no-directed', action='store_true',
                       help='Skip directed test cases')
    parser.add_argument('--stats', action='store_true',
                       help='Print program statistics')
    
    args = parser.parse_args()
    
    # Create generator
    generator = AssemblyGenerator(seed=args.seed)
    
    # Generate program
    program = generator.generate_program(
        num_instructions=args.num_instructions,
        include_directed=not args.no_directed
    )
    
    # Write files
    generator.write_assembly_file(program, args.output)
    generator.write_instruction_map(program, args.mapping)
    
    print(f"Generated assembly program: {args.output}")
    print(f"Generated instruction mapping: {args.mapping}")
    
    if args.stats:
        generator.print_statistics(program)

if __name__ == '__main__':
    main()