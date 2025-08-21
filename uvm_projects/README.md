# CV32E40P ALU UVM Testbench Project

## 🎯 **Final Implementation Available**

This project contains the development history and final implementation of a comprehensive UVM testbench for the CV32E40P ALU module.

## 🚀 **Quick Start - Go to Final Implementation**

**To run the optimized testbench that achieves 55.20% coverage:**

```bash
cd cv32e40p/uvm_projects/final/
```

Then follow the instructions in `final/README.md`

## 📁 **Directory Structure**

```
cv32e40p/
├── rtl/                     ← CV32E40P RTL files
├── uvm_projects/            ← **UVM Testbench Project**
│   ├── final/               ← **GO HERE for the complete testbench**
│   │   ├── README.md       ← Complete setup and run instructions
│   │   ├── alu_sequences.sv ← Main UVM sequences
│   │   ├── asm_generator.py ← Assembly program generator
│   │   ├── run_sim.py      ← Simulation runner
│   │   └── ...             ← All final implementation files
│   │
│   ├── coverage_report*/    ← Historical coverage reports
│   ├── alu_*.sv            ← Development versions
│   ├── asm_generator.py    ← Development version
│   └── README.md           ← This file
│
└── ...                     ← Other CV32E40P directories
```

## 🏆 **What You'll Get**

The final implementation in the `final/` directory provides:

- **55.20% Overall Coverage** achievement
- **Assembly-driven verification** with targeted instruction generation
- **Division and bit manipulation** operation testing
- **Comprehensive RTL bug discovery**
- **Time-optimized sequences** (completes in <2 seconds)
- **Complete documentation** and analysis

## 📊 **Coverage Results**

| Metric | Achievement |
|--------|-------------|
| Overall Coverage | **55.20%** |
| Toggle Coverage | **77.56%** |
| FSM Coverage | **75.00%** |
| Condition Coverage | **62.45%** |
| Branch Coverage | **39.13%** |

## 🔧 **Development History**

This directory contains the complete development evolution:

1. **Basic assembly approach** (~27% coverage)
2. **Enhanced sequences** (~30% coverage)  
3. **Weighted optimization** (~30% coverage)
4. **Final breakthrough** (**55.20%** coverage)

For detailed analysis of the development process, see `final/COVERAGE_ANALYSIS.md`

## 🚀 **Ready to Run?**

**Navigate to the final implementation:**

```bash
cd cv32e40p/uvm_projects/final/
python3 run_sim.py --test alu_assembly_test --verbose
```

**Expected result:** 55.20% coverage with comprehensive RTL verification!

---

**For complete setup instructions, troubleshooting, and detailed documentation, see `final/README.md`**