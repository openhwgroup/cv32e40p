import os
import subprocess

## Code must run in Python 2.7

def sim(arg=None):
    # Compile the Verilog program
    if (arg is None):
        compile_command = "vcs -sverilog -f ../core-sim.txt -full64 -P /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/novas.tab /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/pli.a -R -q"
        compile_directory = "./sim/"
        try:
            subprocess.call(compile_command, cwd=compile_directory, shell=True)
            print("Compilation successful.")
        except subprocess.CalledProcessError as e:
            print("Compilation failed:", e)
            return
    elif (arg == "mult"):
        compile_command = "vcs -sverilog ../rtl/include/cv32e40p_pkg.sv  ../rtl/cv32e40p_mult.sv mult_tb.sv -full64 -P /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/novas.tab /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/pli.a -R -q"
        compile_directory = "./sim/"
        try:
            subprocess.call(compile_command, cwd=compile_directory, shell=True)
            print("Compilation for mult successful.")
        except subprocess.CalledProcessError as e:
            print("Compilation for mult failed:", e)
            return
    elif (arg == "controller"):
        compile_command = "vcs -sverilog ../rtl/include/cv32e40p_pkg.sv  ../rtl/cv32e40p_controller.sv controller_tb.sv -full64 -P /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/novas.tab /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/pli.a -R -q"
        compile_directory = "./sim/"
        try:
            subprocess.call(compile_command, cwd=compile_directory, shell=True)
            print("Compilation for controller successful.")
        except subprocess.CalledProcessError as e:
            print("Compilation for controller failed:", e)
            return
    
def clean_sim(arg=None):
    # Clean the simulation directory
    clean_command = "rm -rf simv csrc simv.daidir ucli.key"
    clean_directory = "./sim/"
    try:
        subprocess.call(clean_command, cwd=clean_directory, shell=True)
        print("Clean successful.")
    except subprocess.CalledProcessError as e:
        print("Clean failed:", e)

def syn(arg=None):
    # Run the DC shell script
    dc_command = "dc_shell -x \"source "+ arg +".tcl\""
    dc_directory = "./syn/"
    try:
        subprocess.call(dc_command, cwd=dc_directory, shell=True)
        print("DC shell script executed successfully.")
    except subprocess.CalledProcessError as e:
        print("DC shell script execution failed:", e)

def clean_syn(arg=None):
    # Clean the synthesis directory
    clean_command = "rm -rf *.log *.vcd *.db *.drc *.sdc *.v"
    clean_directory = "./syn/"
    try:
        subprocess.call(clean_command, cwd=clean_directory, shell=True)
        print("Synthesis clean successful.")
    except subprocess.CalledProcessError as e:
        print("Synthesis clean failed:", e)

def ptpx(arg=None):
    # Run the PTPX script
    ptpx_command = "ptpx -x \"source "+ arg +".tcl\""
    ptpx_directory = "./ptpx/"
    try:
        subprocess.call(ptpx_command, cwd=ptpx_directory, shell=True)
        print("PTPX script executed successfully.")
    except subprocess.CalledProcessError as e:
        print("PTPX script execution failed:", e)

def clean_ptpx(arg=None):
    # Clean the PTPX directory
    clean_command = "rm -rf *.log"
    clean_directory = "./ptpx/"
    try:
        subprocess.call(clean_command, cwd=clean_directory, shell=True)
        print("PTPX clean successful.")
    except subprocess.CalledProcessError as e:
        print("PTPX clean failed:", e)