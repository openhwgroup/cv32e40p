#!/usr/bin/env python3
"""
CV32E40P ALU UVM Simulation Runner
Copyright 2024 ChipAgents
SPDX-License-Identifier: Apache-2.0

Description: Python script to build and run UVM testbench using Synopsys VCS
             based on YAML configuration file.
"""

import os
import sys
import yaml
import subprocess
import argparse
import logging
from pathlib import Path
from datetime import datetime

class SimulationRunner:
    def __init__(self, config_file="config.yaml"):
        """Initialize the simulation runner with configuration."""
        self.config_file = config_file
        self.config = self.load_config()
        self.setup_logging()
        self.setup_environment()
        
    def load_config(self):
        """Load YAML configuration file."""
        try:
            with open(self.config_file, 'r') as f:
                config = yaml.safe_load(f)
            return config
        except FileNotFoundError:
            print(f"Error: Configuration file '{self.config_file}' not found.")
            sys.exit(1)
        except yaml.YAMLError as e:
            print(f"Error parsing YAML configuration: {e}")
            sys.exit(1)
    
    def setup_logging(self):
        """Setup logging configuration."""
        log_dir = Path(self.config['directories']['logs'])
        log_dir.mkdir(exist_ok=True)
        
        log_file = log_dir / f"simulation_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
        
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s',
            handlers=[
                logging.FileHandler(log_file),
                logging.StreamHandler(sys.stdout)
            ]
        )
        self.logger = logging.getLogger(__name__)
        
    def setup_environment(self):
        """Setup environment variables."""
        env_vars = self.config.get('environment', {})
        for var, value in env_vars.items():
            # Expand environment variables in the value
            expanded_value = os.path.expandvars(value)
            os.environ[var] = expanded_value
            self.logger.info(f"Set {var}={expanded_value}")
    
    def create_directories(self):
        """Create necessary directories."""
        dirs = self.config['directories']
        for dir_name, dir_path in dirs.items():
            Path(dir_path).mkdir(parents=True, exist_ok=True)
            self.logger.info(f"Created directory: {dir_path}")
    
    def find_rtl_dependencies(self):
        """Find RTL dependencies that might be needed."""
        rtl_deps = []
        rtl_dir = Path("../cv32e40p/rtl")
        
        # Check for ALU sub-module dependencies (required by cv32e40p_alu.sv)
        potential_deps = [
            "cv32e40p_alu_div.sv",
            "cv32e40p_popcnt.sv", 
            "cv32e40p_ff_one.sv"
        ]
        
        for dep in potential_deps:
            dep_path = rtl_dir / dep
            if dep_path.exists():
                rtl_deps.append(str(dep_path))
                self.logger.info(f"Found ALU sub-module dependency: {dep_path}")
        
        return rtl_deps
    
    def build_compile_command(self):
        """Build the VCS compilation command."""
        compile_opts = self.config['compile']['vcs_options'].copy()
        
        # Add include directories
        for inc_dir in self.config['dut']['include_dirs']:
            compile_opts.append(f"+incdir+{inc_dir}")
        
        # Add defines
        for define in self.config['compile']['defines']:
            compile_opts.append(f"+define+{define}")
        
        # Add coverage options if enabled
        if self.config['coverage']['enabled']:
            compile_opts.extend([
                "-cm", "line+cond+fsm+branch+tgl",
                "-cm_dir", "./coverage/simv.vdb"
            ])
        
        # Build file list
        files = []
        
        # Add UVM package first (expand environment variables)
        uvm_pkg = os.path.expandvars("$UVM_HOME/src/uvm_pkg.sv")
        if os.path.exists(uvm_pkg):
            files.append(uvm_pkg)
        
        # Add design packages
        files.extend(self.config['dut']['packages'])
        
        # Add RTL files (avoid duplicates)
        rtl_files = list(self.config['dut']['rtl_files'])
        rtl_deps = self.find_rtl_dependencies()
        
        # Only add dependencies that aren't already in the RTL files list
        for dep in rtl_deps:
            if dep not in rtl_files:
                rtl_files.append(dep)
        
        files.extend(rtl_files)
        
        # Add UVM testbench files in correct order
        tb_files = []
        for component in self.config['testbench']['component_files']:
            if os.path.exists(component):
                tb_files.append(component)
        
        # Add test file last
        tb_files.extend(self.config['testbench']['test_files'])
        files.extend(tb_files)
        
        # Build complete command
        cmd = ["vcs"] + compile_opts + files + ["-o", "simv"]
        
        return cmd, files
    
    def build_simulation_command(self, test_name=None):
        """Build the simulation command."""
        sim_opts = []
        
        # Add test name
        if test_name:
            sim_opts.append(f"+UVM_TESTNAME={test_name}")
        else:
            sim_opts.append(f"+UVM_TESTNAME={self.config['testbench']['test_name']}")
        
        # Add verbosity
        sim_opts.append(f"+UVM_VERBOSITY={self.config['testbench']['verbosity']}")
        
        # Add simulation options
        sim_opts.extend(self.config['simulation']['plusargs'])
        
        # Add wave dumping if enabled
        if self.config['simulator']['waves']:
            dump_opts = self.config['simulation']['dump_options']
            sim_opts.extend([
                f"+vpdfile+{dump_opts['file']}",
                "+vpdfileswitchsize+1000",
                "+vpdfilesize+1000"
            ])
        
        # Add coverage if enabled
        if self.config['coverage']['enabled']:
            sim_opts.extend([
                "-cm", "line+cond+fsm+branch+tgl",
                "-cm_dir", "./coverage/simv.vdb"
            ])
        
        # Add timeout
        timeout = self.config['testbench']['timeout']
        sim_opts.append(f"+UVM_TIMEOUT={timeout}")
        
        cmd = ["./simv"] + sim_opts + ["-l", "simulation.log"]
        
        return cmd
    
    def run_command(self, cmd, description):
        """Run a shell command and handle errors."""
        self.logger.info(f"Running {description}...")
        self.logger.info(f"Command: {' '.join(cmd)}")
        
        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300  # 5 minute timeout
            )
            
            if result.stdout:
                self.logger.info(f"STDOUT:\n{result.stdout}")
            if result.stderr:
                self.logger.warning(f"STDERR:\n{result.stderr}")
            
            if result.returncode != 0:
                self.logger.error(f"{description} failed with return code {result.returncode}")
                return False
            else:
                self.logger.info(f"{description} completed successfully")
                return True
                
        except subprocess.TimeoutExpired:
            self.logger.error(f"{description} timed out")
            return False
        except Exception as e:
            self.logger.error(f"Error running {description}: {e}")
            return False
    
    def clean(self):
        """Clean previous build artifacts."""
        self.logger.info("Cleaning previous build artifacts...")
        clean_commands = self.config['commands']['clean']
        
        for cmd_str in clean_commands:
            cmd = cmd_str.split()
            self.run_command(cmd, "Clean")
    
    def compile(self):
        """Compile the design and testbench."""
        self.logger.info("Starting compilation...")
        
        # Create directories
        self.create_directories()
        
        # Build and run compile command
        cmd, files = self.build_compile_command()
        
        self.logger.info("Files to be compiled:")
        for f in files:
            self.logger.info(f"  - {f}")
        
        return self.run_command(cmd, "Compilation")
    
    def simulate(self, test_name=None):
        """Run the simulation."""
        self.logger.info("Starting simulation...")
        
        cmd = self.build_simulation_command(test_name)
        return self.run_command(cmd, "Simulation")
    
    def generate_coverage_report(self):
        """Generate coverage report if coverage is enabled."""
        if not self.config['coverage']['enabled']:
            return True
            
        self.logger.info("Generating coverage report...")
        
        cmd = [
            "urg",
            "-dir", "./coverage/simv.vdb",
            "-report", self.config['coverage']['report_dir'],
            "-format", "both"
        ]
        
        return self.run_command(cmd, "Coverage Report Generation")
    
    def run_test(self, test_name=None, clean_first=True):
        """Run complete test flow."""
        self.logger.info(f"Starting test run for: {test_name or 'default test'}")
        
        # Clean if requested
        if clean_first:
            self.clean()
        
        # Compile
        if not self.compile():
            self.logger.error("Compilation failed, aborting test run")
            return False
        
        # Simulate
        if not self.simulate(test_name):
            self.logger.error("Simulation failed")
            return False
        
        # Generate coverage report
        if not self.generate_coverage_report():
            self.logger.warning("Coverage report generation failed")
        
        self.logger.info("Test run completed successfully")
        return True

def main():
    """Main function to handle command line arguments and run simulation."""
    parser = argparse.ArgumentParser(description="CV32E40P ALU UVM Simulation Runner")
    parser.add_argument("-c", "--config", default="config.yaml", 
                       help="Configuration file (default: config.yaml)")
    parser.add_argument("-t", "--test", default=None,
                       help="Test name to run (default: from config)")
    parser.add_argument("--no-clean", action="store_true",
                       help="Skip cleaning before compilation")
    parser.add_argument("--compile-only", action="store_true",
                       help="Only compile, don't simulate")
    parser.add_argument("--sim-only", action="store_true",
                       help="Only simulate (assumes already compiled)")
    parser.add_argument("-v", "--verbose", action="store_true",
                       help="Enable verbose logging")
    
    args = parser.parse_args()
    
    # Create simulation runner
    try:
        runner = SimulationRunner(args.config)
    except Exception as e:
        print(f"Error initializing simulation runner: {e}")
        sys.exit(1)
    
    # Set verbose logging if requested
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    # Run based on arguments
    success = True
    
    if args.compile_only:
        if not args.no_clean:
            runner.clean()
        success = runner.compile()
    elif args.sim_only:
        success = runner.simulate(args.test)
    else:
        success = runner.run_test(args.test, not args.no_clean)
    
    # Exit with appropriate code
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()