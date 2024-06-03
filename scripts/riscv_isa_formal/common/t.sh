#!/bin/bash
#
# This script is a template representing a customization to integrate OneSpin 360 with VCS simulator
#
# onespin calls the script as follows:
# template_vcs_flow.sh <args>
#
# In this script you need to set up the environment for the simulator,
#
ARG1=$1

vsim -64 -c -do "source ${ARG1}; quit -f"
