#!/bin/csh -f

cd /home/csgrad/vtovmasian/cs220_project/cv32e40p/sim

#This ENV is used to avoid overriding current script in next vcselab run 
setenv SNPS_VCSELAB_SCRIPT_NO_OVERRIDE  1

/usr/local/synopsys/vcs/T-2022.06-1/linux64/bin/vcselab $* \
    -o \
    simv \
    -nobanner \

cd -

