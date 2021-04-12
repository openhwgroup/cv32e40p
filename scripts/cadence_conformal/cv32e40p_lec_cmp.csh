#!/bin/tcsh -f


# Copyright 2021 OpenHW Group
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

if ( "$GOLDEN_RTL" == "" ) then
      echo "The env variable  \$GOLDEN_RTL is empty. Please define it"
      exit -1
endif


if ( "$REVISED_RTL" == "" ) then
      echo "The env variable \$REVISED_RTL is empty. Please define it"
      exit -1
endif

setenv cnf_golden_rtl `awk '{ if ($0 ~ "sv" && $0 !~ "incdir" && $0 !~ "wrapper" && $0 !~ "tracer") print $0 }' $GOLDEN_RTL/../cv32e40p_manifest.flist | awk -v rtlpath=$GOLDEN_RTL -F "/" '{$1=rtlpath} OFS="/"'`

setenv cnf_revised_rtl `awk '{ if ($0 ~ "sv" && $0 !~ "incdir" && $0 !~ "wrapper" && $0 !~ "tracer") print $0 }' $REVISED_RTL/../cv32e40p_manifest.flist | awk -v rtlpath=$REVISED_RTL -F "/" '{$1=rtlpath} OFS="/"'`

if ( -d lec_reports ) then
	rm -rf ./lec_reports
endif

mkdir lec_reports

lec -Dofile cv32e40p_lec_conformal.sh -LOGfile cv32e40p_lec_log.log -NoGUI -xl

set nonlec=`awk '{ if ($0 ~ "Hierarchical compare : Equivalent") print "0" }' ./lec_reports/result.rpt`

if ($nonlec == 0) then
    echo "The DESIGN IS LOGICALLY EQUIVALENT"
else
    set nonlec=-1
    echo "The DESIGN IS NOT LOGICALLY EQUIVALENT"
endif

exit $nonlec
