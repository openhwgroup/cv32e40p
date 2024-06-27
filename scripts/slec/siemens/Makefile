##############################################################################
#             Copyright 2006-Mentor Graphics Corporation
#
#             THIS SOFTWARE AND RELATED DOCUMENTATION
#            ARE PROPRIETARY AND CONFIDENTIAL TO SIEMENS.
#                        © 2023 Siemens

INSTALL := $(shell qverify -install_path)
VLIB = $(INSTALL)/modeltech/linux_x86_64/vlib
VMAP = $(INSTALL)/modeltech/linux_x86_64/vmap
VLOG = $(INSTALL)/modeltech/linux_x86_64/vlog
VCOM = $(INSTALL)/modeltech/linux_x86_64/vcom

run_sec_vl: clean run_sec

run_sec:
	$(VLIB) work_ip_orig
	$(VLIB) work_ip_mod
	$(VMAP) work_spec work_ip_orig
	$(VMAP) work_impl work_ip_mod
	$(VLOG) -sv -f $(SPEC_FLIST) -work work_spec
	$(VLOG) -sv -f $(IMPL_FLIST) -work work_impl

	qverify -c -od log -do " \
	onerror { exit 1 }; \
	slec configure -spec -d $(TOP_MODULE) -work work_spec; \
	slec configure -impl -d $(TOP_MODULE) -work work_impl; \
	slec compile; \
	slec verify -timeout 10m; \
	exit"
	@cp log/slec_verify.log $(SUMMARY_LOG)


debug:
	qverify log/slec.db

clean:
	qverify_clean
	rm -rf log* work* *.rpt modelsim.ini .visualizer visualizer*


