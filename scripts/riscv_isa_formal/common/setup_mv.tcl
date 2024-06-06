if {![info exists ::env(DESIGN_RTL_DIR)]} {
	set ::env(DESIGN_RTL_DIR) [pwd]/rtl
}
set_read_hdl_option -verilog_version sv2012 -pragma_ignore {translate_}
vlog -sv -f cv32e40p_fpu_manifest.flist
elaborate 
compile
set_mode mv
