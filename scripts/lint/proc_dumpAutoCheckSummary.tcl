proc dumpAutoCheckSummary { filename } { 
	namespace import -force Autocheck::* 
	if { [catch { set fp [open $filename a] } msg] } {
		puts "Unable to open $filename : $msg"
		exit 1
	}

	set typecnt 0
	#--------- Find types ---------------------------------------
	set checks [GetChecks]
	while { [set check [GetNext $checks]] != "" } {
		set type [GetType $check]
		set severity($type) [GetSeverity $check]
		lappend types $type
	}
	set types [lsort [lrmdups $types]]
	#--------- Collect data for each type -----------------------
	foreach type $types {
		set cnt 0
    set cnt_waiv 0
    set cnt_viol 0
    set cnt_caut 0
    set cnt_inconcl 0
    set cnt_info 0
    set cnt_eval 0
    set cnt_off 0
    set cnt_def 0
		set checks [GetChecks]
		while { [set check [GetNext $checks]] != "" } {
			if {[GetType $check] == $type} {
# debug
#puts $fp "[GetType $check]"
#puts $fp "[GetStatus $check]"
#puts $fp "[GetSeverity $check]"
        ### DM ### increment different counters depending of status
        if {[GetStatus $check] == "Waived"} {
          incr cnt_waiv
        } else {
          set Severity [GetSeverity $check]
          switch $Severity {
            Violation       {incr cnt_viol}
            Caution         {incr cnt_caut}
            Inconclusive    {incr cnt_inconcl}
          }
          ### DM ### add other (off, ...) if needed
        }
      }
		}

    ### DM ### only prints when waived exist / or when violation or inconclusive
    if {$cnt_waiv != 0} {
		  puts $fp "# ** Waived:\t$type ($cnt_waiv)" 
		  puts     "# ** Waived:\t$type ($cnt_waiv)" 
    }
    if {$cnt_viol != 0} {
		  puts $fp "# ** Violation:\t$type ($cnt_viol)" 
		  puts     "# ** Violation:\t$type ($cnt_viol)" 
    }
    if {$cnt_caut != 0} {
		  puts $fp "# ** Caution:\t$type ($cnt_caut)" 
		  puts     "# ** Caution:\t$type ($cnt_caut)" 
    }
    if {$cnt_inconcl != 0} {
		  puts $fp "# ** Inconclusive:\t$type ($cnt_inconcl)" 
		  puts     "# ** Inconclusive:\t$type ($cnt_inconcl)" 
    }
      ### DM ### add other (caution, off, ...) if needed

	}
	puts $fp "=============================================="
	puts $fp "  [llength $types] Types; [GetCount $checks] Checks"
	close $fp 
}

