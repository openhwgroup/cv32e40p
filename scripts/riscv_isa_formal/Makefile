commonPath=../../verif
PREPARE?=0
RTL?=../../cv32e40p/
GUI?=0
NAME?=noname

ifeq ($(APP),)
  $(error APP is empty)
endif
ifeq ($(CONF),)
  $(error CONF is empty)
endif
ifeq ($(MODE),)
  $(error MODE is empty)
endif

$(info APP=$(APP))
$(info CONF=$(CONF))
$(info MODE=$(MODE))

ifeq ($(GUI), 1)
  flag="-i"
else
  flag=
endif

dirname=$(NAME)

ifeq ($(PREPARE), 1)
  script_name=ones_prepare_run
else
  script_name=ones_run
endif

define ones_prepare_run
	@echo "===================================================="
	@echo "Preparing working area $(dirname)"
	@echo "===================================================="
	\mkdir -p cfgs/$(dirname)/logs
	\cd cfgs/$(dirname) && \cp -pf $(commonPath)/{other_bindings.sv,core_checker.sv,io.sv,setup.tcl,setup_mv.tcl,*.json,constraints.sv,t.sh,basics.tcl.obf} . && \cp -prfL $(commonPath)/vips . && \cp -prfL $(RTL) .
	@echo "===================================================="
	@echo "Running mode $(MODE) on configuration $(CONF) in $(dirname)"
	@echo "===================================================="
	\cd cfgs/$(dirname) && onespin -Q -l logs/$(APP)-cfg_$(CONF)-mode_$(MODE).log $(flag) setup.tcl $(CONF) $(MODE) $(APP)
endef

define ones_run
	@echo "===================================================="
	@echo "Running mode $(MODE) on configuration $(CONF) in $(dirname)"
	@echo "===================================================="
	\cd cfgs/$(dirname) && onespin -Q -l logs/$(APP)-cfg_$(CONF)-mode_$(MODE).log $(flag) setup.tcl $(CONF) $(MODE) $(APP)
endef

all:
	$(call $(script_name))

clean: 
	rm -rf cfgs/$(dirname)

