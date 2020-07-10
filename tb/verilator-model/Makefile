build:
	fusesoc --cores-root=../../ run --target=sim --setup --build openhw:cv32e40p:verilator-model
run:
	build/openhw_cv32e40p_verilator-model_0.1/sim-verilator/Vtop "+firmware=firmware/firmware.hex"

.PHONY: build
