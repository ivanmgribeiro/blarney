include *.mk

different:
	verilator --cc Pebbles.v -y $(BLARNEY_ROOT)/Verilog --exe Pebbles.cpp
	# verilator --cc Pebbles.v -y $(BLARNEY_ROOT)/Verilog --exe Pebbles.cpp
	make -j -C obj_dir/ -f VPebbles.mk VPebbles
	cp obj_dir/VPebbles .

different-trace:
	verilator --trace --cc Pebbles.v -y $(BLARNEY_ROOT)/Verilog --exe Pebbles.cpp
	# verilator --cc Pebbles.v -y $(BLARNEY_ROOT)/Verilog --exe Pebbles.cpp
	make -j -C obj_dir/ -f VPebbles.mk VPebbles
	cp obj_dir/VPebbles .
