set sv_input $::env(SV_INPUT)
set sv_output $::env(SV_OUTPUT)

yosys read_verilog -sv $sv_input
yosys hierarchy -auto-top
yosys proc
yosys opt
yosys alumacc
yosys extract_fa
yosys techmap
yosys opt
yosys abc -g simple
yosys clean
yosys write_verilog $sv_output
