module rangeselect(input [31:0] in, output [7:0] out);
   assign out = {in[23], in[22], in[21], in[20], in[19], in[18], in[17], in[16]};
endmodule // rangeselect
