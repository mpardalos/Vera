module rangeselect(input [31:0] in, output [7:0] out);
   assign out = in >> 16;;
endmodule // rangeselect
