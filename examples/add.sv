module add(input wire [31:0] x, input wire [31:0] y, output wire [31:0] out);
   wire [15:0] v;
   assign v = x;
   assign out = v + y;
endmodule // add
