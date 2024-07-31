module Mult(input in, input power, output out);
   wire [31:0] in;
   wire [31:0] power;
   wire [31:0] out;

   wire [31:0] multiplier;
   assign multiplier = 1 << power;
   assign out = in * multiplier;
endmodule // Mult
