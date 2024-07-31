module Shift(input in, input power, output out);
   wire [31:0] in;
   wire [31:0] power;
   wire [31:0] out;

   assign out = in << power;
endmodule // Shift
