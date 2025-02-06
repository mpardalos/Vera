module Mult (input wire [31:0]  in1,
             input wire [31:0]  in2,
             output wire [31:0] out
             );
   assign out = in2 + in1;
endmodule : Mult
