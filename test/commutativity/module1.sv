module Mult(input wire [31:0]  in1,
            input wire [31:0]  in2,
            output wire [31:0] out
            );
   assign out = in1 + (0 + in2);
endmodule : Mult
