module nondeterminism1(input clk, output a, output b);
   reg [1:0] a;
   reg [1:0] b;

   always @(posedge clk) a = a + 1;
   always @(posedge clk) b = a;
endmodule // nondeterminism1
