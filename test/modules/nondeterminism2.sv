module nondeterminism2(input clk, output a, output b, output c);
   reg [1:0] a;
   reg [1:0] b;
   reg [1:0] c;

   always @(posedge clk) begin
      a = 1;
      b = 1;
   end

   always @(posedge clk) begin
      c = a + b;
   end
endmodule // nondeterminism2
