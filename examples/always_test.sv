module always_test(input wire [15:0] x);
   reg [31:0] r1;
   reg [31:0] r2;

   initial begin
      r1 = 1;
      r2 = 2;
   end

   always @(posedge clk) begin
      r2 <= r2 + 1;
      r1 = r1 + 1;
      r2 = r1 * 2;
   end
endmodule; // always_test
