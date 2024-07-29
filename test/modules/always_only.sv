module M();
   reg x;
   reg [31:0] y;

   always @(posedge clk) begin
      x = 1;
      y = 2;
      y = 3;
   end
endmodule
