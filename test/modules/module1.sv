module M();
  reg x;
  reg [31:0] y;

  assign x = 1;
  always @(posedge clk) begin
    y = 2;
    y = 3;
  end
endmodule
