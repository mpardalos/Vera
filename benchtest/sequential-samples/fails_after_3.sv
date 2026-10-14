module fails_after_3(input logic clk, output logic [2:0] count);
  initial count = 3'd0;
  always @(posedge clk)
    count <= count + 3'd1;
  assert property (@(posedge clk) count != 3'd3);
endmodule
