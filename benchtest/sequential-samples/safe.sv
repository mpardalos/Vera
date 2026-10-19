module safe(input logic clk, output logic [2:0] count);
  initial count = 3'd0;
  always @(posedge clk)
    count <= count + 3'd2;
  assert property (@(posedge clk) count % 3'd2 == 3'd0);
endmodule
