module toggle_fails(input logic clk, output logic toggle);
  initial toggle = 1'b0;
  always @(posedge clk)
    toggle <= !toggle;
  assert property (@(posedge clk) toggle == 1'b0);
endmodule
