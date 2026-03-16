module combinational_single_cycle (
    input  logic [7:0] in1,
    input  logic [7:0] in2,
    output logic [15:0] out
);
  wire [15:0] part0;
  assign part0 = (in1[8'd0] ? in2 << 8'd0 : 8'd0);
  wire [15:0] part1;
  assign part1 = (in1[8'd1] ? in2 << 8'd1 : 8'd0);
  wire [15:0] part2;
  assign part2 = (in1[8'd2] ? in2 << 8'd2 : 8'd0);
  wire [15:0] part3;
  assign part3 = (in1[8'd3] ? in2 << 8'd3 : 8'd0);
  wire [15:0] part4;
  assign part4 = (in1[8'd4] ? in2 << 8'd4 : 8'd0);
  wire [15:0] part5;
  assign part5 = (in1[8'd5] ? in2 << 8'd5 : 8'd0);
  wire [15:0] part6;
  assign part6 = (in1[8'd6] ? in2 << 8'd6 : 8'd0);
  wire [15:0] part7;
  assign part7 = (in1[8'd7] ? in2 << 8'd7 : 8'd0);

  assign out = part0 + part1 + part2 + part3 + part4 + part5 + part6 + part7;
endmodule
