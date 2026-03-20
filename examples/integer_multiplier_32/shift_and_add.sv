module combinational_single_cycle (
    input  logic [31:0] in1,
    input  logic [31:0] in2,
    output logic [63:0] out
);
  wire [63:0] part0;
  assign part0 = (in1[8'd0] ? in2 << 8'd0 : 32'd0);
  wire [63:0] part1;
  assign part1 = (in1[8'd1] ? in2 << 8'd1 : 32'd0);
  wire [63:0] part2;
  assign part2 = (in1[8'd2] ? in2 << 8'd2 : 32'd0);
  wire [63:0] part3;
  assign part3 = (in1[8'd3] ? in2 << 8'd3 : 32'd0);
  wire [63:0] part4;
  assign part4 = (in1[8'd4] ? in2 << 8'd4 : 32'd0);
  wire [63:0] part5;
  assign part5 = (in1[8'd5] ? in2 << 8'd5 : 32'd0);
  wire [63:0] part6;
  assign part6 = (in1[8'd6] ? in2 << 8'd6 : 32'd0);
  wire [63:0] part7;
  assign part7 = (in1[8'd7] ? in2 << 8'd7 : 32'd0);
  wire [63:0] part8;
  assign part8 = (in1[8'd8] ? in2 << 8'd8 : 32'd0);
  wire [63:0] part9;
  assign part9 = (in1[8'd9] ? in2 << 8'd9 : 32'd0);
  wire [63:0] part10;
  assign part10 = (in1[8'd10] ? in2 << 8'd10 : 32'd0);
  wire [63:0] part11;
  assign part11 = (in1[8'd11] ? in2 << 8'd11 : 32'd0);
  wire [63:0] part12;
  assign part12 = (in1[8'd12] ? in2 << 8'd12 : 32'd0);
  wire [63:0] part13;
  assign part13 = (in1[8'd13] ? in2 << 8'd13 : 32'd0);
  wire [63:0] part14;
  assign part14 = (in1[8'd14] ? in2 << 8'd14 : 32'd0);
  wire [63:0] part15;
  assign part15 = (in1[8'd15] ? in2 << 8'd15 : 32'd0);
  wire [63:0] part16;
  assign part16 = (in1[8'd16] ? in2 << 8'd16 : 32'd0);
  wire [63:0] part17;
  assign part17 = (in1[8'd17] ? in2 << 8'd17 : 32'd0);
  wire [63:0] part18;
  assign part18 = (in1[8'd18] ? in2 << 8'd18 : 32'd0);
  wire [63:0] part19;
  assign part19 = (in1[8'd19] ? in2 << 8'd19 : 32'd0);
  wire [63:0] part20;
  assign part20 = (in1[8'd20] ? in2 << 8'd20 : 32'd0);
  wire [63:0] part21;
  assign part21 = (in1[8'd21] ? in2 << 8'd21 : 32'd0);
  wire [63:0] part22;
  assign part22 = (in1[8'd22] ? in2 << 8'd22 : 32'd0);
  wire [63:0] part23;
  assign part23 = (in1[8'd23] ? in2 << 8'd23 : 32'd0);
  wire [63:0] part24;
  assign part24 = (in1[8'd24] ? in2 << 8'd24 : 32'd0);
  wire [63:0] part25;
  assign part25 = (in1[8'd25] ? in2 << 8'd25 : 32'd0);
  wire [63:0] part26;
  assign part26 = (in1[8'd26] ? in2 << 8'd26 : 32'd0);
  wire [63:0] part27;
  assign part27 = (in1[8'd27] ? in2 << 8'd27 : 32'd0);
  wire [63:0] part28;
  assign part28 = (in1[8'd28] ? in2 << 8'd28 : 32'd0);
  wire [63:0] part29;
  assign part29 = (in1[8'd29] ? in2 << 8'd29 : 32'd0);
  wire [63:0] part30;
  assign part30 = (in1[8'd30] ? in2 << 8'd30 : 32'd0);
  wire [63:0] part31;
  assign part31 = (in1[8'd31] ? in2 << 8'd31 : 32'd0);

  assign out = part0 + part1 + part2 + part3 + part4 + part5 + part6 + part7
             + part8 + part9 + part10 + part11 + part12 + part13 + part14 + part15
             + part16 + part17 + part18 + part19 + part20 + part21 + part22 + part23
             + part24 + part25 + part26 + part27 + part28 + part29 + part30 + part31;
endmodule
