module combinational_single_cycle (
    input  logic [ 7:0] in1,
    input  logic [ 7:0] in2,
    output logic [15:0] out
);
   assign out =
     (in1[8'd0] ? in2 << 8'd0 : 8'd0) +
     (in1[8'd1] ? in2 << 8'd1 : 8'd0) +
     (in1[8'd2] ? in2 << 8'd2 : 8'd0) +
     (in1[8'd3] ? in2 << 8'd3 : 8'd0) +
     (in1[8'd4] ? in2 << 8'd4 : 8'd0) +
     (in1[8'd5] ? in2 << 8'd5 : 8'd0) +
     (in1[8'd6] ? in2 << 8'd6 : 8'd0) +
     (in1[8'd7] ? in2 << 8'd7 : 8'd0);
endmodule
