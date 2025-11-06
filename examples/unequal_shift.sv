module combinational_single_cycle (
    input  logic [3:0] in1,
    // input  logic [4:0] in2,
    output logic [4:0] out
);
   assign out = in1 << 8'd3;
endmodule
