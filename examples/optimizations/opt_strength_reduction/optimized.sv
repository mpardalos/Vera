module strength_reduction_optimized (
    input  logic [7:0] x,
    input  logic [7:0] y,
    output logic [7:0] out1,
    output logic [7:0] out2,
    output logic [7:0] out3
);
    assign out1 = x << 8'd3;
    assign out2 = y << 8'd2;
    assign out3 = (x << 8'd1) + (y << 8'd4);
endmodule
