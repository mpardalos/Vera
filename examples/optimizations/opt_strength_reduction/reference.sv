module strength_reduction_reference (
    input  logic [7:0] x,
    input  logic [7:0] y,
    output logic [7:0] out1,
    output logic [7:0] out2,
    output logic [7:0] out3
);
    assign out1 = x * 8'd8;
    assign out2 = y * 8'd4;
    assign out3 = x * 8'd2 + y * 8'd16;
endmodule
