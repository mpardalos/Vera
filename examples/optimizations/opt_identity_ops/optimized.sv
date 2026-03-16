module identity_ops_optimized (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic [7:0] c,
    output logic [7:0] out1,
    output logic [7:0] out2,
    output logic [7:0] out3,
    output logic [7:0] out4
);
    assign out1 = a;
    assign out2 = b;
    assign out3 = c;
    assign out4 = a + b;
endmodule
