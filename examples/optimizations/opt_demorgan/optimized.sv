module demorgan_optimized (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic [7:0] c,
    output logic [7:0] out1,
    output logic [7:0] out2,
    output logic [7:0] out3
);
    assign out1 = ~a | ~b;
    assign out2 = ~a & ~b;
    assign out3 = (~a | ~b) & ~c;
endmodule
