module boolean_simp_reference (
    input  logic [7:0] x,
    input  logic [7:0] y,
    output logic [7:0] out1,
    output logic [7:0] out2,
    output logic [7:0] out3,
    output logic [7:0] out4
);
    assign out1 = x & ~x;
    assign out2 = y | ~y;
    assign out3 = (x & ~x) + (y | ~y);
    assign out4 = x & (x | y);
endmodule
