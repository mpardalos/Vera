module algebraic_identities_optimized (
    input  logic [7:0] x,
    input  logic [7:0] y,
    output logic [7:0] out1,
    output logic [7:0] out2,
    output logic [7:0] out3,
    output logic [7:0] out4
);
    assign out1 = x;
    assign out2 = y;
    assign out3 = 8'd0;
    assign out4 = x + y;
endmodule
