module identity_ops_reference (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic [7:0] c,
    output logic [7:0] out1,
    output logic [7:0] out2,
    output logic [7:0] out3,
    output logic [7:0] out4
);
    assign out1 = a + 8'd0;
    assign out2 = b * 8'd1;
    assign out3 = c & 8'b11111111;
    assign out4 = (a | 8'd0) + (b << 8'd0);
endmodule
