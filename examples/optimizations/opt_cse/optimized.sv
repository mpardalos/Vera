module cse_optimized (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic [7:0] c,
    output logic [7:0] out1,
    output logic [7:0] out2,
    output logic [7:0] out3
);
    wire [7:0] temp1;
    wire [7:0] temp2;

    assign temp1 = a + b;
    assign temp2 = a & b;

    assign out1 = temp1 * temp1;
    assign out2 = temp1 + c;
    assign out3 = temp2 + (temp2 << 8'd1);
endmodule
