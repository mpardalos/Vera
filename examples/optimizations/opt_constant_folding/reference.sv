module constant_folding_reference (
    input  logic [7:0] x,
    input  logic [7:0] y,
    output logic [7:0] result
);
    wire [7:0] const_sum;
    wire [7:0] const_prod;
    wire [7:0] const_shift;

    assign const_sum = 8'd5 + 8'd3;
    assign const_prod = 8'd4 * 8'd2;
    assign const_shift = 8'd1 << 8'd3;

    assign result = x + const_sum + y + const_prod + const_shift;
endmodule
