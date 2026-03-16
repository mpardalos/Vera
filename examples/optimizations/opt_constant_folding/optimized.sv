module constant_folding_optimized (
    input  logic [7:0] x,
    input  logic [7:0] y,
    output logic [7:0] result
);
    assign result = x + 8'd8 + y + 8'd8 + 8'd8;
endmodule
