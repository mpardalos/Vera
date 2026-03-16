// Written by Gemini 3.0
module karatsuba (
    input  logic [7:0] in1,
    input  logic [7:0] in2,
    output logic [15:0] out
);
    // 1. Split inputs into high and low 4-bit halves
    wire [3:0] a1;
    wire [3:0] a0;
    wire [3:0] b1;
    wire [3:0] b0;
    
    assign a1 = {in1[7], in1[6], in1[5], in1[4]};
    assign a0 = {in1[3], in1[2], in1[1], in1[0]};
    assign b1 = {in2[7], in2[6], in2[5], in2[4]};
    assign b0 = {in2[3], in2[2], in2[1], in2[0]};

    // 2. Calculate Z0 = a0 * b0 (Inlined 4x4 multiplication)
    wire [7:0] z0;
    assign z0 = (a0[0] ? {4'b0000, b0}       : 8'd0) +
                (a0[1] ? {3'b000, b0, 1'b0}  : 8'd0) +
                (a0[2] ? {2'b00, b0, 2'b00}  : 8'd0) +
                (a0[3] ? {1'b0, b0, 3'b000}  : 8'd0);

    // 3. Calculate Z2 = a1 * b1 (Inlined 4x4 multiplication)
    wire [7:0] z2;
    assign z2 = (a1[0] ? {4'b0000, b1}       : 8'd0) +
                (a1[1] ? {3'b000, b1, 1'b0}  : 8'd0) +
                (a1[2] ? {2'b00, b1, 2'b00}  : 8'd0) +
                (a1[3] ? {1'b0, b1, 3'b000}  : 8'd0);

    // 4. Calculate Z1 = (a1 + a0) * (b1 + b0) - z2 - z0
    wire [4:0] sum_a;
    wire [4:0] sum_b;
    assign sum_a = a1 + a0;
    assign sum_b = b1 + b0;
    
    // Inlined 5x5 multiplication for the middle product
    wire [9:0] sum_prod;
    assign sum_prod = (sum_a[0] ? {5'b00000, sum_b}        : 10'd0) +
                      (sum_a[1] ? {4'b0000, sum_b, 1'b0}   : 10'd0) +
                      (sum_a[2] ? {3'b000, sum_b, 2'b00}   : 10'd0) +
                      (sum_a[3] ? {2'b00, sum_b, 3'b000}   : 10'd0) +
                      (sum_a[4] ? {1'b0, sum_b, 4'b0000}   : 10'd0);
    
    wire [9:0] z1;
    assign z1 = sum_prod - z2 - z0;

    // 5. Final recombination: (Z2 * 2^8) + (Z1 * 2^4) + Z0
    // Explicit concatenation used to prevent self-determined expression truncation
    wire [15:0] z2_shifted;
    wire [15:0] z1_shifted;
    wire [15:0] z0_extended;
    
    assign z2_shifted  = {z2, 8'd0};
    assign z1_shifted  = {2'b00, z1, 4'd0};
    assign z0_extended = {8'd0, z0};

    assign out = z2_shifted + z1_shifted + z0_extended;

endmodule
