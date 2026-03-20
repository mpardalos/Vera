// Written by Claude, adapted from 8-bit Gemini version
module karatsuba (
    input  logic [31:0] in1,
    input  logic [31:0] in2,
    output logic [63:0] out
);
    // 1. Split inputs into high and low 16-bit halves
    wire [15:0] a1;
    wire [15:0] a0;
    wire [15:0] b1;
    wire [15:0] b0;

    assign a1 = in1[31:16];
    assign a0 = in1[15:0];
    assign b1 = in2[31:16];
    assign b0 = in2[15:0];

    // 2. Calculate Z0 = a0 * b0 (Inlined 16x16 shift-and-add multiplication)
    wire [31:0] z0;
    assign z0 = (a0[0]  ? {16'd0, b0}            : 32'd0) +
                (a0[1]  ? {15'd0, b0, 1'b0}       : 32'd0) +
                (a0[2]  ? {14'd0, b0, 2'b00}      : 32'd0) +
                (a0[3]  ? {13'd0, b0, 3'b000}     : 32'd0) +
                (a0[4]  ? {12'd0, b0, 4'b0000}    : 32'd0) +
                (a0[5]  ? {11'd0, b0, 5'b00000}   : 32'd0) +
                (a0[6]  ? {10'd0, b0, 6'b000000}  : 32'd0) +
                (a0[7]  ? {9'd0, b0, 7'b0000000}  : 32'd0) +
                (a0[8]  ? {8'd0, b0, 8'd0}        : 32'd0) +
                (a0[9]  ? {7'd0, b0, 9'd0}        : 32'd0) +
                (a0[10] ? {6'd0, b0, 10'd0}       : 32'd0) +
                (a0[11] ? {5'd0, b0, 11'd0}       : 32'd0) +
                (a0[12] ? {4'd0, b0, 12'd0}       : 32'd0) +
                (a0[13] ? {3'd0, b0, 13'd0}       : 32'd0) +
                (a0[14] ? {2'd0, b0, 14'd0}       : 32'd0) +
                (a0[15] ? {1'd0, b0, 15'd0}       : 32'd0);

    // 3. Calculate Z2 = a1 * b1 (Inlined 16x16 shift-and-add multiplication)
    wire [31:0] z2;
    assign z2 = (a1[0]  ? {16'd0, b1}            : 32'd0) +
                (a1[1]  ? {15'd0, b1, 1'b0}       : 32'd0) +
                (a1[2]  ? {14'd0, b1, 2'b00}      : 32'd0) +
                (a1[3]  ? {13'd0, b1, 3'b000}     : 32'd0) +
                (a1[4]  ? {12'd0, b1, 4'b0000}    : 32'd0) +
                (a1[5]  ? {11'd0, b1, 5'b00000}   : 32'd0) +
                (a1[6]  ? {10'd0, b1, 6'b000000}  : 32'd0) +
                (a1[7]  ? {9'd0, b1, 7'b0000000}  : 32'd0) +
                (a1[8]  ? {8'd0, b1, 8'd0}        : 32'd0) +
                (a1[9]  ? {7'd0, b1, 9'd0}        : 32'd0) +
                (a1[10] ? {6'd0, b1, 10'd0}       : 32'd0) +
                (a1[11] ? {5'd0, b1, 11'd0}       : 32'd0) +
                (a1[12] ? {4'd0, b1, 12'd0}       : 32'd0) +
                (a1[13] ? {3'd0, b1, 13'd0}       : 32'd0) +
                (a1[14] ? {2'd0, b1, 14'd0}       : 32'd0) +
                (a1[15] ? {1'd0, b1, 15'd0}       : 32'd0);

    // 4. Calculate Z1 = (a1 + a0) * (b1 + b0) - z2 - z0
    wire [16:0] sum_a;
    wire [16:0] sum_b;
    assign sum_a = a1 + a0;
    assign sum_b = b1 + b0;

    // Inlined 17x17 multiplication for the middle product
    wire [33:0] sum_prod;
    assign sum_prod = (sum_a[0]  ? {17'd0, sum_b}             : 34'd0) +
                      (sum_a[1]  ? {16'd0, sum_b, 1'b0}       : 34'd0) +
                      (sum_a[2]  ? {15'd0, sum_b, 2'b00}      : 34'd0) +
                      (sum_a[3]  ? {14'd0, sum_b, 3'b000}     : 34'd0) +
                      (sum_a[4]  ? {13'd0, sum_b, 4'b0000}    : 34'd0) +
                      (sum_a[5]  ? {12'd0, sum_b, 5'b00000}   : 34'd0) +
                      (sum_a[6]  ? {11'd0, sum_b, 6'b000000}  : 34'd0) +
                      (sum_a[7]  ? {10'd0, sum_b, 7'b0000000} : 34'd0) +
                      (sum_a[8]  ? {9'd0, sum_b, 8'd0}        : 34'd0) +
                      (sum_a[9]  ? {8'd0, sum_b, 9'd0}        : 34'd0) +
                      (sum_a[10] ? {7'd0, sum_b, 10'd0}       : 34'd0) +
                      (sum_a[11] ? {6'd0, sum_b, 11'd0}       : 34'd0) +
                      (sum_a[12] ? {5'd0, sum_b, 12'd0}       : 34'd0) +
                      (sum_a[13] ? {4'd0, sum_b, 13'd0}       : 34'd0) +
                      (sum_a[14] ? {3'd0, sum_b, 14'd0}       : 34'd0) +
                      (sum_a[15] ? {2'd0, sum_b, 15'd0}       : 34'd0) +
                      (sum_a[16] ? {1'd0, sum_b, 16'd0}       : 34'd0);

    wire [33:0] z1;
    assign z1 = sum_prod - z2 - z0;

    // 5. Final recombination: (Z2 * 2^32) + (Z1 * 2^16) + Z0
    wire [63:0] z2_shifted;
    wire [63:0] z1_shifted;
    wire [63:0] z0_extended;

    assign z2_shifted  = {z2, 32'd0};
    assign z1_shifted  = {14'd0, z1, 16'd0};
    assign z0_extended = {32'd0, z0};

    assign out = z2_shifted + z1_shifted + z0_extended;

endmodule
