module adder_carry_lookahead (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [8:0] sum
);
    // Generate and propagate signals
    wire [0:0] g0; assign g0 = a[8'd0] & b[8'd0];
    wire [0:0] g1; assign g1 = a[8'd1] & b[8'd1];
    wire [0:0] g2; assign g2 = a[8'd2] & b[8'd2];
    wire [0:0] g3; assign g3 = a[8'd3] & b[8'd3];
    wire [0:0] g4; assign g4 = a[8'd4] & b[8'd4];
    wire [0:0] g5; assign g5 = a[8'd5] & b[8'd5];
    wire [0:0] g6; assign g6 = a[8'd6] & b[8'd6];
    wire [0:0] g7; assign g7 = a[8'd7] & b[8'd7];

    wire [0:0] p0; assign p0 = a[8'd0] ^ b[8'd0];
    wire [0:0] p1; assign p1 = a[8'd1] ^ b[8'd1];
    wire [0:0] p2; assign p2 = a[8'd2] ^ b[8'd2];
    wire [0:0] p3; assign p3 = a[8'd3] ^ b[8'd3];
    wire [0:0] p4; assign p4 = a[8'd4] ^ b[8'd4];
    wire [0:0] p5; assign p5 = a[8'd5] ^ b[8'd5];
    wire [0:0] p6; assign p6 = a[8'd6] ^ b[8'd6];
    wire [0:0] p7; assign p7 = a[8'd7] ^ b[8'd7];

    // Group 0 (bits 0-3): carry lookahead within group
    wire [0:0] c1; assign c1 = g0;
    wire [0:0] c2; assign c2 = g1 | (p1 & g0);
    wire [0:0] c3; assign c3 = g2 | (p2 & g1) | (p2 & p1 & g0);

    // Group 0 generate and propagate
    wire [0:0] G0; assign G0 = g3 | (p3 & g2) | (p3 & p2 & g1) | (p3 & p2 & p1 & g0);
    wire [0:0] P0; assign P0 = p3 & p2 & p1 & p0;

    // Group 1 (bits 4-7): carry lookahead using group carry-in = G0
    wire [0:0] c4; assign c4 = G0;
    wire [0:0] c5; assign c5 = g4 | (p4 & G0);
    wire [0:0] c6; assign c6 = g5 | (p5 & g4) | (p5 & p4 & G0);
    wire [0:0] c7; assign c7 = g6 | (p6 & g5) | (p6 & p5 & g4) | (p6 & p5 & p4 & G0);

    // Carry out
    wire [0:0] c8; assign c8 = g7 | (p7 & g6) | (p7 & p6 & g5) | (p7 & p6 & p5 & g4) | (p7 & p6 & p5 & p4 & G0);

    // Sum bits: s_i = p_i ^ c_i (where c_0 = 0)
    wire [0:0] s0; assign s0 = p0;
    wire [0:0] s1; assign s1 = p1 ^ c1;
    wire [0:0] s2; assign s2 = p2 ^ c2;
    wire [0:0] s3; assign s3 = p3 ^ c3;
    wire [0:0] s4; assign s4 = p4 ^ c4;
    wire [0:0] s5; assign s5 = p5 ^ c5;
    wire [0:0] s6; assign s6 = p6 ^ c6;
    wire [0:0] s7; assign s7 = p7 ^ c7;

    assign sum = {c8, s7, s6, s5, s4, s3, s2, s1, s0};
endmodule
