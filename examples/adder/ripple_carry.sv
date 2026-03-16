module adder_ripple_carry (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [8:0] sum
);
    // Bit 0
    wire c0;
    wire [0:0] s0;
    assign s0 = a[0] ^ b[0];
    assign c0 = a[0] & b[0];

    // Bit 1
    wire [0:0] c1;
    wire [0:0] s1;
    assign s1 = a[1] ^ b[1] ^ c0;
    assign c1 = (a[1] & b[1]) | (a[1] & c0) | (b[1] & c0);

    // Bit 2
    wire [0:0] c2;
    wire [0:0] s2;
    assign s2 = a[2] ^ b[2] ^ c1;
    assign c2 = (a[2] & b[2]) | (a[2] & c1) | (b[2] & c1);

    // Bit 3
    wire [0:0] c3;
    wire [0:0] s3;
    assign s3 = a[3] ^ b[3] ^ c2;
    assign c3 = (a[3] & b[3]) | (a[3] & c2) | (b[3] & c2);

    // Bit 4
    wire [0:0] c4;
    wire [0:0] s4;
    assign s4 = a[4] ^ b[4] ^ c3;
    assign c4 = (a[4] & b[4]) | (a[4] & c3) | (b[4] & c3);

    // Bit 5
    wire [0:0] c5;
    wire [0:0] s5;
    assign s5 = a[5] ^ b[5] ^ c4;
    assign c5 = (a[5] & b[5]) | (a[5] & c4) | (b[5] & c4);

    // Bit 6
    wire [0:0] c6;
    wire [0:0] s6;
    assign s6 = a[6] ^ b[6] ^ c5;
    assign c6 = (a[6] & b[6]) | (a[6] & c5) | (b[6] & c5);

    // Bit 7
    wire [0:0] c7;
    wire [0:0] s7;
    assign s7 = a[7] ^ b[7] ^ c6;
    assign c7 = (a[7] & b[7]) | (a[7] & c6) | (b[7] & c6);

    assign sum = {c7, s7, s6, s5, s4, s3, s2, s1, s0};
endmodule
