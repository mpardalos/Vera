module combinational_star (
    input  logic [ 7:0] in1,
    input  logic [ 7:0] in2,
    output logic [15:0] out
);
   assign out = in1 * in2;
endmodule
