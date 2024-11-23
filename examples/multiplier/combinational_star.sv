module combinational_star (
    input  logic [ 7:0] star_in1,
    input  logic [ 7:0] star_in2,
    output logic [15:0] star_out
);

   assign star_out = 1 + star_in1 * star_in2;
endmodule
