module bitselect (
    input  logic [ 1:0] in1,
    input  logic [ 7:0] in2,
    output logic [0:0] out
);
   assign out = in2[in1];
endmodule
