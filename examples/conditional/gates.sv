module conditional (
    input  logic in1,
    input  logic [7:0] in2,
    input  logic [7:0] in3,
    output logic [7:0] out
);
   assign out = ({8{in1}} & in2) | ({8{~in1}} & in3);
endmodule
