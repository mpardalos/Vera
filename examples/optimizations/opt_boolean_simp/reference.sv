// Yosys reorders the inputs here (puts inputs at the end).
// Vera still accepts that because the inputs and the outputs are in
// the same relative order --- input order is the same, output order
// is the same.
//
// But should it? The behaviour is the same if you instantiate the
// module with named connections, but if you just use
// order-based/unnamed params then you there might be issues. Probably
// not different behaviour, because you will get an error, although
// I'm not entirely sure.
module boolean_simp_reference (
    input  logic [7:0] x,
    input  logic [7:0] y,
    output logic [7:0] out1,
    output logic [7:0] out2,
    output logic [7:0] out3,
    output logic [7:0] out4
);
    assign out1 = x & ~x;
    assign out2 = y | ~y;
    assign out3 = (x & ~x) + (y | ~y);
    assign out4 = x & (x | y);
endmodule
