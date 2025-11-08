module shuffled (
    input  logic [0:0] in,
    output logic [0:0] out
);
   wire [0:0] p1, p2, p3;

   assign p1 = in;
   assign out = p3;
   assign p3 = p2;
   assign p2 = p1;
endmodule
