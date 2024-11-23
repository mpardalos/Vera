module combinational_single_cycle (
    input  logic [ 7:0] in1,
    input  logic [ 7:0] in2,
    output logic [15:0] out
);
   wire [15:0] part1, part2, part3, part4, part5, part6, part7, part8;

   assign part1 = (in1[0] ? in2 << 0 : 8'd0);
   assign part2 = (in1[1] ? in2 << 1 : 8'd0);
   assign part3 = (in1[2] ? in2 << 2 : 8'd0);
   assign part4 = (in1[3] ? in2 << 3 : 8'd0);
   assign part5 = (in1[4] ? in2 << 4 : 8'd0);
   assign part6 = (in1[5] ? in2 << 5 : 8'd0);
   assign part7 = (in1[6] ? in2 << 6 : 8'd0);
   assign part8 = (in1[7] ? in2 << 7 : 8'd0);

   assign out = part1 + part2 + part3 + part4 + part5 + part6 + part7 + part8;
endmodule
