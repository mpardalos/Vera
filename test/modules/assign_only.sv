module A(output a);
   wire [31:0] a;
   wire [31:0] b;
   wire [31:0] c;


   assign c = 5;
   assign b = c;
   assign a = b + c;

endmodule // A
