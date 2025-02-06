module A(output wire unsigned [31:0] a, output wire unsigned [31:0] b, output wire unsigned [31:0] c);
   assign c = 32'd5;
   assign b = c;
   assign a = b + c;
endmodule : A
