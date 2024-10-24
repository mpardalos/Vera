module combinational (
    input  logic        clk,
    input  logic [ 7:0] in1,
    input  logic [ 7:0] in2,
    output logic [15:0] out
);
   logic [3:0] stage;
   logic [15:0] result;
   logic [15:0] val1, val2;

   initial begin
      stage = 3'd0;
      val1 = 16'd0;
      val2 = 16'd0;
   end

   // Stage logic
   always @(posedge clk) begin
      stage <= (stage < 4'd9) ? stage + 3'd1 : 3'd0;
   end

   // Stage 0: Capture inputs
   always @(posedge clk) begin
      if (stage == 0) begin
         val1 <= in1;
         val2 <= in2;
      end
   end

   // Datapath
   assign result = (val1[0] ? val2 << 0 : 8'd0) +
                   (val1[1] ? val2 << 1 : 8'd0) +
                   (val1[2] ? val2 << 2 : 8'd0) +
                   (val1[3] ? val2 << 3 : 8'd0) +
                   (val1[4] ? val2 << 4 : 8'd0) +
                   (val1[5] ? val2 << 5 : 8'd0) +
                   (val1[6] ? val2 << 6 : 8'd0) +
                   (val1[7] ? val2 << 7 : 8'd0);

   // Output logic
   assign out = (stage == 4'd9) ? result : 16'd0;
endmodule
