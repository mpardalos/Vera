module iterative (
    input  logic        clk,
    input  logic [ 7:0] in1,
    input  logic [ 7:0] in2,
    output logic [15:0] out
);
   logic [3:0] stage;
   logic [15:0] accumulator;
   logic [15:0] val1, val2;

   initial begin
      stage = 3'd0;
      accumulator = 16'd0;
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

   // Stage 1-8
   always @(posedge clk) begin
      if (stage > 4'd0 && stage <= 4'd8) begin
         if (val1[stage - 4'd1]) begin
            accumulator <= accumulator + (val2 << (stage - 4'd1));
         end
      end else begin
         accumulator <= 16'd0;
      end
   end

   // Stage 9
   always @(posedge clk) begin
   end

   // Output logic
   assign out = (stage == 4'd9) ? accumulator : 16'd0;
endmodule
