module pipelined (
    input logic         clk,
    input logic [ 7:0]  in1,
    input logic [ 7:0]  in2,
    output logic [15:0] out
);
   logic [15:0]         stage1 = 0;
   logic [15:0]         stage2 = 0;
   logic [15:0]         stage3 = 0;
   logic [15:0]         stage4 = 0;
   logic [15:0]         stage5 = 0;
   logic [15:0]         stage6 = 0;
   logic [15:0]         stage7 = 0;
   logic [15:0]         stage8 = 0;

   logic [3:0]          stage = 0;
   logic [15:0]         val1 = 0, val2 = 0;

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

   // Pipeline
   always @(posedge clk) begin
      stage1 <= (val1[0] ? val2 << 0 : 8'd0);
      stage2 <= stage1 + (val1[1] ? val2 << 1 : 8'd0);
      stage3 <= stage2 + (val1[2] ? val2 << 2 : 8'd0);
      stage4 <= stage3 + (val1[3] ? val2 << 3 : 8'd0);
      stage5 <= stage4 + (val1[4] ? val2 << 4 : 8'd0);
      stage6 <= stage5 + (val1[5] ? val2 << 5 : 8'd0);
      stage7 <= stage6 + (val1[6] ? val2 << 6 : 8'd0);
      stage8 <= stage7 + (val1[7] ? val2 << 7 : 8'd0);
   end

   // Output logic
   assign out = (stage == 4'd9) ? stage8 : 16'd0;
endmodule
