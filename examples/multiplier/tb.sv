`include "pipelined.sv"
`include "combinational.sv"
`include "iterative.sv"

module tb;
   reg clk = 0;
   reg [7:0] in1 = 0;
   reg [7:0] in2 = 0;
   wire [15:0] out_pipelined;
   wire [15:0] out_combinational;
   wire [15:0] out_iterative;

   pipelined pipelined(.clk(clk),
                       .in1(in1),
                       .in2(in2),
                       .out(out_pipelined));

   combinational combinational(.clk(clk),
                               .in1(in1),
                               .in2(in2),
                               .out(out_combinational));

   iterative iterative(.clk(clk),
                       .in1(in1),
                       .in2(in2),
                       .out(out_iterative));


   always #1 clk = ~clk;
   // always @(posedge clk) $display("tick | stage %d | out %d", pipelined.stage, pipelined.out);

   task test(input [7:0] val1, input [7:0] val2);
      begin
         logic [15:0] reference;
         in1 = val1;
         in2 = val2;
         // $display("start");
         repeat (10) @(posedge clk);
         reference = val1 * val2;
         if (out_pipelined !== reference) begin
            $display("Pipelined failed");
            $display("Input: %2h * %2h", in1, in2);
            $display("reference:     %h", reference);
            $display("combinational: %h", out_combinational);
            $display("pipelined:     %h", out_pipelined);
            $display("  Stage1 ", pipelined.stage1);
            $display("  Stage2 ", pipelined.stage2);
            $display("  Stage3 ", pipelined.stage3);
            $display("  Stage4 ", pipelined.stage4);
            $display("  Stage5 ", pipelined.stage5);
            $display("  Stage6 ", pipelined.stage6);
            $display("  Stage7 ", pipelined.stage7);
            $display("  Stage8 ", pipelined.stage8);
            $display("----");
            $finish();
         end
         if (out_iterative !== reference) begin
            $display("Iterative failed");
            $display("Input: %2h * %2h", in1, in2);
            $display("reference:     %h", reference);
            $display("pipelined:     %h", out_pipelined);
            $display("combinational: %h", out_combinational);
            $display("iterative: %h", out_iterative);
            $display("----");
            $finish();
         end
         if (out_combinational !== reference) begin
            $display("Combinational failed");
            $display("Input: %2h * %2h", in1, in2);
            $display("reference:     %h", reference);
            $display("pipelined:     %h", out_pipelined);
            $display("combinational: %h", out_combinational);
            $display("----");
            $finish();
         end
         $display("%d * %d = %d | %d | %d", v1, v2, out_combinational, out_iterative, out_pipelined);
      end
   endtask; // show

   logic [7:0]        v1, v2;
   initial begin
      for (v1 = 0; v1 < 'hff; v1 += 1) begin
         for (v2 = 0; v2 < 'hff; v2 += 1) begin
            test(v1, v2);
         end
      end
      $finish();
   end
endmodule // tb
