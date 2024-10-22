// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Equifuzz: Modified to remove parameter - Fixed as RV32B = RV32BFull
/**
 * Arithmetic logic unit
 */
module ibex_alu (
  input  logic [6:0]        operator_i,
  input  logic [31:0]       operand_a_i,
  input  logic [31:0]       operand_b_i,

  input  logic              instr_first_cycle_i,

  input  logic [32:0]       multdiv_operand_a_i,
  input  logic [32:0]       multdiv_operand_b_i,

  input  logic              multdiv_sel_i,

  input  logic [31:0]       imd_val_q_i[2],
  output logic [31:0]       imd_val_d_o[2],
  output logic [1:0]        imd_val_we_o,

  output logic [31:0]       adder_result_o,
  output logic [33:0]       adder_result_ext_o,

  output logic [31:0]       result_o,
  output logic              comparison_result_o,
  output logic              is_equal_result_o
);
  logic [31:0] operand_a_rev;
  logic [32:0] operand_b_neg;

  // bit reverse operand_a for left shifts and bit counting
  // for (genvar k = 0; k < 32; k++) begin : gen_rev_operand_a
  //   assign operand_a_rev[k] = operand_a_i[31-k];
  // end
  assign operand_a_rev[0] = operand_a_i[31];
  assign operand_a_rev[1] = operand_a_i[30];
  assign operand_a_rev[2] = operand_a_i[29];
  assign operand_a_rev[3] = operand_a_i[28];
  assign operand_a_rev[4] = operand_a_i[27];
  assign operand_a_rev[5] = operand_a_i[26];
  assign operand_a_rev[6] = operand_a_i[25];
  assign operand_a_rev[7] = operand_a_i[24];
  assign operand_a_rev[8] = operand_a_i[23];
  assign operand_a_rev[9] = operand_a_i[22];
  assign operand_a_rev[10] = operand_a_i[21];
  assign operand_a_rev[11] = operand_a_i[20];
  assign operand_a_rev[12] = operand_a_i[19];
  assign operand_a_rev[13] = operand_a_i[18];
  assign operand_a_rev[14] = operand_a_i[17];
  assign operand_a_rev[15] = operand_a_i[16];
  assign operand_a_rev[16] = operand_a_i[15];
  assign operand_a_rev[17] = operand_a_i[14];
  assign operand_a_rev[18] = operand_a_i[13];
  assign operand_a_rev[19] = operand_a_i[12];
  assign operand_a_rev[20] = operand_a_i[11];
  assign operand_a_rev[21] = operand_a_i[10];
  assign operand_a_rev[22] = operand_a_i[9];
  assign operand_a_rev[23] = operand_a_i[8];
  assign operand_a_rev[24] = operand_a_i[7];
  assign operand_a_rev[25] = operand_a_i[6];
  assign operand_a_rev[26] = operand_a_i[5];
  assign operand_a_rev[27] = operand_a_i[4];
  assign operand_a_rev[28] = operand_a_i[3];
  assign operand_a_rev[29] = operand_a_i[2];
  assign operand_a_rev[30] = operand_a_i[1];
  assign operand_a_rev[31] = operand_a_i[0];

  ///////////
  // Adder //
  ///////////

  logic        adder_op_a_shift1;
  logic        adder_op_a_shift2;
  logic        adder_op_a_shift3;
  logic        adder_op_b_negate;
  logic [32:0] adder_in_a, adder_in_b;
  logic [31:0] adder_result;

  always_comb begin
    adder_op_a_shift1 = 1'b0;
    adder_op_a_shift2 = 1'b0;
    adder_op_a_shift3 = 1'b0;
    adder_op_b_negate = 1'b0;
    unique case (operator_i)
      // Adder OPs
      7'd1,

      // Comparator OPs
      7'd29,   7'd30,
      7'd27,   7'd28,
      7'd25,   7'd26,
      7'd43,  7'd44,

      // MinMax OPs (RV32B Ops)
      7'd31,  7'd32,
      7'd33,  7'd34: adder_op_b_negate = 1'b1;

      // Address Calculation OPs (RV32B Ops)
      7'd22: ;
      7'd23: ;
      7'd24: ;

      default:;
    endcase
  end

  // prepare operand a
  always_comb begin
    unique case (1'b1)
      multdiv_sel_i:     adder_in_a = multdiv_operand_a_i;
      adder_op_a_shift1: adder_in_a = {operand_a_i[30:0],2'b01};
      adder_op_a_shift2: adder_in_a = {operand_a_i[29:0],3'b001};
      adder_op_a_shift3: adder_in_a = {operand_a_i[28:0],4'b0001};
      default:           adder_in_a = {operand_a_i,1'b1};
    endcase
  end

  // prepare operand b
  assign operand_b_neg = {operand_b_i,1'b0} ^ {33{1'b1}};
  always_comb begin
    unique case (1'b1)
      multdiv_sel_i:     adder_in_b = multdiv_operand_b_i;
      adder_op_b_negate: adder_in_b = operand_b_neg;
      default:           adder_in_b = {operand_b_i, 1'b0};
    endcase
  end

  // actual adder
  assign adder_result_ext_o = $unsigned(adder_in_a) + $unsigned(adder_in_b);

  assign adder_result       = adder_result_ext_o[32:1];

  assign adder_result_o     = adder_result;

  ////////////////
  // Comparison //
  ////////////////

  logic is_equal;
  logic is_greater_equal;  // handles both signed and unsigned forms
  logic cmp_signed;

  always_comb begin
    unique case (operator_i)
      7'd27,
      7'd25,
      7'd43,
      // RV32B only
      7'd31,
      7'd33: cmp_signed = 1'b1;

      default: cmp_signed = 1'b0;
    endcase
  end

  assign is_equal = (adder_result == 32'b0);
  assign is_equal_result_o = is_equal;

  // Is greater equal
  always_comb begin
    if ((operand_a_i[31] ^ operand_b_i[31]) == 1'b0) begin
      is_greater_equal = (adder_result[31] == 1'b0);
    end else begin
      is_greater_equal = operand_a_i[31] ^ (cmp_signed);
    end
  end

  // GTE unsigned:
  // (a[31] == 1 && b[31] == 1) => adder_result[31] == 0
  // (a[31] == 0 && b[31] == 0) => adder_result[31] == 0
  // (a[31] == 1 && b[31] == 0) => 1
  // (a[31] == 0 && b[31] == 1) => 0

  // GTE signed:
  // (a[31] == 1 && b[31] == 1) => adder_result[31] == 0
  // (a[31] == 0 && b[31] == 0) => adder_result[31] == 0
  // (a[31] == 1 && b[31] == 0) => 0
  // (a[31] == 0 && b[31] == 1) => 1

  // generate comparison result
  logic cmp_result;

  always_comb begin
    unique case (operator_i)
      7'd29:             cmp_result =  is_equal;
      7'd30:             cmp_result = ~is_equal;
      7'd27,   7'd28,
      7'd33,  7'd34: cmp_result = is_greater_equal; // RV32B only
      7'd25,   7'd26,
      7'd31,  7'd32, //RV32B only
      7'd43,  7'd44: cmp_result = ~is_greater_equal;

      default: cmp_result = is_equal;
    endcase
  end

  assign comparison_result_o = cmp_result;

  ///////////
  // Shift //
  ///////////

  // The shifter structure consists of a 33-bit shifter: 32-bit operand + 1 bit extension for
  // arithmetic shifts and one-shift support.
  // Rotations and funnel shifts are implemented as multi-cycle instructions.
  // The shifter is also used for single-bit instructions and bit-field place as detailed below.
  //
  // Standard Shifts
  // ===============
  // For standard shift instructions, the direction of the shift is to the right by default. For
  // left shifts, the signal shift_left signal is set. If so, the operand is initially reversed,
  // shifted to the right by the specified amount and shifted back again. For arithmetic- and
  // one-shifts the 33rd bit of the shifter operand can is set accordingly.
  //
  // Multicycle Shifts
  // =================
  //
  // Rotation
  // --------
  // For rotations, the operand signals operand_a_i and operand_b_i are kept constant to rs1 and
  // rs2 respectively.
  //
  // Rotation pseudocode:
  //   shift_amt = rs2 & 31;
  //   multicycle_result = (rs1 >> shift_amt) | (rs1 << (32 - shift_amt));
  //                       ^-- cycle 0 -----^ ^-- cycle 1 --------------^
  //
  // Funnel Shifts
  // -------------
  // For funnel shifs, operand_a_i is tied to rs1 in the first cycle and rs3 in the
  // second cycle. operand_b_i is always tied to rs2. The order of applying the shift amount or
  // its complement is determined by bit [5] of shift_amt.
  //
  // Funnel shift Pseudocode: (fsl)
  //  shift_amt = rs2 & 63;
  //  shift_amt_compl = 32 - shift_amt[4:0]
  //  if (shift_amt >=33):
  //     multicycle_result = (rs1 >> shift_amt_compl[4:0]) | (rs3 << shift_amt[4:0]);
  //                         ^-- cycle 0 ----------------^ ^-- cycle 1 ------------^
  //  else if (shift_amt <= 31 && shift_amt > 0):
  //     multicycle_result = (rs1 << shift_amt[4:0]) | (rs3 >> shift_amt_compl[4:0]);
  //                         ^-- cycle 0 ----------^ ^-- cycle 1 -------------------^
  //  For shift_amt == 0, 32, both shift_amt[4:0] and shift_amt_compl[4:0] == '0.
  //  these cases need to be handled separately outside the shifting structure:
  //  else if (shift_amt == 32):
  //     multicycle_result = rs3
  //  else if (shift_amt == 0):
  //     multicycle_result = rs1.
  //
  // Single-Bit Instructions
  // =======================
  // Single bit instructions operate on bit operand_b_i[4:0] of operand_a_i.

  // The operations bset, bclr and binv are implemented by generation of a bit-mask using the
  // shifter structure. This is done by left-shifting the operand 32'h1 by the required amount.
  // The signal shift_sbmode multiplexes the shifter input and sets the signal shift_left.
  // Further processing is taken care of by a separate structure.
  //
  // For bext, the bit defined by operand_b_i[4:0] is to be returned. This is done by simply
  // shifting operand_a_i to the right by the required amount and returning bit [0] of the result.
  //
  // Bit-Field Place
  // ===============
  // The shifter structure is shared to compute bfp_mask << bfp_off.

  logic       shift_left;
  logic       shift_ones;
  logic       shift_arith;
  logic       shift_funnel;
  logic       shift_sbmode;
  logic [5:0] shift_amt;
  logic [5:0] shift_amt_compl; // complementary shift amount (32 - shift_amt)

  logic        [31:0] shift_operand;
  logic signed [32:0] shift_result_ext_signed;
  logic        [32:0] shift_result_ext;
  logic               unused_shift_result_ext;
  logic        [31:0] shift_result;
  logic        [31:0] shift_result_rev;

  // zbf
  logic bfp_op;
  logic [4:0]  bfp_len;
  logic [4:0]  bfp_off;
  logic [31:0] bfp_mask;
  logic [31:0] bfp_mask_rev;
  logic [31:0] bfp_result;

  // bfp: shares the shifter structure to compute bfp_mask << bfp_off
  assign bfp_op = 1'b0;
  assign bfp_len = {~(|operand_b_i[27:24]), operand_b_i[27:24]}; // len = 0 encodes for len = 16
  assign bfp_off = operand_b_i[20:16];
  assign bfp_mask = '0;

  // for (genvar i = 0; i < 32; i++) begin : gen_rev_bfp_mask
  //   assign bfp_mask_rev[i] = bfp_mask[31-i];
  // end
  assign bfp_mask_rev[0] = bfp_mask[31];
  assign bfp_mask_rev[1] = bfp_mask[30];
  assign bfp_mask_rev[2] = bfp_mask[29];
  assign bfp_mask_rev[3] = bfp_mask[28];
  assign bfp_mask_rev[4] = bfp_mask[27];
  assign bfp_mask_rev[5] = bfp_mask[26];
  assign bfp_mask_rev[6] = bfp_mask[25];
  assign bfp_mask_rev[7] = bfp_mask[24];
  assign bfp_mask_rev[8] = bfp_mask[23];
  assign bfp_mask_rev[9] = bfp_mask[22];
  assign bfp_mask_rev[10] = bfp_mask[21];
  assign bfp_mask_rev[11] = bfp_mask[20];
  assign bfp_mask_rev[12] = bfp_mask[19];
  assign bfp_mask_rev[13] = bfp_mask[18];
  assign bfp_mask_rev[14] = bfp_mask[17];
  assign bfp_mask_rev[15] = bfp_mask[16];
  assign bfp_mask_rev[16] = bfp_mask[15];
  assign bfp_mask_rev[17] = bfp_mask[14];
  assign bfp_mask_rev[18] = bfp_mask[13];
  assign bfp_mask_rev[19] = bfp_mask[12];
  assign bfp_mask_rev[20] = bfp_mask[11];
  assign bfp_mask_rev[21] = bfp_mask[10];
  assign bfp_mask_rev[22] = bfp_mask[9];
  assign bfp_mask_rev[23] = bfp_mask[8];
  assign bfp_mask_rev[24] = bfp_mask[7];
  assign bfp_mask_rev[25] = bfp_mask[6];
  assign bfp_mask_rev[26] = bfp_mask[5];
  assign bfp_mask_rev[27] = bfp_mask[4];
  assign bfp_mask_rev[28] = bfp_mask[3];
  assign bfp_mask_rev[29] = bfp_mask[2];
  assign bfp_mask_rev[30] = bfp_mask[1];
  assign bfp_mask_rev[31] = bfp_mask[0];

  assign bfp_result = '0;

  // bit shift_amt[5]: word swap bit: only considered for FSL/FSR.
  // if set, reverse operations in first and second cycle.
  assign shift_amt[5] = operand_b_i[5] & shift_funnel;
  assign shift_amt_compl = 32 - operand_b_i[4:0];

  always_comb begin
    if (bfp_op) begin
      shift_amt[4:0] = bfp_off;  // length field of bfp control word
    end else begin
      shift_amt[4:0] = instr_first_cycle_i ?
          (operand_b_i[5] && shift_funnel ? shift_amt_compl[4:0] : operand_b_i[4:0]) :
          (operand_b_i[5] && shift_funnel ? operand_b_i[4:0] : shift_amt_compl[4:0]);
    end
  end

  // single-bit mode: shift
  assign shift_sbmode = 1'b0;

  // left shift if this is:
  // * a standard left shift (slo, sll)
  // * a rol in the first cycle
  // * a ror in the second cycle
  // * fsl: without word-swap bit: first cycle, else: second cycle
  // * fsr: without word-swap bit: second cycle, else: first cycle
  // * a single-bit instruction: bclr, bset, binv (excluding bext)
  // * bfp: bfp_mask << bfp_off
  always_comb begin
    unique case (operator_i)
      7'd10: shift_left = 1'b1;
      7'd12: shift_left = 1'b0;
      7'd55: shift_left = 1'b0;
      7'd14: shift_left = 0;
      7'd13: shift_left = 0;
      7'd47: shift_left = 1'b0;
      7'd48: shift_left = 1'b0;
      default: shift_left = 1'b0;
    endcase
    if (shift_sbmode) begin
      shift_left = 1'b1;
    end
  end

  assign shift_arith  = (operator_i == 7'd8);
  assign shift_ones   = 1'b0;
  assign shift_funnel = 1'b0;

  // shifter structure.
  always_comb begin
    // select shifter input
    // for bfp, sbmode and shift_left the corresponding bit-reversed input is chosen.
    //if (RV32B == RV32BNone) begin
    shift_operand = shift_left ? operand_a_rev : operand_a_i;
    //end else begin
    //   unique case (1'b1)
    //     bfp_op:       shift_operand = bfp_mask_rev;
    //     shift_sbmode: shift_operand = 32'h8000_0000;
    //     default:      shift_operand = shift_left ? operand_a_rev : operand_a_i;
    //   endcase
    // end

    shift_result_ext_signed =
        $signed({shift_ones | (shift_arith & shift_operand[31]), shift_operand}) >>> shift_amt[4:0];
    shift_result_ext = $unsigned(shift_result_ext_signed);

    shift_result            = shift_result_ext[31:0];
    unused_shift_result_ext = shift_result_ext[32];

    // for (int unsigned i = 0; i < 32; i++) begin
    //   shift_result_rev[i] = shift_result[31-i];
    // end
    shift_result_rev[0] = shift_result[31];
    shift_result_rev[1] = shift_result[30];
    shift_result_rev[2] = shift_result[29];
    shift_result_rev[3] = shift_result[28];
    shift_result_rev[4] = shift_result[27];
    shift_result_rev[5] = shift_result[26];
    shift_result_rev[6] = shift_result[25];
    shift_result_rev[7] = shift_result[24];
    shift_result_rev[8] = shift_result[23];
    shift_result_rev[9] = shift_result[22];
    shift_result_rev[10] = shift_result[21];
    shift_result_rev[11] = shift_result[20];
    shift_result_rev[12] = shift_result[19];
    shift_result_rev[13] = shift_result[18];
    shift_result_rev[14] = shift_result[17];
    shift_result_rev[15] = shift_result[16];
    shift_result_rev[16] = shift_result[15];
    shift_result_rev[17] = shift_result[14];
    shift_result_rev[18] = shift_result[13];
    shift_result_rev[19] = shift_result[12];
    shift_result_rev[20] = shift_result[11];
    shift_result_rev[21] = shift_result[10];
    shift_result_rev[22] = shift_result[9];
    shift_result_rev[23] = shift_result[8];
    shift_result_rev[24] = shift_result[7];
    shift_result_rev[25] = shift_result[6];
    shift_result_rev[26] = shift_result[5];
    shift_result_rev[27] = shift_result[4];
    shift_result_rev[28] = shift_result[3];
    shift_result_rev[29] = shift_result[2];
    shift_result_rev[30] = shift_result[1];
    shift_result_rev[31] = shift_result[0];

    shift_result = shift_left ? shift_result_rev : shift_result;

  end

  ///////////////////
  // Bitwise Logic //
  ///////////////////

  logic bwlogic_or;
  logic bwlogic_and;
  logic [31:0] bwlogic_operand_b;
  logic [31:0] bwlogic_or_result;
  logic [31:0] bwlogic_and_result;
  logic [31:0] bwlogic_xor_result;
  logic [31:0] bwlogic_result;

  logic bwlogic_op_b_negate;

  always_comb begin
    unique case (operator_i)
      // Logic-with-negate OPs (RV32B Ops)
      7'd5,
      ALU_ORN,
      ALU_ANDN: bwlogic_op_b_negate = 1'b0;
      7'd46: bwlogic_op_b_negate = 1'b0;
      default:  bwlogic_op_b_negate = 1'b0;
    endcase
  end

  assign bwlogic_operand_b = bwlogic_op_b_negate ? operand_b_neg[32:1] : operand_b_i;

  assign bwlogic_or_result  = operand_a_i | bwlogic_operand_b;
  assign bwlogic_and_result = operand_a_i & bwlogic_operand_b;
  assign bwlogic_xor_result = operand_a_i ^ bwlogic_operand_b;

  assign bwlogic_or  = (operator_i == ALU_OR)  | (operator_i == ALU_ORN);
  assign bwlogic_and = (operator_i == ALU_AND) | (operator_i == ALU_ANDN);

  always_comb begin
    unique case (1'b1)
      bwlogic_or:  bwlogic_result = bwlogic_or_result;
      bwlogic_and: bwlogic_result = bwlogic_and_result;
      default:     bwlogic_result = bwlogic_xor_result;
    endcase
  end

  logic [5:0]  bitcnt_result;
  logic [31:0] minmax_result;
  logic [31:0] pack_result;
  logic [31:0] sext_result;
  logic [31:0] singlebit_result;
  logic [31:0] rev_result;
  logic [31:0] shuffle_result;
  logic [31:0] xperm_result;
  logic [31:0] butterfly_result;
  logic [31:0] invbutterfly_result;
  logic [31:0] clmul_result;
  logic [31:0] multicycle_result;

  // begin g_no_alu_rvb
  logic [31:0] unused_imd_val_q[2];
  assign unused_imd_val_q           = imd_val_q_i;
  logic [31:0] unused_butterfly_result;
  assign unused_butterfly_result    = butterfly_result;
  logic [31:0] unused_invbutterfly_result;
  assign unused_invbutterfly_result = invbutterfly_result;
  // RV32B result signals
  assign bitcnt_result       = '0;
  assign minmax_result       = '0;
  assign pack_result         = '0;
  assign sext_result         = '0;
  assign singlebit_result    = '0;
  assign rev_result          = '0;
  assign shuffle_result      = '0;
  assign xperm_result        = '0;
  assign butterfly_result    = '0;
  assign invbutterfly_result = '0;
  assign clmul_result        = '0;
  assign multicycle_result   = '0;
  // RV32B support signals
  assign imd_val_d_o         = '{default: '0};
  assign imd_val_we_o        = '{default: '0};
  // end g_no_alu_rvb

  ////////////////
  // Result mux //
  ////////////////

  always_comb begin
    result_o   = '0;

    unique case (operator_i)
      // Bitwise Logic Operations (negate: RV32B)
      7'd2,  7'd5,
      ALU_OR,   ALU_ORN,
      ALU_AND,  ALU_ANDN: result_o = bwlogic_result;

      // Adder Operations
      7'd0,  7'd1,
      // RV32B
      7'd22, 7'd23,
      7'd24: result_o = adder_result;

      // Shift Operations
      7'd10,  7'd9,
      7'd8,
      // RV32B
      7'd12,  7'd11: result_o = shift_result;

      // Shuffle Operations (RV32B)
      7'd17, 7'd18: result_o = shuffle_result;

      // Crossbar Permutation Operations (RV32B)
      7'd19, 7'd20, 7'd21: result_o = xperm_result;

      // Comparison Operations
      7'd29,   7'd30,
      7'd27,   7'd28,
      7'd25,   7'd26,
      7'd43,  7'd44: result_o = {31'h0,cmp_result};

      // MinMax Operations (RV32B)
      7'd31,  7'd33,
      7'd32, 7'd34: result_o = minmax_result;

      // Bitcount Operations (RV32B)
      7'd40, 7'd41,
      7'd42: result_o = {26'h0, bitcnt_result};

      // Pack Operations (RV32B)
      7'd35, 7'd37,
      7'd36: result_o = pack_result;

      // Sign-Extend (RV32B)
      7'd38, 7'd39: result_o = sext_result;

      // Ternary Bitmanip Operations (RV32B)
      7'd46, 7'd45,
      7'd47,  7'd48,
      // Rotate Shift (RV32B)
      7'd14, 7'd13,
      // Cyclic Redundancy Checks (RV32B)
      7'd63, 7'd64,
      7'd61, 7'd62,
      7'd59, 7'd60,
      // Bit Compress / Decompress (RV32B)
      7'd53, 7'd54: result_o = multicycle_result;

      // Single-Bit Bitmanip Operations (RV32B)
      7'd49, 7'd50,
      7'd51, 7'd52: result_o = singlebit_result;

      // General Reverse / Or-combine (RV32B)
      7'd15, 7'd16: result_o = rev_result;

      // Bit Field Place (RV32B)
      7'd55: result_o = bfp_result;

      // Carry-less Multiply Operations (RV32B)
      7'd56, 7'd57,
      7'd58: result_o = clmul_result;

      default: ;
    endcase
  end

  logic unused_shift_amt_compl;
  assign unused_shift_amt_compl = shift_amt_compl[5];

endmodule

// To check with slang:
// slang -y rtl rtl/ibex_alu.sv --top alu_tb
module alu_tb;
   logic [31:0] imd_val_q_i[2];

   logic [31:0] imd_val_d_o[2];
   logic [1:0]  imd_val_we_o;

   logic [31:0] adder_result_o;
   logic [33:0] adder_result_ext_o;

   logic [31:0] result_o;
   logic        comparison_result_o;
   logic        is_equal_result_o;

   ibex_alu ALU (.operator_i(7'd0),
                 .operand_a_i(32'd0),
                 .operand_b_i(32'd0),

                 .instr_first_cycle_i(1'b0),

                 .multdiv_operand_a_i(0),
                 .multdiv_operand_b_i(0),

                 .multdiv_sel_i(0),

                 .imd_val_q_i(imd_val_q_i),

                 .imd_val_d_o(imd_val_d_o),
                 .imd_val_we_o(imd_val_we_o),
                 .adder_result_o(adder_result_o),
                 .adder_result_ext_o(adder_result_ext_o),
                 .result_o(result_o),
                 .comparison_result_o(comparison_result_o),
                 .is_equal_result_o(is_equal_result_o)
                 );
endmodule // alu_tb
