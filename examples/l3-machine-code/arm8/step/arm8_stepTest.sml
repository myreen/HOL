(* ------------------------------------------------------------------------
   Tests for FP extensions to the ARMv8 step evaluator
   ------------------------------------------------------------------------ *)
(*

Test cases and results run on Apple Silicon:

FADD: -12.0 + -2.0:
	result = 0xc02c000000000000 (-14.00)
FSUB: -12.0 - -2.0:
	result = 0xc024000000000000 (-10.00)
FMUL: -12.0 * -2.0:
	result = 0x4038000000000000 (24.00)
FMADD: -12.0 * -2.0 + 3.0:
	result = 0x403b000000000000 (27.00)
FCMPE: -12.0, 10.0:
	result = 0x0000000080000000 (NZCV = 1000)
FCMPE: 10.0, -12.0:
	result = 0x0000000020000000 (NZCV = 0010)
FCMPE: 10.0, 10.0:
	result = 0x0000000060000000 (NZCV = 0110)
FCMPE: #FFFFFFFFFFFFFFFF, 10.0:
	result = 0x0000000030000000 (NZCV = 0011)
FCMPE: 10.0, #FFFFFFFFFFFFFFFF:
	result = 0x0000000030000000 (NZCV = 0011)
LDR: 24.0:
	result = 0x4038000000000000 (24.00)
STR: 15.0:
	result = 0x402e000000000000 (15.00)
FMOV (register): 24.0:
	result = 0x4038000000000000 (24.00)
FMOV (immediate): 25.0:
	result = 0x4039000000000000 (25.00)

Operands used:
	-12.00 = 0xc028000000000000 = 13846317054350589952
	 -2.00 = 0xc000000000000000 = 13835058055282163712
	  3.00 = 0x4008000000000000 = 4613937818241073152
	 10.00 = 0x4024000000000000 = 4621819117588971520
	 24.00 = 0x4038000000000000 = 4627448617123184640
	 25.00 = 0x4039000000000000 = 4627730092099895296

Results:
	-14.00 = 0xc02c000000000000 = 13847442954257432576
	-10.00 = 0xc024000000000000 = 13845191154443747328
	 15.00 = 0x402e000000000000 = 4624633867356078080
	 24.00 = 0x4038000000000000 = 4627448617123184640
	 25.00 = 0x4039000000000000 = 4627730092099895296
	 27.00 = 0x403b000000000000 = 4628293042053316608

*)

load "arm8_stepTheory";

use "arm8_stepLib.sig";
use "arm8_stepLib.sml";

open arm8_stepLib;
open arm8Theory;
open binary_ieeeTheory;
open machine_ieeeTheory;
load "binary_ieeeLib";
open binary_ieeeLib;

val s = "1e612800"; val th = arm8_step_hex s |> hd (* fadd	d0, d0, d1 *);

val float_add = th
  |> DISCH “s.FPREG 0w = 0xC028000000000000w”
  |> DISCH “s.FPREG 1w = 0xC000000000000000w”
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPAdd64_def,RoundingMode_def] THENC RAND_CONV EVAL)
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPAdd64_def,RoundingMode_def] THENC RAND_CONV EVAL THENC REWRITE_CONV [float_to_fp64_def] THENC RAND_CONV EVAL);

val s = "1e613800"; val th = arm8_step_hex s |> hd (* fsub	d0, d0, d1 *);

val float_sub = th
  |> DISCH “s.FPREG 0w = 0xC028000000000000w”
  |> DISCH “s.FPREG 1w = 0xC000000000000000w”
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPSub64_def,RoundingMode_def] THENC RAND_CONV EVAL)
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPSub64_def,RoundingMode_def] THENC RAND_CONV EVAL THENC REWRITE_CONV [float_to_fp64_def] THENC RAND_CONV EVAL);


val s = "1e610800"; val th = arm8_step_hex s |> hd (* fmul	d0, d0, d1 *);


val float_mul = th
  |> DISCH “s.FPREG 0w = 0xC028000000000000w”
  |> DISCH “s.FPREG 1w = 0xC000000000000000w”
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPMul64_def,RoundingMode_def] THENC RAND_CONV EVAL)
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPMul64_def,RoundingMode_def] THENC RAND_CONV EVAL THENC REWRITE_CONV [float_to_fp64_def] THENC RAND_CONV EVAL);

val s = "1f410800"; val th = arm8_step_hex s |> hd (* fmadd    d0, d0, d1, d2 *);

val float_madd = th
  |> DISCH “s.FPREG 0w = 0xC028000000000000w”
  |> DISCH “s.FPREG 1w = 0xC000000000000000w”
  |> DISCH “s.FPREG 2w = 0x4008000000000000w”
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPMul64_def, FPAdd64_def, RoundingMode_def] THENC RAND_CONV EVAL)
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPMul64_def, FPAdd64_def,RoundingMode_def] THENC RAND_CONV EVAL THENC REWRITE_CONV [float_to_fp64_def] THENC RAND_CONV EVAL);

val s = "1e602030"; val th = arm8_step_hex s |> hd (* fcmpe	d1, d0 *);

val float_m12_compare_10 = th
  |> DISCH “s.FPREG 1w = 0xC028000000000000w”
  |> DISCH “s.FPREG 0w = 0x4024000000000000w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPCompare64_def, RoundingMode_def] THENC RAND_CONV EVAL)
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPCompare64_def,RoundingMode_def] THENC RAND_CONV EVAL THENC REWRITE_CONV [float_to_fp64_def] THENC RAND_CONV EVAL);

val float_10_compare_m12 = th
  |> DISCH “s.FPREG 0w = 0xC028000000000000w”
  |> DISCH “s.FPREG 1w = 0x4024000000000000w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPCompare64_def, RoundingMode_def] THENC RAND_CONV EVAL)
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPCompare64_def,RoundingMode_def] THENC RAND_CONV EVAL THENC REWRITE_CONV [float_to_fp64_def] THENC RAND_CONV EVAL);

val float_10_compare_10 = th
  |> DISCH “s.FPREG 0w = 0x4024000000000000w”
  |> DISCH “s.FPREG 1w = 0x4024000000000000w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPCompare64_def, RoundingMode_def] THENC RAND_CONV EVAL)
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPCompare64_def,RoundingMode_def] THENC RAND_CONV EVAL THENC REWRITE_CONV [float_to_fp64_def] THENC RAND_CONV EVAL);

val float_nan_compare_10 = th
  |> DISCH “s.FPREG 0w = 0x4024000000000000w”
  |> DISCH “s.FPREG 1w = 0xFFFFFFFFFFFFFFFFw”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPCompare64_def, RoundingMode_def] THENC RAND_CONV EVAL)
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPCompare64_def,RoundingMode_def] THENC RAND_CONV EVAL THENC REWRITE_CONV [float_to_fp64_def] THENC RAND_CONV EVAL);

val float_10_compare_nan = th
  |> DISCH “s.FPREG 1w = 0x4024000000000000w”
  |> DISCH “s.FPREG 0w = 0xFFFFFFFFFFFFFFFFw”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPCompare64_def, RoundingMode_def] THENC RAND_CONV EVAL)
  |> DISCH “s.FPCR.RMode = 0w”
  |> SIMP_RULE bool_ss []
  |> UNDISCH_ALL
  |> CONV_RULE (REWRITE_CONV [FPCompare64_def,RoundingMode_def] THENC RAND_CONV EVAL THENC REWRITE_CONV [float_to_fp64_def] THENC RAND_CONV EVAL);


(* TODO: FMOV, STR and LDR *)

(*

Paul Whittakers list of FP instructions:

val s = "1e610800"; arm8_step_hex s (* fmul	d0, d0, d1 *);
val s = "1f410800"; arm8_step_hex s (* fmadd    d0, d0, d1, d2 *);
val s = "1e651001"; arm8_step_hex s (* fmov	d1, #1.200000000000000000e+01 *);
val s = "1e612800"; arm8_step_hex s (* fadd	d0, d0, d1 *);
val s = "1e611800"; arm8_step_hex s (* fdiv	d0, d0, d1 *);
val s = "1e613800"; arm8_step_hex s (* fsub	d0, d0, d1 *);
val s = "fd0007e0"; arm8_step_hex s (* str	d0, [sp, #8] *);
val s = "fd0003e1"; arm8_step_hex s (* str	d1, [sp] *);
val s = "fd4007e1"; arm8_step_hex s (* ldr	d1, [sp, #8] *);
val s = "fd4003e0"; arm8_step_hex s (* ldr	d0, [sp] *);
val s = "1e602030"; arm8_step_hex s (* fcmpe	d1, d0 *);
val s = "fd4007e1"; arm8_step_hex s (* ldr	d1, [sp, #8] *);
val s = "fd4003e0"; arm8_step_hex s (* ldr	d0, [sp] *);
val s = "1e603820"; arm8_step_hex s (* fsub	d0, d1, d0 *);
val s = "fd0017e0"; arm8_step_hex s (* str	d0, [sp, #40] *);
val s = "fd4017e0"; arm8_step_hex s (* ldr	d0, [sp, #40] *);
val s = "9e670001"; arm8_step_hex s (* fmov	d1, x0 *);
val s = "1e612800"; arm8_step_hex s (* fadd	d0, d0, d1 *);
val s = "fd001be0"; arm8_step_hex s (* str	d0, [sp, #48] *);
val s = "fd4017e0"; arm8_step_hex s (* ldr	d0, [sp, #40] *);
val s = "fd0013e0"; arm8_step_hex s (* str	d0, [sp, #32] *);
val s = "fd401be0"; arm8_step_hex s (* ldr	d0, [sp, #48] *);
val s = "fd0013e0"; arm8_step_hex s (* str	d0, [sp, #32] *);
val s = "fd4013e0"; arm8_step_hex s (* ldr	d0, [sp, #32] *);
val s = "fd001fe0"; arm8_step_hex s (* str	d0, [sp, #56] *);
val s = "fd401fe0"; arm8_step_hex s (* ldr	d0, [sp, #56] *);

*)
