(* ------------------------------------------------------------------------
   A few regression tests for ppc_stepLib
   ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib;
open ppc_stepLib;

val _ = new_theory "ppc_step_test";

(* add with regs only *)

val [th] = ppc_step_hex "7C221A14" (* add 1,2,3 *);

Theorem add_r1_r2_r3_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM s.PC = v2w [F; T; T; T; T; T; F; F] ⇒
  s.MEM (s.PC + 1w) = v2w [F; F; T; F; F; F; T; F] ⇒
  s.MEM (s.PC + 2w) = v2w [F; F; F; T; T; F; T; F] ⇒
  s.MEM (s.PC + 3w) = v2w [F; F; F; T; F; T; F; F] ⇒
  NextStatePPC s =
  SOME (s with <|PC := s.PC + 4w; REG := s.REG⦇1w ↦ s.REG 2w + s.REG 3w⦈|>)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th) \\ simp []
QED

(* addi with immediate *)

val [th] = ppc_step_hex "397f0020"; (* addi r11,r31,32 *)

Theorem add_r11_r31_32_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 2w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM (s.PC + 3w) = v2w [F; F; T; F; F; F; F; F] ⇒
  s.MEM (s.PC + 1w) = v2w [F; T; T; T; T; T; T; T] ⇒
  s.MEM s.PC = v2w [F; F; T; T; T; F; F; T] ⇒
  NextStatePPC s =
  SOME
  (s with <|PC := s.PC + 4w; REG := s.REG⦇11w ↦ s.REG 31w + 32w⦈|>)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th) \\ simp []
QED

(* nop instruction *)

val [th] = ppc_step_hex "60000000"; (* nop *)

Theorem nop_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 2w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM (s.PC + 3w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM (s.PC + 1w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM s.PC = v2w [F; T; T; F; F; F; F; F] ⇒
  NextStatePPC s = SOME (s with PC := s.PC + 4w)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th) \\ simp []
QED

(* mr instruction *)

val [th] = ppc_step_hex "7d234b78"; (* mr r3,r9 *)

Theorem mr_r3_r9_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 2w) = v2w [F; T; F; F; T; F; T; T] ⇒
  s.MEM (s.PC + 3w) = v2w [F; T; T; T; T; F; F; F] ⇒
  s.MEM (s.PC + 1w) = v2w [F; F; T; F; F; F; T; T] ⇒
  s.MEM s.PC = v2w [F; T; T; T; T; T; F; T] ⇒
  NextStatePPC s =
  SOME (s with <|PC := s.PC + 4w; REG := s.REG⦇3w ↦ s.REG 9w⦈|>)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th) \\ simp []
QED

(* b instruction *)

val [th] = ppc_step_hex "48000030"; (* b 90 <f+0x58> *)

Theorem b_90_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 3w) = v2w [F; F; T; T; F; F; F; F] ⇒
  s.MEM (s.PC + 2w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM (s.PC + 1w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM s.PC = v2w [F; T; F; F; T; F; F; F] ⇒
  NextStatePPC s = SOME (s with PC := s.PC + 48w)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th) \\ simp []
QED

(* bl instruction *)

val [th] = ppc_step_hex "48000001"; (* bl 78 <f+0x40> *)

Theorem bl_78_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 3w) = v2w [F; F; F; F; F; F; F; T] ⇒
  s.MEM (s.PC + 2w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM (s.PC + 1w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM s.PC = v2w [F; T; F; F; T; F; F; F] ⇒
  NextStatePPC s = SOME (s with <|PC := s.PC + 0w; LR := s.PC + 4w|>)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th) \\ simp [wordsTheory.WORD_ADD_0]
QED

(* blr instruction *)

val [th] = ppc_step_hex "4e800020"; (* blr *)

Theorem blr_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 3w) = v2w [F; F; T; F; F; F; F; F] ⇒
  s.MEM (s.PC + 2w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM (s.PC + 1w) = v2w [T; F; F; F; F; F; F; F] ⇒
  s.MEM s.PC = v2w [F; T; F; F; T; T; T; F] ⇒
  NextStatePPC s = SOME (s with PC := s.LR)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th) \\ simp [wordsTheory.WORD_ADD_0]
QED

(* bc instruction *)

val [th1,th2] = ppc_step_hex "4081ffcc"; (* ble 64 <f+0x2c> *)

Theorem ble_test1:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 3w) = v2w [T; T; F; F; T; T; F; F] ⇒
  s.MEM (s.PC + 2w) = v2w [T; T; T; T; T; T; T; T] ⇒
  s.MEM (s.PC + 1w) = v2w [T; F; F; F; F; F; F; T] ⇒
  s.MEM s.PC = v2w [F; T; F; F; F; F; F; F] ⇒
  ¬s.CR1 ⇒
  NextStatePPC s = SOME (s with PC := s.PC + 0xFFFFFFCCw)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th1) \\ simp []
QED

Theorem ble_test2:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 2w) = v2w [T; T; T; T; T; T; T; T] ⇒
  s.MEM (s.PC + 3w) = v2w [T; T; F; F; T; T; F; F] ⇒
  s.MEM (s.PC + 1w) = v2w [T; F; F; F; F; F; F; T] ⇒
  s.MEM s.PC = v2w [F; T; F; F; F; F; F; F] ⇒
  s.CR1 ⇒
  NextStatePPC s = SOME (s with PC := s.PC + 4w)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th2) \\ simp []
QED

val _ = export_theory ();
