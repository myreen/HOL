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

(* add immediate *)

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

(* load immediate *)

val [th] = ppc_step_hex "39200000"; (* li r9,0  same as addi r9,r0,0 *)

Theorem li_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 3w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM (s.PC + 2w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM (s.PC + 1w) = v2w [F; F; T; F; F; F; F; F] ⇒
  s.MEM s.PC = v2w [F; F; T; T; T; F; F; T] ⇒
  NextStatePPC s =
  SOME (s with <|PC := s.PC + 4w; REG := s.REG⦇9w ↦ 0w⦈|>)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th) \\ simp []
QED

(* cmpwi instruction *)

val [th] = ppc_step_hex "2c090063"; (* cmpwi r9,99 *)

Theorem cmpwi_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 2w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM (s.PC + 3w) = v2w [F; T; T; F; F; F; T; T] ⇒
  s.MEM (s.PC + 1w) = v2w [F; F; F; F; T; F; F; T] ⇒
  s.MEM s.PC = v2w [F; F; T; F; T; T; F; F] ⇒
  NextStatePPC s =
  SOME
  (s with
   <|CR0 := (s.REG 9w < 99w); CR1 := (s.REG 9w = 99w);
     CR2 := (s.REG 9w > 99w); PC := s.PC + 4w|>)
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

(* lwz instruction *)

val [th] = ppc_step_hex "815f000c"; (* lwz r10,12(r31) *)

Theorem lwz_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 2w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM (s.PC + 3w) = v2w [F; F; F; F; T; T; F; F] ⇒
  s.MEM (s.PC + 1w) = v2w [F; T; F; T; T; T; T; T] ⇒
  s.MEM s.PC = v2w [T; F; F; F; F; F; F; T] ⇒
  NextStatePPC s =
  SOME
  (s with
   REG :=
   s.REG⦇
    10w ↦
    w2w (s.MEM (s.REG 31w + 12w + 0w)) ≪ 24 ‖
    w2w (s.MEM (s.REG 31w + 12w + 1w)) ≪ 16 ‖
    w2w (s.MEM (s.REG 31w + 12w + 2w)) ≪ 8 ‖
    w2w (s.MEM (s.REG 31w + 12w + 3w))
    ⦈)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th) \\ simp []
QED

(* stw instruction *)

val [th] = ppc_step_hex "913f001c"; (* stw r9,28(r31) *)

Theorem stw_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 2w) = v2w [F; F; F; F; F; F; F; F] ⇒
  s.MEM (s.PC + 3w) = v2w [F; F; F; T; T; T; F; F] ⇒
  s.MEM (s.PC + 1w) = v2w [F; F; T; T; T; T; T; T] ⇒
  s.MEM s.PC = v2w [T; F; F; T; F; F; F; T] ⇒
  NextStatePPC s =
  SOME
  (s with
   MEM :=
   s.MEM⦇
    28w + s.REG 31w ↦ w2w (s.REG 9w ⋙ 24);
    28w + s.REG 31w + 1w ↦ w2w (s.REG 9w ⋙ 16);
    28w + s.REG 31w + 2w ↦ w2w (s.REG 9w ⋙ 8);
    28w + s.REG 31w + 3w ↦ w2w (s.REG 9w)
    ⦈)
Proof
  rpt strip_tac \\ irule (DISCH_ALL th) \\ simp []
QED

(* stwu instruction *)

val [th] = ppc_step_hex "9421ffe0"; (* stwu r1,-32(r1) *)

Theorem stwu_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 2w) = v2w [T; T; T; T; T; T; T; T] ⇒
  s.MEM (s.PC + 3w) = v2w [T; T; T; F; F; F; F; F] ⇒
  s.MEM (s.PC + 1w) = v2w [F; F; T; F; F; F; F; T] ⇒
  s.MEM s.PC = v2w [T; F; F; T; F; T; F; F] ⇒
  NextStatePPC s =
  SOME
  (s with
   <|MEM :=
     s.MEM⦇
      0xFFFFFFE0w + s.REG 1w ↦ w2w (s.REG 1w ⋙ 24);
      0xFFFFFFE0w + s.REG 1w + 1w ↦ w2w (s.REG 1w ⋙ 16);
      0xFFFFFFE0w + s.REG 1w + 2w ↦ w2w (s.REG 1w ⋙ 8);
      0xFFFFFFE0w + s.REG 1w + 3w ↦ w2w (s.REG 1w)
      ⦈; REG := s.REG⦇1w ↦ 0xFFFFFFE0w + s.REG 1w⦈|>)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th) \\ simp []
QED

(* mflr instruction *)

val [th] = ppc_step_hex "7c0802a6"; (* mflr r0 *)

Theorem mflr_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 2w) = v2w [F; F; F; F; F; F; T; F] ⇒
  s.MEM (s.PC + 3w) = v2w [T; F; T; F; F; T; T; F] ⇒
  s.MEM (s.PC + 1w) = v2w [F; F; F; F; T; F; F; F] ⇒
  s.MEM s.PC = v2w [F; T; T; T; T; T; F; F] ⇒
  NextStatePPC s =
  SOME (s with <|PC := s.PC + 4w; REG := s.REG⦇0w ↦ s.LR⦈|>)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th) \\ simp []
QED

(* mtlr instruction *)

val [th] = ppc_step_hex "7c0803a6"; (* mtlr r0 *)

Theorem mtlr_test:
  aligned 2 s.PC ⇒
  s.exception = NoException ⇒
  s.MEM (s.PC + 2w) = v2w [F; F; F; F; F; F; T; T] ⇒
  s.MEM (s.PC + 3w) = v2w [T; F; T; F; F; T; T; F] ⇒
  s.MEM (s.PC + 1w) = v2w [F; F; F; F; T; F; F; F] ⇒
  s.MEM s.PC = v2w [F; T; T; T; T; T; F; F] ⇒
  NextStatePPC s = SOME (s with <|LR := s.REG 0w; PC := s.PC + 4w|>)
Proof
  rpt strip_tac \\ drule_all (DISCH_ALL th) \\ simp []
QED

val _ = export_theory ();
