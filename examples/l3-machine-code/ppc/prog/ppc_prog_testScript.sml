
open HolKernel Parse boolLib bossLib;
open ppc_progLib set_sepTheory;

val _ = new_theory "ppc_prog_test";

val _ = Parse.hide "mem";

val [th] = ppc_spec_hex "60000000"; (* nop *)

Theorem nop_test:
  SPEC PPC_MODEL
    (ppc_pc pc)
    {(pc,0x60000000w)}
    (ppc_pc (pc + 4w))
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "397f0020"; (* addi r11,r31,32 *)

Theorem addi_test:
  SPEC PPC_MODEL
    (ppc_REG 31w r31 * ppc_REG 11w r11 * ppc_pc pc)
    {(pc,0x397F0020w)}
    (ppc_REG 31w r31 * ppc_REG 11w (r31 + 32w) * ppc_pc (pc + 4w))
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "39200000"; (* li r9,0  same as addi r9,r0,0 *)

Theorem li_test:
  SPEC PPC_MODEL
    (ppc_REG 9w r9 * ppc_pc pc)
    {(pc,0x39200000w)}
    (ppc_REG 9w 0w * ppc_pc (pc + 4w))
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "7d234b78"; (* mr r3,r9 *)

Theorem mr_test:
  SPEC PPC_MODEL
    (ppc_REG 3w r3 * ppc_REG 9w r9 * ppc_pc pc)
    {(pc,0x7D234B78w)}
    (ppc_REG 3w r9 * ppc_REG 9w r9 * ppc_pc (pc + 4w))
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "48000030"; (* b 90 <f+0x58> *)

Theorem b_test:
  SPEC PPC_MODEL
    (ppc_pc pc)
    {(pc,0x48000030w)}
    (ppc_pc (pc + 48w))
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "4e800020"; (* blr *)

Theorem blr_test:
  SPEC PPC_MODEL
    (ppc_LR lr * ppc_pc pc * cond (aligned 2 pc ⇒ aligned 2 lr))
    {(pc,0x4E800020w)}
    (ppc_LR lr * ppc_pc lr)
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "7c0802a6"; (* mflr r0 *)

Theorem mflr_test:
  SPEC PPC_MODEL
    (ppc_LR lr * ppc_REG 0w r0 * ppc_pc pc)
    {(pc,0x7C0802A6w)}
    (ppc_LR lr * ppc_REG 0w lr * ppc_pc (pc + 4w))
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "5529073e"; (* clrlwi r9,r9,28 same as rlwinm r9, r9, 0, 28, 31 *)

Theorem clrlwi_test:
  SPEC PPC_MODEL
    (ppc_REG 9w r9 * ppc_pc pc)
    {(pc,0x5529073Ew)}
    (ppc_REG 9w (r9 && 15w) * ppc_pc (pc + 4w))
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "2c090063"; (* cmpwi r9,99 *)

Theorem cmpwi_test:
  SPEC PPC_MODEL
    (ppc_CR2 cr2 * ppc_CR1 cr1 * ppc_CR0 cr0 * ppc_REG 9w r9 * ppc_pc pc)
    {(pc,0x2C090063w)}
    (ppc_CR2 (r9 = 99w) * ppc_CR1 (r9 > 99w) * ppc_CR0 (r9 < 99w) *
     ppc_REG 9w r9 * ppc_pc (pc + 4w))
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "48000001"; (* bl 78 <f+0x40> *)

Theorem bl_test:
  SPEC PPC_MODEL
    (ppc_LR lr * ppc_pc pc * cond (aligned 2 pc ⇒ aligned 2 (pc + 0w)))
    {(pc,0x48000001w)}
    (ppc_LR (pc + 4w) * ppc_pc (pc + 0w))
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "7c0803a6"; (* mtlr r0 *)

Theorem mtlr_test:
  SPEC PPC_MODEL
    (ppc_LR lr * ppc_REG 0w r0 * ppc_pc pc)
    {(pc,0x7C0803A6w)}
    (ppc_LR r0 * ppc_REG 0w r0 * ppc_pc (pc + 4w))
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "815f000c"; (* lwz r10,12(r31) *)

Theorem lwz_test:
  SPEC PPC_MODEL
    (ppc_REG 31w r31 * ppc_REG 10w r10 * ppc_pc pc * ppc_MEMORY dmem mem *
     cond
     (r31 + 12w + 0w ∈ dmem ∧ r31 + 12w + 1w ∈ dmem ∧
      r31 + 12w + 3w ∈ dmem ∧ r31 + 12w + 2w ∈ dmem)) {(pc,0x815F000Cw)}
    (ppc_REG 31w r31 * ppc_MEMORY dmem mem *
     ppc_REG 10w
      (w2w (mem (r31 + 12w + 0w)) ≪ 24 ‖
       w2w (mem (r31 + 12w + 1w)) ≪ 16 ‖ w2w (mem (r31 + 12w + 2w)) ≪ 8 ‖
       w2w (mem (r31 + 12w + 3w))) * ppc_pc (pc + 4w))
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "913f001c"; (* stw r9,28(r31) *)

Theorem stw_test:
  SPEC PPC_MODEL
    (ppc_REG 31w r31 * ppc_REG 9w r9 * ppc_pc pc * ppc_MEMORY dmem mem *
     cond
     (28w + r31 ∈ dmem ∧ 28w + r31 + 1w ∈ dmem ∧ 28w + r31 + 3w ∈ dmem ∧
      28w + r31 + 2w ∈ dmem)) {(pc,0x913F001Cw)}
    (ppc_REG 31w r31 * ppc_REG 9w r9 * ppc_pc (pc + 4w) *
     ppc_MEMORY dmem
       mem⦇
         28w + r31 ↦ w2w (r9 ⋙ 24);
         28w + r31 + 1w ↦ w2w (r9 ⋙ 16);
         28w + r31 + 2w ↦ w2w (r9 ⋙ 8);
         28w + r31 + 3w ↦ w2w r9
       ⦈)
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th] = ppc_spec_hex "9421ffe0"; (* stwu r1,-32(r1) *)

Theorem stwu_test:
  SPEC PPC_MODEL
    (ppc_REG 1w r1 * ppc_pc pc * ppc_MEMORY dmem mem *
     cond
     (0xFFFFFFE0w + r1 ∈ dmem ∧ 0xFFFFFFE0w + r1 + 1w ∈ dmem ∧
      0xFFFFFFE0w + r1 + 3w ∈ dmem ∧ 0xFFFFFFE0w + r1 + 2w ∈ dmem))
    {(pc,0x9421FFE0w)}
    (ppc_REG 1w (0xFFFFFFE0w + r1) * ppc_pc (pc + 4w) *
     ppc_MEMORY dmem
       mem⦇
         0xFFFFFFE0w + r1 ↦ w2w (r1 ⋙ 24);
         0xFFFFFFE0w + r1 + 1w ↦ w2w (r1 ⋙ 16);
         0xFFFFFFE0w + r1 + 2w ↦ w2w (r1 ⋙ 8);
         0xFFFFFFE0w + r1 + 3w ↦ w2w r1
       ⦈)
Proof
  assume_tac th \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val [th1,th2] = ppc_spec_hex "4081ffcc"; (* ble 64 <f+0x2c> *)

Theorem ble_test:
  SPEC PPC_MODEL
    (ppc_pc pc * ppc_CR1 cr1 * cond (¬cr1))
    {(pc,0x4081FFCCw)}
    (ppc_pc (pc + 0xFFFFFFCCw) * ppc_CR1 cr1) ∧
  SPEC PPC_MODEL
    (ppc_pc pc * ppc_CR1 cr1 * cond cr1)
    {(pc,0x4081FFCCw)}
    (ppc_pc (pc + 4w) * ppc_CR1 cr1)
Proof
  assume_tac th1 \\ assume_tac th2 \\ fs [AC STAR_COMM STAR_ASSOC]
QED

val _ = export_theory();
