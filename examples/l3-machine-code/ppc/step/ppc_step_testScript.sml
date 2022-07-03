(* ------------------------------------------------------------------------
   A few regression tests for ppc_stepLib
   ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib;
open ppc_stepLib;

val _ = new_theory "ppc_step_test";

val [th] = ppc_step_hex "7C221A14" (* add 1,2,3 *);

Theorem add_123_test:
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

val _ = export_theory ();
