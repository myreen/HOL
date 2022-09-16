open HolKernel boolLib bossLib
open blastLib stateLib
open set_sepTheory progTheory temporal_stateTheory ppc_stepTheory

val () = new_theory "ppc_prog"
val _ = ParseExtras.temp_loose_equality()

(* ------------------------------------------------------------------------ *)

val _ =
   stateLib.sep_definitions "ppc" [] [["undefined"]]
      ppc_stepTheory.NextStatePPC_def

val ppc_instr_def = Define`
   ppc_instr (a, i: word32) =
   { (ppc_c_MEM a,        ppc_d_word8 ((31 >< 24) i));
     (ppc_c_MEM (a + 1w), ppc_d_word8 ((23 >< 16) i));
     (ppc_c_MEM (a + 2w), ppc_d_word8 ((15 ><  8) i));
     (ppc_c_MEM (a + 3w), ppc_d_word8 ((7  ><  0) i)) }`

val PPC_MODEL_def = Define`
   PPC_MODEL =
   (STATE ppc_proj, NEXT_REL (=) NextStatePPC, ppc_instr,
    ($= :ppc_state -> ppc_state -> bool), (K F: ppc_state -> bool))`

val PPC_IMP_SPEC = Theory.save_thm ("PPC_IMP_SPEC",
   stateTheory.IMP_SPEC
   |> Q.ISPECL [`ppc_proj`, `NextStatePPC`, `ppc_instr`]
   |> REWRITE_RULE [GSYM PPC_MODEL_def]
   )

val PPC_IMP_TEMPORAL = Theory.save_thm ("PPC_IMP_TEMPORAL",
   temporal_stateTheory.IMP_TEMPORAL
   |> Q.ISPECL [`ppc_proj`, `NextStatePPC`, `ppc_instr`,
                `(=): ppc_state -> ppc_state -> bool`,
                `K F: ppc_state -> bool`]
   |> REWRITE_RULE [GSYM PPC_MODEL_def]
   )

(* ------------------------------------------------------------------------ *)

(* Aliases *)

val ppc_REG_def = DB.definition "ppc_REG_def"
val ppc_MEM_def = DB.definition "ppc_MEM_def"

val (ppc_REGISTERS_def, ppc_REGISTERS_INSERT) =
   stateLib.define_map_component ("ppc_REGISTERS", "reg", ppc_REG_def)

val (ppc_MEMORY_def, ppc_MEMORY_INSERT) =
   stateLib.define_map_component ("ppc_MEMORY", "mem", ppc_MEM_def)

val ppc_WORD_def = Define`
   ppc_WORD a (i: word32) =
   ppc_MEM a        ((31 >< 24) i) *
   ppc_MEM (a + 1w) ((23 >< 16) i) *
   ppc_MEM (a + 2w) ((15 ><  8) i) *
   ppc_MEM (a + 3w) ((7  ><  0) i)`;

val ppc_WORD_MEMORY_def = Define`
  ppc_WORD_MEMORY dmem mem =
  {BIGUNION { BIGUNION (ppc_WORD a (mem a)) | a IN dmem /\ aligned 2 a}}`

val ppc_pc_def = Define`
   ppc_pc pc =
   ppc_PC pc * ppc_exception NoException * set_sep$cond (aligned 2 pc)`;

val pS_def = Define `
   pS (c0,c1,c2) =
   ppc_CR0 c0 * ppc_CR1 c1 * ppc_CR2 c2`;

(* ------------------------------------------------------------------------ *)

val pS_HIDE = Q.store_thm("pS_HIDE",
   `~pS = ~ppc_CR0 * ~ppc_CR1 * ~ppc_CR2`,
   SIMP_TAC std_ss [SEP_HIDE_def, pS_def, SEP_CLAUSES, FUN_EQ_THM]
   \\ SIMP_TAC std_ss [SEP_EXISTS]
   \\ METIS_TAC [pS_def, pairTheory.PAIR]
   )

(* ------------------------------------------------------------------------ *)

val ppc_PC_INTRO = Q.store_thm("ppc_PC_INTRO",
   `SPEC m (p1 * ppc_pc pc) code
       (p2 * ppc_PC pc' * ppc_exception NoException) ==>
    (aligned 2 pc ==> aligned 2 pc') ==>
    SPEC m (p1 * ppc_pc pc) code (p2 * ppc_pc pc')`,
   REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC std_ss
        [ppc_pc_def, SPEC_MOVE_COND, STAR_ASSOC, SEP_CLAUSES]
   )

val ppc_TEMPORAL_PC_INTRO = Q.store_thm("ppc_TEMPORAL_PC_INTRO",
   `TEMPORAL_NEXT m (p1 * ppc_pc pc) code
       (p2 * ppc_PC pc' * ppc_exception NoException) ==>
    (aligned 2 pc ==> aligned 2 pc') ==>
    TEMPORAL_NEXT m (p1 * ppc_pc pc) code (p2 * ppc_pc pc')`,
   REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC std_ss
         [ppc_pc_def, TEMPORAL_NEXT_MOVE_COND, STAR_ASSOC, SEP_CLAUSES]
   )

(* ------------------------------------------------------------------------ *)

val () = export_theory()
