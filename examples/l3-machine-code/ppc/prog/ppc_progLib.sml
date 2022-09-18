structure ppc_progLib :> ppc_progLib =
struct

open HolKernel boolLib bossLib
open stateLib spec_databaseLib ppc_progTheory

structure Parse =
struct
   open Parse
   val (Type, Term) = parse_from_grammars ppc_progTheory.ppc_prog_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "ppc_progLib";

(* ------------------------------------------------------------------------ *)

val ppc_proj_def = ppc_progTheory.ppc_proj_def
val ppc_comp_defs = ppc_progTheory.component_defs

val step_1 = HolKernel.syntax_fns1 "ppc_step"
fun syn n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "ppc_prog"
val ppc_1 = syn 2 HolKernel.dest_monop HolKernel.mk_monop
val ppc_2 = syn 3 HolKernel.dest_binop HolKernel.mk_binop
val word5 = wordsSyntax.mk_int_word_type 5
val word = wordsSyntax.mk_int_word_type 32
val (_, _, dest_ppc_instr, _) = ppc_1 "ppc_instr"
val (_, mk_ppc_PC, dest_ppc_PC, is_ppc_PC) = ppc_1 "ppc_PC"
val (_, mk_ppc_CR0, dest_ppc_CR0, is_ppc_CR0) = ppc_1 "ppc_CR0"
val (_, mk_ppc_CR1, dest_ppc_CR1, is_ppc_CR1) = ppc_1 "ppc_CR1"
val (_, mk_ppc_CR2, dest_ppc_CR2, is_ppc_CR2) = ppc_1 "ppc_CR2"
val (_, mk_ppc_LR, dest_ppc_LR, is_ppc_LR) = ppc_1 "ppc_LR"
val (_, _, dest_ppc_MEM, is_ppc_MEM) = ppc_2 "ppc_MEM"
val (_, mk_ppc_REG, dest_ppc_REG, is_ppc_REG) = ppc_2 "ppc_REG"

val ppc_select_state_thms =
   List.map (fn t => stateLib.star_select_state_thm ppc_proj_def [] ([], t))
            ppc_comp_defs

val ppc_select_state_pool_thm =
   pool_select_state_thm ppc_proj_def []
      (utilsLib.SRW_CONV
         [pred_setTheory.INSERT_UNION_EQ, stateTheory.CODE_POOL, ppc_instr_def]
         ``CODE_POOL ppc_instr {(pc, opc)}``)

val state_id =
   utilsLib.mk_state_id_thm ppcTheory.ppc_state_component_equality
      [
       ["MEM", "PC"],
       ["MEM", "PC", "REG", "branch_hint"],
       ["MEM", "PC", "branch_hint"],
       ["REG", "CR0", "branch_hint"],
       ["REG", "branch_hint"]
      ]

val ppc_frame =
   stateLib.update_frame_state_thm ppc_proj_def
      ["PC", "REG", "MEM", "CR0", "CR1", "CR2", "LR", "CTR"]

(* -- *)

local
  val memnm =
      "ppc$" ^ TypeBasePure.mk_recordtype_fieldsel
                  {tyname="ppc_state",fieldname="MEM"}
   val ppc_instr_tm =
      Term.prim_mk_const {Thy = "ppc_prog", Name = "ppc_instr"}
   fun is_mem_access v tm =
      case Lib.total boolSyntax.dest_eq tm of
         SOME (l, r) =>
            stateLib.is_code_access (memnm, v) l andalso
            (wordsSyntax.is_word_literal r orelse bitstringSyntax.is_v2w r)
       | NONE => false
   val dest_opc = fst o listSyntax.dest_list o fst o bitstringSyntax.dest_v2w
   val ty32 = fcpSyntax.mk_int_numeric_type 32
   fun list_mk_concat l =
      bitstringSyntax.mk_v2w
         (listSyntax.mk_list
            (List.concat (List.map dest_opc l), Type.bool), ty32)
in
   fun mk_ppc_code_pool thm =
      let
         val r15 = stateLib.gvar "pc" word
         val r15_a = mk_ppc_PC r15
         val (a, tm) = Thm.dest_thm thm
         val r15_subst = Term.subst [``s.PC`` |-> r15]
         val a = List.map r15_subst a
         val (m, a) = List.partition (is_mem_access r15) a
         val m = List.map dest_code_access m
         val m = mlibUseful.sort_map fst Int.compare m
         val opc = list_mk_concat (List.map snd m) (* used to have List.rev *)
      in
         (r15_a,
          boolSyntax.rand (stateLib.mk_code_pool (ppc_instr_tm, r15, opc)),
          list_mk_imp (a, r15_subst tm))
      end
end

(* -- *)

fun reg_index tm = Lib.with_exn wordsSyntax.uint_of_word tm (ERR "reg_index" "")

local
   fun other_index tm =
      case fst (Term.dest_const (boolSyntax.rator tm)) of
         "cond" => 0
       | "ppc_PC" => 1
       | "ppc_exception" => 2
       | _ => ~1
   val total_dest_lit = Lib.total wordsSyntax.dest_word_literal
   fun word_compare (w1, w2) =
      case (total_dest_lit w1, total_dest_lit w2) of
         (SOME x1, SOME x2) => Arbnum.compare (x1, x2)
       | (SOME _, NONE) => General.GREATER
       | (NONE, SOME _) => General.LESS
       | (NONE, NONE) => Term.compare (w1, w2)
   val register = fst o dest_ppc_REG
   val address = HolKernel.strip_binop wordsSyntax.dest_word_add o
                 fst o dest_ppc_MEM
in
   fun psort p =
      let
         val (m, rst) = List.partition is_ppc_MEM p
         val (r, rst) = List.partition is_ppc_REG rst
      in
         mlibUseful.sort_map other_index Int.compare rst @
         mlibUseful.sort_map register Term.compare r @
         mlibUseful.sort_map address (mlibUseful.lex_list_order word_compare) m
      end
end

local
  fun fupnm ty f =
      "ppc$" ^ TypeBasePure.mk_recordtype_fieldfupd{tyname=ty,fieldname=f}
   val st = Term.mk_var ("s", ``:ppc_state``)
in
   val ppc_write_footprint =
      stateLib.write_footprint ppc_1 ppc_2
        [(fupnm "ppc_state" "MEM", "ppc_MEM", ``^st.MEM``),
         (fupnm "ppc_state" "REG", "ppc_REG", ``^st.REG``)]
        [(fupnm "ppc_state" "PC",  "ppc_PC"),
         (fupnm "ppc_state" "CR0", "ppc_CR0"),
         (fupnm "ppc_state" "CR1", "ppc_CR1"),
         (fupnm "ppc_state" "CR2", "ppc_CR2"),
         (fupnm "ppc_state" "LR",  "ppc_LR")]
        [] []
        (K false)
end

local
   val model_def = ppc_progTheory.PPC_MODEL_def
   val comp_defs = ppc_comp_defs
   val cpool = mk_ppc_code_pool
   val extras = [] : footprint_extra list
   val write_fn = ppc_write_footprint
in
   val ppc_mk_pre_post =
      stateLib.mk_pre_post model_def comp_defs cpool extras write_fn psort
end

(* ------------------------------------------------------------------------ *)

local
   val ppc_rmap =
      Lib.total
        (fn "ppc_prog$ppc_PSTATE_N" => K "n"
          | "ppc_prog$ppc_PSTATE_Z" => K "z"
          | "ppc_prog$ppc_PSTATE_C" => K "c"
          | "ppc_prog$ppc_PSTATE_V" => K "v"
          | "ppc_prog$ppc_SP_EL0" => K "sp"
          | "ppc_prog$ppc_REG" =>
              Lib.curry (op ^) "r" o Int.toString o reg_index o List.hd
          | "ppc_prog$ppc_MEM" => K "b"
          | _ => fail())
in
   val ppc_rename = stateLib.rename_vars (ppc_rmap, ["b"])
end

local
   open stateLib
   val addr_eq_conv =
      SIMP_CONV (bool_ss++wordsLib.WORD_ARITH_ss++wordsLib.WORD_ARITH_EQ_ss) []
in
   val byte_memory_introduction =
      introduce_map_definition
         (ppc_progTheory.ppc_MEMORY_INSERT, addr_eq_conv)
end

local
   val MOVE_COND_RULE = Conv.CONV_RULE stateLib.MOVE_COND_CONV
   val SPEC_IMP_RULE =
      Conv.CONV_RULE
        (Conv.REWR_CONV (Thm.CONJUNCT1 (Drule.SPEC_ALL boolTheory.IMP_CLAUSES))
         ORELSEC MOVE_COND_CONV)
   val ppc_PC_INTRO0 =
      ppc_PC_INTRO |> Q.INST [`p1`|->`emp`, `p2`|->`emp`]
                    |> PURE_REWRITE_RULE [set_sepTheory.SEP_CLAUSES]
   val ppc_TEMPORAL_PC_INTRO0 =
      ppc_TEMPORAL_PC_INTRO |> Q.INST [`p1`|->`emp`, `p2`|->`emp`]
                             |> PURE_REWRITE_RULE [set_sepTheory.SEP_CLAUSES]
   fun MP_ppc_PC_INTRO th =
      Lib.tryfind (fn thm => MATCH_MP thm th)
         [ppc_PC_INTRO, ppc_TEMPORAL_PC_INTRO,
          ppc_PC_INTRO0, ppc_TEMPORAL_PC_INTRO0]
   val cnv = REWRITE_CONV [alignmentTheory.aligned_numeric]
   val ppc_PC_bump_intro =
      SPEC_IMP_RULE o
      Conv.CONV_RULE (Conv.LAND_CONV cnv) o
      MP_ppc_PC_INTRO o
      Conv.CONV_RULE
         (helperLib.POST_CONV
            (helperLib.LIST_MOVE_OUT_CONV false
               [``ppc_prog$ppc_PC``,
                ``ppc_prog$ppc_exception``]))
in
   val ppc_intro =
      ppc_PC_bump_intro o
      stateLib.introduce_triple_definition (false, ppc_pc_def)
end

local
   val component_11 = Drule.CONJUNCTS ppc_progTheory.ppc_component_11
   val ppc_rwts = tl (utilsLib.datatype_rewrites true "ppc"
                        ["ppc_state"])
   val imp_spec = ppc_progTheory.PPC_IMP_SPEC
   val imp_temp = ppc_progTheory.PPC_IMP_TEMPORAL
   val read_thms = [ppc_stepTheory.get_bytes] : thm list
   val write_thms = [] : thm list
   val select_state_thms = ppc_select_state_pool_thm :: ppc_select_state_thms
   val frame_thms = [ppc_frame, state_id]
   val map_tys = [word5, word]
   val EXTRA_TAC = ASM_REWRITE_TAC [boolTheory.DE_MORGAN_THM]
   val STATE_TAC = ASM_REWRITE_TAC ppc_rwts
   val basic_spec =
      stateLib.spec imp_spec imp_temp read_thms write_thms select_state_thms
         frame_thms component_11 map_tys EXTRA_TAC STATE_TAC
   fun rename_regs th =
     let
       val (_,p,_,_) = helperLib.dest_spec (concl th)
       val xs = helperLib.list_dest helperLib.dest_star p
       fun var v = if is_var v then v else fail()
       fun new_r tm =
         let
           val (r,v) = dest_ppc_REG tm
           val n = r |> rand |> numSyntax.int_of_term |> int_to_string
         in [var v |-> mk_var("r" ^ n, type_of v)] end
         handle HOL_ERR _ =>
         [(var (dest_ppc_CR0 tm) |-> mk_var("cr0", bool))] handle HOL_ERR _ =>
         [(var (dest_ppc_CR1 tm) |-> mk_var("cr1", bool))] handle HOL_ERR _ =>
         [(var (dest_ppc_CR2 tm) |-> mk_var("cr2", bool))] handle HOL_ERR _ =>
         [(var (dest_ppc_LR tm)  |-> mk_var("lr",  word))] handle HOL_ERR _ => []
     in INST (flatten (map new_r xs)) th end
  fun make_cr_into_var th =
    let
       val (_,p,_,_) = helperLib.dest_spec (concl th)
       val xs = helperLib.list_dest helperLib.dest_star p
       val tm = first (fn tm => aconv (rand tm) T orelse aconv (rand tm) F) xs
       val c = helperLib.MOVE_OUT_CONV (rator tm)
       val th = CONV_RULE (helperLib.PRE_CONV c THENC helperLib.POST_CONV c) th
       val th = MATCH_MP SPEC_IMP_F th |> SPEC_ALL handle HOL_ERR _ =>
                MATCH_MP SPEC_IMP_T th |> SPEC_ALL handle HOL_ERR _ =>
                MATCH_MP SPEC_IMP_F_ALT th |> SPEC_ALL handle HOL_ERR _ =>
                MATCH_MP SPEC_IMP_T_ALT th |> SPEC_ALL
    in th end handle HOL_ERR _ => th
in

   fun ppc_spec_hex s = let
     val thms = ppc_stepLib.ppc_step_hex s
     val ts = List.map ppc_mk_pre_post thms
     val thms_ts = ListPair.zip (thms, ts)
     (*
     val (thm,t) = hd thms_ts
     *)
     fun prove_one (thm,t) = let
       val th = basic_spec (thm,t)
       val th = th |> CONV_RULE (PATH_CONV "lrlrr" bitstringLib.v2w_n2w_CONV)
       val th = ppc_intro th
       val th = byte_memory_introduction th
       val th = make_cr_into_var th
       val th = ONCE_REWRITE_RULE [ppc_pc_cond_intro_neg] th
       val th = SIMP_RULE std_ss [] th
       val th = rename_regs th
       in th end
   in
     map prove_one thms_ts
   end

end



(* Testing...

val res = ppc_spec_hex "60000000"; (* nop *)
val res = ppc_spec_hex "397f0020"; (* addi r11,r31,32 *)
val res = ppc_spec_hex "39200000"; (* li r9,0  same as addi r9,r0,0 *)
val res = ppc_spec_hex "7d234b78"; (* mr r3,r9 *)
val res = ppc_spec_hex "48000030"; (* b 90 <f+0x58> *)
val res = ppc_spec_hex "4e800020"; (* blr *)
val res = ppc_spec_hex "7c0802a6"; (* mflr r0 *)
val res = ppc_spec_hex "5529073e"; (* clrlwi r9,r9,28 same as rlwinm r9, r9, 0, 28, 31 *)
val res = ppc_spec_hex "2c090063"; (* cmpwi r9,99 *)
val res = ppc_spec_hex "48000001"; (* bl 78 <f+0x40> *)
val res = ppc_spec_hex "7c0803a6"; (* mtlr r0 *)
val res = ppc_spec_hex "815f000c"; (* lwz r10,12(r31) *)
val res = ppc_spec_hex "913f001c"; (* stw r9,28(r31) *)
val res = ppc_spec_hex "9421ffe0"; (* stwu r1,-32(r1) *)
val res = ppc_spec_hex "4081ffcc"; (* ble 64 <f+0x2c> *)

*)

local
   fun format_thm th =
      (th, 4,
       stateLib.get_pc_delta
          (Lib.equal "ppc_prog$ppc_pc" o fst o boolSyntax.dest_strip_comb) th)
   val ppc_pc = Term.prim_mk_const {Thy = "ppc_prog", Name = "ppc_pc"}
in
   fun ppc_spec hex =
      case List.map format_thm (ppc_spec_hex hex) of
         [x] => (x, NONE)
       | [x1, x2] => (x1, SOME x2)
       | _ => raise ERR "ppc_spec" ""
   val ppc_tools = (ppc_spec, fn _ => fail(), pS_HIDE, ppc_pc): helperLib.decompiler_tools
end

(*

val res = ppc_spec "4081ffcc"; (* ble 64 <f+0x2c> *)

*)

end
