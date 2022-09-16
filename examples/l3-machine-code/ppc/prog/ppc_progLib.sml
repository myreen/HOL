structure ppc_progLib :> ppc_progLib =
struct

open HolKernel boolLib bossLib
open (* stateLib *) spec_databaseLib ppc_progTheory

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
val pc_tm = Term.mk_var ("pc", word)
val (_, _, dest_ppc_instr, _) = ppc_1 "ppc_instr"
val (_, mk_ppc_PC, dest_ppc_PC, is_ppc_PC) = ppc_1 "ppc_PC"
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
       ["MEM", "PC", "SP_EL0", "branch_hint"],
       ["MEM", "PC", "REG", "branch_hint"],
       ["MEM", "PC", "branch_hint"],
       ["REG", "SP_EL0", "branch_hint"],
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

(*
local
   val err = ERR "DISJOINT_CONV" ""
   val cnv =
      LAND_CONV wordsLib.WORD_EVAL_CONV
      THENC REWRITE_CONV [ppc_progTheory.sub_intro, wordsTheory.WORD_ADD_ASSOC]
   fun split_ppc_instr tm =
      Lib.with_exn (pairSyntax.dest_pair o dest_ppc_instr) tm err
in
   fun DISJOINT_CONV tm =
      let
         val (l, r) = Lib.with_exn pred_setSyntax.dest_disjoint tm err
         val (a, x) = split_ppc_instr l
         val y = snd (split_ppc_instr r)
         val a = case utilsLib.strip_add_or_sub a of
                    (_, [(false, w)]) => wordsSyntax.mk_word_2comp w
                  | (_, [(true, w)]) => w
                  | (_, [(true, w), (true, x)]) =>
                      wordsSyntax.mk_word_add (w, x)
                  | (_, [(false, w), (true, x)]) =>
                      wordsSyntax.mk_word_add (wordsSyntax.mk_word_2comp w, x)
                  | _ => raise err
         val thm =
            Conv.CONV_RULE cnv
               (Drule.SPECL [a, pc_tm, x, y] ppc_progTheory.DISJOINT_ppc_instr)
      in
         if Thm.concl thm ~~ tm
            then Drule.EQT_INTRO thm
         else raise err
      end
end
*)

(*
local
   fun is_pc_relative tm =
      case Lib.total dest_ppc_MEM tm of
         SOME (t, _) => fst (utilsLib.strip_add_or_sub t) ~~ pc_tm
       | NONE => false
   fun rwt (w, a) =
      [Drule.SPECL [a, w] ppc_progTheory.MOVE_TO_TEMPORAL_PPC_CODE_POOL,
       Drule.SPECL [a, w] ppc_progTheory.MOVE_TO_PPC_CODE_POOL]
   fun move_to_code wa =
      REWRITE_RULE
       ([stateTheory.BIGUNION_IMAGE_1, stateTheory.BIGUNION_IMAGE_2,
         set_sepTheory.STAR_ASSOC, set_sepTheory.SEP_CLAUSES,
         ppc_progTheory.disjoint_ppc_instr_thms,
         ppc_stepTheory.concat_bytes] @
        List.concat (List.map rwt wa))
   val byte_chunks = stateLib.group_into_chunks (dest_ppc_MEM, 4, false)
   val strip_pre =
      progSyntax.strip_star o fst o temporal_stateSyntax.dest_pre_post' o
      Thm.concl
in
   val chunk32 = stateLib.chunks_intro_pre_process ppc_progTheory.ppc_WORD_def
   fun extend_ppc_code_pool thm =
      if Lib.exists is_pc_relative (strip_pre thm)
         then let
                 val thm' = chunk32 thm
                 val (s, wa) = byte_chunks (strip_pre thm')
              in
                 if List.null s
                    then thm
                 else move_to_code wa (Thm.INST (List.concat s) thm')
              end
      else thm
end
*)

(* -- *)

fun reg_index tm = Lib.with_exn wordsSyntax.uint_of_word tm (ERR "reg_index" "")

local
   fun other_index tm =
      case fst (Term.dest_const (boolSyntax.rator tm)) of
         "cond" => 0
       | "ppc_PC" => 1
       | "ppc_exception" => 2
       | "ppc_PSTATE_EL" => 3
       | "ppc_SCTLR_EL1_E0E" => 4
       | "ppc_PSTATE_N" => 5
       | "ppc_PSTATE_Z" => 6
       | "ppc_PSTATE_C" => 7
       | "ppc_PSTATE_V" => 8
       | "ppc_SP_EL0" => 9
       | "ppc_TCR_EL1_TBI0" => 10
       | "ppc_TCR_EL1_TBI1" => 11
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
  fun selnm ty f =
      "ppc$" ^ TypeBasePure.mk_recordtype_fieldsel{tyname=ty,fieldname=f}
   val st = Term.mk_var ("s", ``:ppc_state``)
   val pstate_footprint =
      stateLib.write_footprint ppc_1 ppc_2 []
        [] [] []
        (fn (s, l) => s = selnm "ppc_state" "PSTATE" andalso tml_eq l [st])
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
     (* [(fupnm "ppc_state" "PSTATE", pstate_footprint),
         (fupnm "ppc_state" "branch_hint", fn (p, q, _) => (p, q))] *)
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
   val rwts =
      List.map bitstringLib.v2w_n2w_CONV
         (List.tabulate
            (32, fn i => bitstringSyntax.padded_fixedwidth_of_num
                           (Arbnum.fromInt i, 5)))
in
   val REG_CONV = Conv.QCONV (REWRITE_CONV rwts)
end;

local
   val dest_reg = dest_ppc_REG
   val width_reg = 5
   val proj_reg = NONE
   val reg_conv = REG_CONV
   val ok_conv = Conv.DEPTH_CONV wordsLib.word_EQ_CONV
                 THENC Conv.QCONV (SIMP_CONV (bool_ss++boolSimps.CONJ_ss) [])
   fun asm_rule (tm: term) = (raise ERR "" "") : thm
   val model_tm = ``PPC_MODEL``
in
   val combinations =
      (*stateLib.*)register_combinations
         (dest_reg, width_reg, proj_reg, reg_conv, ok_conv, asm_rule, model_tm)
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
   val concat_bytes_rule =
      Conv.CONV_RULE
         (stateLib.PRE_COND_CONV
             (SIMP_CONV (bool_ss++boolSimps.CONJ_ss)
                 [alignmentTheory.aligned_numeric,
                  alignmentTheory.aligned_imp, DECIDE ``2 < 3n``])) o
      PURE_REWRITE_RULE [ppc_stepTheory.concat_bytes]
   val chunk32 = chunks_intro_pre_process ppc_progTheory.ppc_WORD_def
in
   val byte_memory_introduction =
      introduce_map_definition
         (ppc_progTheory.ppc_MEMORY_INSERT, addr_eq_conv)
end

local
   val reg_eq_conv = Conv.DEPTH_CONV wordsLib.word_EQ_CONV
                     THENC REWRITE_CONV []
in
   val gp_introduction =
      stateLib.introduce_map_definition
         (ppc_progTheory.ppc_REGISTERS_INSERT, reg_eq_conv)
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
      stateLib.introduce_triple_definition (false, ppc_pc_def) (* o
      extend_ppc_code_pool *)
end

local
   val dest_some_pair =
      Lib.total (pairSyntax.dest_pair o optionSyntax.dest_some)
   fun mask_subst tm =
      case Lib.total boolSyntax.dest_eq tm of
         SOME (l, r) =>
            (case (dest_some_pair l, dest_some_pair r) of
                (SOME (l1, l2), SOME (r1, r2)) => [r1 |-> l1, r2 |-> l2]
              | _ => [])
       | NONE => []
   val rule =
      REWRITE_RULE [stateTheory.cond_true_elim, boolTheory.DE_MORGAN_THM]
in
   fun DecodeBitMasks_RULE thm =
      let
         val p = temporal_stateSyntax.dest_pre' (Thm.concl thm)
         val p = progSyntax.strip_star p
      in
         case List.mapPartial (Lib.total progSyntax.dest_cond) p of
            [tm] => let
                       val s = mask_subst tm
                    in
                       rule (if List.null s then thm else Thm.INST s thm)
                    end
          | _ => thm
      end
end

fun tdistinct tl = HOLset.numItems (listset tl) = length tl

local
   val rwt = utilsLib.map_conv (SIMP_CONV bool_ss [])
               [``if b then x else T``, ``if b then x else F``]
   fun check_unique_reg_CONV tm =
      let
         val p = progSyntax.strip_star (temporal_stateSyntax.dest_pre' tm)
         val rp = List.mapPartial (Lib.total (fst o dest_ppc_REG)) p
      in
         if tdistinct rp
            then Conv.ALL_CONV tm
         else raise ERR "check_unique_reg_CONV" "duplicate register"
      end
   exception FalseTerm
   fun NOT_F_CONV tm =
      if Feq tm then raise FalseTerm else Conv.ALL_CONV tm
   fun is_reducible tm =
      case Lib.total boolSyntax.dest_strip_comb tm of (*
         SOME ("ppc$LSL", [_]) => true
       | SOME ("ppc$ASR", [_]) => true
       | SOME ("ppc$LSR", [_]) => true
       | SOME ("ppc$ROR", [_]) => true
       | SOME ("ppc$ShiftValue", [_]) => true
       | SOME ("ppc$DecodeRegExtend", [_]) => true
       | SOME ("ppc$ExtendWord", [_]) => true
       | SOME ("ppc$ConditionTest", [_]) => true
       | SOME ("ppc$DecodeBitMasks", [_]) => true
       | SOME ("fcp$dimindex", [_]) => true
       | *) _ => false
   val cnv = ALL_CONV (*Conv.CHANGED_CONV ppc_stepLib.PPC_CONV *)
   val SELECTIVE_PPC_CONV =
      Conv.DEPTH_CONV (fn tm => if is_reducible tm then cnv tm else NO_CONV tm)
   val WGROUND_RW_CONV =
      Conv.DEPTH_CONV (utilsLib.cache 10 Term.compare bitstringLib.v2w_n2w_CONV)
      THENC utilsLib.WGROUND_CONV
      THENC SELECTIVE_PPC_CONV
      THENC REWRITE_CONV []
   val cnv =
      REG_CONV
      THENC check_unique_reg_CONV
      THENC stateLib.PRE_COND_CONV (REWRITE_CONV [] THENC NOT_F_CONV)
  (*  THENC ppc_stepLib.DATATYPE_CONV  *)
      THENC WGROUND_RW_CONV
      THENC stateLib.PRE_COND_CONV
               ((* Conv.DEPTH_CONV DISJOINT_CONV
                THENC *) REWRITE_CONV
                        [alignmentTheory.aligned_numeric,
                         alignmentTheory.aligned_0,
                         optionTheory.NOT_NONE_SOME]
                THENC NOT_F_CONV)
      THENC helperLib.POST_CONV (stateLib.PC_CONV "ppc_prog$ppc_pc")
in
   fun simp_triple_rule thm =
      ppc_rename (DecodeBitMasks_RULE (Conv.CONV_RULE cnv thm))
      handle FalseTerm => raise ERR "simp_triple_rule" "condition false"
end

datatype memory = Flat | Array32 | Array64 | Map8 | Map32 | Map64
type opt = {gpr_map: bool, mem: memory, temporal: bool, newline: bool}

local
   val newline_options =
      [["newline"],
       ["no-newline"]]
   val gpr_map_options =
      [["map-gpr", "gpr-map", "reg-map", "map-reg"],
       ["no-map-gpr", "no-gpr-map"]]
   val mem_options =
      [["map-mem8", "mem-map8", "mapped8", "map8"],
       ["map-mem32", "mem-map32", "mapped32", "map32"],
       ["map-mem64", "mem-map64", "mapped64", "map64"],
       ["array-mem32", "mem-array32", "array32"],
       ["array-mem64", "mem-array64", "array64"],
       ["flat-map", "mem-flat", "flat"]]
   val temporal_options =
      [["temporal"],
       ["not-temporal"]]
   fun isDelim c = Char.isPunct c andalso c <> #"-" orelse Char.isSpace c
   val memopt =
      fn 0 => Map8
       | 1 => Map32
       | 2 => Map64
       | 3 => Array32
       | 4 => Array64
       | 5 => Flat
       | _ => raise ERR "process_rule_options" ""
   val print_options = utilsLib.print_options NONE
in
   fun basic_opt () =
      {newline = true, gpr_map = false, mem = Flat,
       temporal = stateLib.generate_temporal()}: opt
   val default_opt =
      {newline = true, gpr_map = false, mem = Map8, temporal = false}: opt
   fun proj_opt ({gpr_map, mem, ...}: opt) = (gpr_map, mem)
   fun closeness (target: opt) (opt: opt) =
      (case (#gpr_map opt, #gpr_map target) of
          (false, true) => 0
        | (true, false) => ~100
        | (_, _) => 1) +
      (case (#mem opt, #mem target) of
          (Flat, _) => 0
        | (_, Flat) => ~100
        | (m1, m2) => if m1 = m2 then 1 else ~10)
   fun convert_opt_rule (opt: opt) (target: opt) =
      (if #gpr_map target andalso not (#gpr_map opt)
          then gp_introduction
       else Lib.I) o
      (if #mem target = #mem opt
         then Lib.I
       else case #mem target of
               Flat => Lib.I
             | _ => byte_memory_introduction
             )
   fun process_rule_options s =
      let
         val l = String.tokens isDelim s
         val l = List.map utilsLib.lowercase l
         val (newline, l) =
            utilsLib.process_opt newline_options "Print newlines"
               (#newline default_opt) l (Lib.equal 0)
         val (gpr_map, l) =
            utilsLib.process_opt gpr_map_options "Introduce GPR map"
               (#gpr_map default_opt) l (Lib.equal 0)
         val (mem, l) =
            utilsLib.process_opt mem_options "MEM type"
               (#mem default_opt) l memopt
         val (temporal, l) =
            utilsLib.process_opt temporal_options "Temoporal triple"
               (#temporal default_opt) l (Lib.equal 0)
      in
         if List.null l
            then {gpr_map = gpr_map, mem = mem, temporal = temporal,
                  newline = newline}: opt
         else ( print_options "Print options" newline_options
              ; print_options "Register view" gpr_map_options
              ; print_options "Memory view" mem_options
              ; print_options "Temporal triple" temporal_options
              ; raise ERR "process_options"
                    ("Unrecognized option" ^
                     (if List.length l > 1 then "s" else "") ^
                     ": " ^ String.concat (commafy l))
              )
      end
end

(*
local
   val v31 = wordsSyntax.mk_wordii (31, 5)
   fun get_cond tm = let val (c, _, _) = boolSyntax.dest_cond tm in c end
   fun is_cond_31 tm =
      case Lib.total boolSyntax.dest_cond tm of
         SOME (c, v, _) =>
           (Lib.total wordsSyntax.uint_of_word v = SOME 0 andalso
            case Lib.total boolSyntax.dest_eq c of
               SOME (l, r) => r ~~ v31 andalso bitstringSyntax.is_v2w l
             | NONE => false)
       | NONE => false
   fun all_assigns acc =
      fn [] => acc
       | (h: Term.term) :: t =>
          all_assigns
            (List.map (fn s => ASSUME h :: s) acc @
             List.map (fn s => ASSUME (boolSyntax.mk_neg h) :: s) acc) t
   val all_assigns = all_assigns [[]]
in
   fun split_on_31 th =
      let
         val tm = boolSyntax.list_mk_conj (Thm.concl th :: Thm.hyp th)
         val l = Lib.op_mk_set aconv (HolKernel.find_terms is_cond_31 tm)
      in
         if List.null l
            then [th]
         else let
                 val assigns = all_assigns (List.map get_cond l)
                 fun rule rwts =
                    ppc_stepLib.REG_31_RULE
                       (utilsLib.FULL_CONV_RULE (REWRITE_CONV rwts) th)
              in
                 List.filter (not o utilsLib.vacuous) (List.map rule assigns)
              end
      end
end
*)

local
   val ppc_step = ppc_stepLib.ppc_step (*
      List.map
         (PURE_REWRITE_RULE
            [ppc_stepTheory.mem_half_def,
             ppc_stepTheory.mem_word_def,
             ppc_stepTheory.mem_dword_def]) o
      ppc_stepLib.ppc_step o Option.valOf o ppc_stepLib.ppc_pattern *)
   fun thm_eq thm1 thm2 = Term.aconv (Thm.concl thm1) (Thm.concl thm2)
   val mk_thm_set = Lib.op_mk_set thm_eq
   val component_11 = Drule.CONJUNCTS ppc_progTheory.ppc_component_11
   val ppc_rwts = tl (utilsLib.datatype_rewrites true "ppc"
                        ["ppc_state"])
   val imp_spec = ppc_progTheory.PPC_IMP_SPEC
   val imp_temp = ppc_progTheory.PPC_IMP_TEMPORAL
   val read_thms = [ppc_stepTheory.get_bytes] : thm list
   val write_thms = [] : thm list
   val select_state_thms = ppc_select_state_pool_thm :: ppc_select_state_thms
   val frame_thms = [ppc_frame, (* ppc_frame_hidden, *) state_id]
   val map_tys = [word5, word]
   val EXTRA_TAC = ASM_REWRITE_TAC [boolTheory.DE_MORGAN_THM]
   val STATE_TAC = ASM_REWRITE_TAC ppc_rwts
   val basic_spec =
      (*stateLib.*)spec imp_spec imp_temp read_thms write_thms select_state_thms
         frame_thms component_11 map_tys EXTRA_TAC STATE_TAC
   val get_opcode =
      fst o bitstringSyntax.dest_v2w o
      snd o pairSyntax.dest_pair o
      List.last o pred_setSyntax.strip_set o
      temporal_stateSyntax.dest_code' o
      Thm.concl
   val (reset_db, set_current_opt, get_current_opt, add1_pending, find_spec,
        list_db) =
      spec_databaseLib.mk_spec_database basic_opt default_opt proj_opt
         closeness convert_opt_rule get_opcode (ppc_intro o basic_spec)
   val spec_label_set = ref (Redblackset.empty String.compare)
   fun reset_specs () =
      (reset_db (); spec_label_set := Redblackset.empty String.compare)
   fun spec_spec opc thm =
      let
         val thm_opc = get_opcode thm
         val a = fst (Term.match_term thm_opc opc)
      in
         simp_triple_rule (Thm.INST a thm)
      end
   fun pend_spec s =
      let
         val thms = ppc_step s
         val ts = List.map ppc_mk_pre_post thms
         val thms_ts = ListPair.zip (thms, ts)
         val thms_ts = List.concat (List.map combinations thms_ts)
      in
         List.map (fn x => (print "."; add1_pending x)) thms_ts
         ; thms_ts
      end
   val string_to_opcode =
      bitstringSyntax.bitstring_of_hexstring o StringCvt.padLeft #"0" 8
   val nl = ref (fn () => ())
in
   val list_db = list_db
   fun ppc_config options =
      let
         val opt = process_rule_options options
      in
         if #temporal (get_current_opt ()) = #temporal opt
            then ()
         else (reset_specs (); stateLib.set_temporal (#temporal opt))
       ; nl := (fn () => if #newline opt then print "\n" else ())
       ; set_current_opt opt
      end
   fun ppc_spec s =
      List.map (fn t => (print "+"; basic_spec t)) (pend_spec s) before !nl ()
   fun addInstructionClass s =
      ( print (" " ^ s)
      ; if Redblackset.member (!spec_label_set, s)
           then ()
        else ( pend_spec s
             ; spec_label_set := Redblackset.add (!spec_label_set, s)
             )
      )
   fun ppc_spec_hex looped s =
      let
         val opc = string_to_opcode s
      in
         case find_spec opc of
         (*
         val SOME (new, thms) = find_spec opc
         *)
            SOME (new, thms) =>
              let
                 val l = List.mapPartial (Lib.total (spec_spec opc)) thms
              in
                 if List.null l
                    then loop looped opc "failed to find suitable spec" s
                 else (if new then !nl () else (); mk_thm_set l)
              end
          | NONE => loop looped opc "failed to add suitable spec" s
      end
   and loop looped opc e s = raise ERR "ppc_spec_hex" (e ^ ": " ^ s) (*
      if looped
         then raise ERR "ppc_spec_hex" (e ^ ": " ^ s)
      else ( case ppc_stepLib.ppc_instruction opc of
             (*
             val SOME s = ppc_stepLib.ppc_instruction opc
             val () = addInstructionClass s
             *)
                SOME s => addInstructionClass s
              | NONE => raise ERR "ppc_spec_hex" "not supported"
           ; ppc_spec_hex true s) *)
(* val ppc_spec_code = List.map ppc_spec_hex o ppcAssemblerLib.ppc_code *)

   fun ppc_spec_hex s = let
     val thms = ppc_stepLib.ppc_step_hex s
     val ts = List.map ppc_mk_pre_post thms
     val thms_ts = ListPair.zip (thms, ts)
     val thms_ts = List.concat (List.map combinations thms_ts)
     (* --- *)
     val x = hd thms_ts
     val th = basic_spec x
     val th = th |> CONV_RULE (PATH_CONV "lrlrr" bitstringLib.v2w_n2w_CONV)
     val th = ppc_intro th
   in
     th
   end

end

(* Testing...

TODO:
 - support cond branch
 - support load word
 - support load byte
 - support store word
 - support store byte
 - clean up memory
 - rename registers,cr,lr

val s = "397f0020"; (* addi r11,r31,32 *)

(* todo *)

val res = ppc_spec_hex "815f000c"; (* lwz r10,12(r31) *)
val res = ppc_spec_hex "4081ffcc"; (* ble 64 <f+0x2c> *)
val res = ppc_spec_hex "913f001c"; (* stw r9,28(r31) *)
val res = ppc_spec_hex "9421ffe0"; (* stwu r1,-32(r1) *)

(* works *)

val res = ppc_spec_hex "60000000"; (* nop *)
val res = ppc_spec_hex "397f0020"; (* addi r11,r31,32 *)
val res = ppc_spec_hex "39200000"; (* li r9,0  same as addi r9,r0,0 *)
val res = ppc_spec_hex "7d234b78"; (* mr r3,r9 *)
val res = ppc_spec_hex "48000030"; (* b 90 <f+0x58> *)
val res = ppc_spec_hex "4e800020"; (* blr *)
val res = ppc_spec_hex "7c0802a6"; (* mflr r0 *)
val res = ppc_spec_hex "5529073e"; (* clrlwi  r9,r9,28 same as rlwinm r9, r9, 0, 28, 31 *)
val res = ppc_spec_hex "2c090063"; (* cmpwi r9,99 *)
val res = ppc_spec_hex "48000001"; (* bl 78 <f+0x40> *)
val res = ppc_spec_hex "7c0803a6"; (* mtlr r0 *)

*)

end
