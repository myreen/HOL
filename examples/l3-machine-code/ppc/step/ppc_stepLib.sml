(* ------------------------------------------------------------------------
   PowerPC step evaluator
   ------------------------------------------------------------------------ *)

structure ppc_stepLib :> ppc_stepLib =
struct

open HolKernel boolLib bossLib

open ppcTheory ppc_stepTheory
open state_transformerSyntax blastLib

structure Parse =
struct
   open Parse
   val (Type, Term) = parse_from_grammars ppc_stepTheory.ppc_step_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "ppc_stepLib"
val WARN = Feedback.HOL_WARNING "ppc_stepLib"

val () = show_assums := true

(* ========================================================================= *)

val mk_byte = bitstringSyntax.mk_vec 8
val rhsc = utilsLib.rhsc
fun mapl x = utilsLib.augment x [[]]

fun MATCH_HYP_RW l = utilsLib.MATCH_HYP_CONV_RULE (REWRITE_CONV l)
val REG_CONV = REWRITE_CONV [v2w_13_15_rwts, v2w_ground4, v2w_ground5]

val opcodes     = utilsLib.list_mk_wordii 4 (List.tabulate (16, Lib.I))
val arithlogic  = utilsLib.list_mk_wordii 4 [0,1,2,3,4,5,6,7,12,14]
val testcompare = utilsLib.list_mk_wordii 2 [0,2,3]

val st = Term.mk_var ("s", Type.mk_type ("ppc_state", []))

fun mk_ppc_const n = Term.prim_mk_const {Thy = "ppc", Name = n}
fun mk_ppc_type n = Type.mk_thy_type {Thy = "ppc", Tyop = n, Args = []}

(* ---------------------------- *)

local
   val a_of = utilsLib.accessor_fns o mk_ppc_type
   val u_of = utilsLib.update_fns o mk_ppc_type
   val state_fns = a_of "ppc_state"
   val other_fns =
      [pairSyntax.fst_tm, pairSyntax.snd_tm, bitstringSyntax.v2w_tm,
       ``IncPC ()``, ``(h >< l) : 'a word -> 'b word``] @ u_of "ppc_state"
   val exc = ``SND (raise'exception e s : 'a # ppc_state)``
in
   val cond_rand_thms = utilsLib.mk_cond_rand_thms (other_fns @ state_fns)
   val snd_exception_thms =
      utilsLib.map_conv
         (Drule.GEN_ALL o
          utilsLib.SRW_CONV [cond_rand_thms, ppcTheory.raise'exception_def] o
          (fn tm => Term.mk_comb (tm, exc))) state_fns
end

(* ---------------------------- *)

(* PPC datatype theorems/conversions *)

fun datatype_thms thms =
   thms @ [cond_rand_thms, snd_exception_thms, FST_SWAP,
           ppc_stepTheory.Align, ppc_stepTheory.Aligned] @
   utilsLib.datatype_rewrites true "ppc" ["ppc_state"]

val DATATYPE_CONV = REWRITE_CONV (datatype_thms [])
val DATATYPE_RULE = Conv.CONV_RULE DATATYPE_CONV
val FULL_DATATYPE_RULE = utilsLib.FULL_CONV_RULE DATATYPE_CONV

val COND_UPDATE_CONV =
   REWRITE_CONV
     (utilsLib.qm [] ``!b. (if b then T else F) = b`` ::
      utilsLib.mk_cond_update_thms (List.map mk_ppc_type ["ppc_state"]))

val COND_UPDATE_RULE = Conv.CONV_RULE COND_UPDATE_CONV

val STATE_CONV =
   REWRITE_CONV (utilsLib.datatype_rewrites true "ppc" ["ppc_state"] @
                 [boolTheory.COND_ID, cond_rand_thms])

local
   val cmp = computeLib.bool_compset ()
   val () = computeLib.add_thms (datatype_thms [pairTheory.FST]) cmp
in
   val EVAL_DATATYPE_CONV = Conv.TRY_CONV (utilsLib.CHANGE_CBV_CONV cmp)
end

fun fix_datatype tm = rhsc (Conv.QCONV DATATYPE_CONV tm)
val fix_datatypes = List.map fix_datatype

fun specialized0 m tms =
    utilsLib.specialized m (Conv.ALL_CONV, fix_datatypes tms)
fun specialized1 m tms =
    utilsLib.specialized m (utilsLib.WGROUND_CONV, fix_datatypes tms)

local
   fun ADD_PRECOND_RULE thm = FULL_DATATYPE_RULE thm
   val rwts = ref ([]: thm list)
in
   fun getThms tms =
      List.map ADD_PRECOND_RULE (specialized1 "eval" tms (!rwts))
      |> List.filter (not o utilsLib.vacuous)
   fun resetThms () = rwts := []
   fun addThms thms = (rwts := thms @ !rwts; thms)
end

val EV = utilsLib.STEP (datatype_thms, st)
val resetEvConv = utilsLib.resetStepConv
val setEvConv = utilsLib.setStepConv

(* ========================================================================= *)

(* register access *)

(*

val () = setEvConv utilsLib.WGROUND_CONV

val PC_rwt =
   EV [PC_def, R_def] [] []
      ``PC`` |> hd

val () = resetEvConv ()

val write'PC_rwt =
   EV [write'PC_def] [] []
      ``write'PC x`` |> hd

local
   val mask_sp =
      blastLib.BBLAST_PROVE
         ``d && 0xFFFFFFFCw : word32 = ((31 >< 2) d : word30) @@ (0w: word2)``

   fun r_rwt t = Q.prove(t,
      wordsLib.Cases_on_word_value `n`
      \\ simp [write'R_def, R_def, R_name_def, LookUpSP_def, num2RName_thm,
               mask_sp]
      )
      |> Drule.UNDISCH
in
   val R_name_rwt = r_rwt
      `n <> 15w ==> (R n ^st = ^st.REG (R_name ^st.CONTROL.SPSEL n))`

   val write'R_name_rwt = r_rwt
      `n <> 15w ==>
       (write'R (d, n) ^st =
        ^st with REG :=
        (R_name ^st.CONTROL.SPSEL n =+
        if n = 13w then d && 0xFFFFFFFCw else d) ^st.REG)`

   val RName_LR_rwt = EVAL ``ppc_step$R_name x 14w``
end

*)

(* ---------------------------- *)

(* write PC *)

val BranchTo_rwt =
   EV [BranchTo_def] [] []
     ``BranchTo imm32`` |> hd

val IncPC_rwt =
   EV [IncPC_def, BranchTo_rwt] [] []
     ``IncPC ()`` |> hd

(*

val BranchWritePC_rwt =
   EV [BranchWritePC_def, BranchTo_rwt] [] []
     ``BranchWritePC imm32`` |> hd

val BXWritePC_rwt =
   EV [BXWritePC_def, BranchTo_rwt]
      [[``^st.CurrentMode <> Mode_Handler``, ``word_bit 0 (imm32:word32)``]] []
    ``BXWritePC imm32`` |> hd

val BLXWritePC_rwt =
   EV [BLXWritePC_def, BranchTo_rwt] [[``word_bit 0 (imm32:word32)``]] []
    ``BLXWritePC imm32`` |> hd

val LoadWritePC_rwt =
   EV [LoadWritePC_def, BXWritePC_rwt] [] []
    ``LoadWritePC imm32`` |> hd

val ALUWritePC_rwt =
   EV [ALUWritePC_def, BranchWritePC_rwt] [] []
      ``ALUWritePC d`` |> hd

*)

(* ---------------------------- *)

(* read mem *)

fun fixwidth_for ty =
  bitstringTheory.fixwidth_id
    |> Q.ISPEC `w2v (w:^(ty_antiq (wordsSyntax.mk_word_type ty)))`
    |> REWRITE_RULE [bitstringTheory.length_w2v]
    |> Conv.CONV_RULE (Conv.DEPTH_CONV wordsLib.SIZES_CONV)
    |> Drule.GEN_ALL

val mem_rwt =
  EV ([mem_def, mem1_def, concat16, concat32, bitstringTheory.field_fixwidth] @
      List.map fixwidth_for [``:8``, ``:16``, ``:32``]) []
    (mapl (`n`, [``1n``,``2n``,``4n``]))
    ``mem (a, n)``

local
   val rwts =
     [MemA_def, cond_rand_thms, snd_exception_thms, alignmentTheory.aligned_0,
      wordsTheory.WORD_ADD_0, bitstringTheory.v2w_w2v]
in
   val MemA_1_rwt =
     EV (rwts @ [bitstringTheory.field_fixwidth, fixwidth_for ``:8``]) [] []
       ``MemA (v, 1) : ppc_state -> word8 # ppc_state``
       |> hd

   val MemA_2_rwt =
     EV (extract16 :: rwts) [[``aligned 1 (v:word32)``]] []
       ``MemA (v, 2) : ppc_state -> word16 # ppc_state``
       |> hd

   val MemA_4_rwt =
     EV (extract32 :: rwts) [[``aligned 2 (v:word32)``]] []
       ``MemA (v, 4) : ppc_state -> word32 # ppc_state``
       |> hd

   val MemU_1_rwt =
     EV [MemU_def, MemA_1_rwt] [] []
       ``MemU (v, 1) : ppc_state -> word8 # ppc_state``
       |> hd

   val MemU_2_rwt =
     EV [MemU_def, MemA_2_rwt] [] []
       ``MemU (v, 2) : ppc_state -> word16 # ppc_state``
       |> hd

   val MemU_4_rwt =
     EV [MemU_def, MemA_4_rwt] [] []
       ``MemU (v, 4) : ppc_state -> word32 # ppc_state``
       |> hd
end

(* ---------------------------- *)

(* write mem *)

(*

val write'mem_rwt =
  EV ([write'mem_def]) [] (mapl (`n`, [``1n``,``2n``,``4n``]))
    ``write'mem (v, a, n)``

local
   val field_cond_rand = Drule.ISPEC ``field h l`` boolTheory.COND_RAND
   val rwts =
     [write'MemA_def, cond_rand_thms, snd_exception_thms,
      wordsTheory.WORD_ADD_0, bitstringTheory.v2w_w2v,
      alignmentTheory.aligned_0, field_cond_rand] @
     write'mem_rwt @ BigEndianReverse_rwt
in
   val write'MemA_1_rwt =
     EV (rwts @ [fixwidth_for ``:8``, bitstringTheory.field_fixwidth]) [] []
       ``write'MemA (w: word8, v, 1)``
       |> hd

   val write'MemA_2_rwt =
     EV (field16 :: rwts) [[``aligned 1 (v:word32)``]] []
       ``write'MemA (w:word16, v, 2)``
       |> hd

   val write'MemA_4_rwt =
     EV (field32 :: rwts) [[``aligned 2 (v:word32)``]] []
       ``write'MemA (w:word32, v, 4)``
       |> hd

   val write'MemU_1_rwt =
     EV [write'MemU_def, write'MemA_1_rwt] [] []
       ``write'MemU (w: word8, v, 1)``
       |> hd

   val write'MemU_2_rwt =
     EV [write'MemU_def, write'MemA_2_rwt] [] []
       ``write'MemU (w: word16, v, 2)``
       |> hd

   val write'MemU_4_rwt =
     EV [write'MemU_def, write'MemA_4_rwt] [] []
       ``write'MemU (w: word32, v, 4)``
       |> hd
end;

*)

(* ---------------------------- *)

local
   val word_bit_conv = wordsLib.WORD_BIT_INDEX_CONV true
   val map_word_bit_rule =
      List.map (Conv.CONV_RULE (Conv.LHS_CONV word_bit_conv))
   fun word_bit_thms n =
      let
         val v = bitstringSyntax.mk_vec n 0
         fun wb i = wordsSyntax.mk_word_bit (numSyntax.term_of_int i, v)
      in
         List.tabulate (n, fn i => bitstringLib.word_bit_CONV (wb i))
      end
   val suc_rule =
      Conv.CONV_RULE
         (Conv.LHS_CONV (Conv.RATOR_CONV (Conv.RAND_CONV reduceLib.SUC_CONV)))
in
   fun BIT_THMS_CONV n =
      let
         val wbit_thms = word_bit_thms n
         val widx_thms = map_word_bit_rule wbit_thms
      (* val dim_thm =
            wordsLib.SIZES_CONV
               (wordsSyntax.mk_dimindex (fcpSyntax.mk_int_numeric_type n))
         val thms = ref ([dim_thm, wordsTheory.bit_count_def] @ wbit_thms) *)
         val thms = ref wbit_thms
         val c = ref (PURE_REWRITE_CONV (!thms))
         fun bit_count_thms v =
            let
               fun upto_thm i =
                  wordsSyntax.mk_bit_count_upto (numSyntax.term_of_int i, v)
               fun thm i t =
                  let
                     val thm =
                        wordsTheory.bit_count_upto_SUC
                        |> Drule.ISPECL [v, numSyntax.term_of_int (i - 1)]
                        |> suc_rule
                  in
                     i |> upto_thm
                       |> (Conv.REWR_CONV thm
                           THENC Conv.LAND_CONV (REWRITE_CONV widx_thms)
                           THENC Conv.RAND_CONV (Conv.REWR_CONV t)
                           THENC numLib.REDUCE_CONV)
                  end
               fun loop a i =
                  if n < i then a else loop (thm i (hd a) :: a) (i + 1)
            in
               loop [Drule.ISPEC v wordsTheory.bit_count_upto_0] 1
            end
      in
         fn tm =>
            (!c) tm
            handle Conv.UNCHANGED =>
              let
                 val v =
                    HolKernel.find_term
                      (fn t =>
                         case Lib.total bitstringSyntax.dest_v2w t of
                            SOME (_, ty) =>
                               fcpSyntax.dest_int_numeric_type ty = n andalso
                               List.null (Term.free_vars t)
                          | NONE => false) tm
                 val () = thms := !thms @ (bit_count_thms v)
                 val () = c := PURE_REWRITE_CONV (!thms)
              in
                 (!c) tm
              end
      end
end

val BIT_THMS_CONV_9 = BIT_THMS_CONV 9
val BIT_THMS_CONV_8 = BIT_THMS_CONV 8 ORELSEC BIT_THMS_CONV_9

(* ========================================================================= *)

(* Fetch *)

fun mk_bool_list l = listSyntax.mk_list (l, Type.bool)

local
   val err = ERR "dest_bool_list" "bad Bool list"
in
   fun dest_bool_list tm =
      case Lib.total listSyntax.dest_list tm of
         SOME (l, ty) => (ty = Type.bool orelse raise err; l)
       | NONE => raise err
end

local
   fun pad_opcode n =
      let
         val wty = fcpSyntax.mk_int_numeric_type n
      in
         fn v =>
            let
               val l = dest_bool_list v
               val () = ignore (List.length l <= n
                                orelse raise ERR "pad_opcode" "bad Bool list")
            in
               (utilsLib.padLeft boolSyntax.F n l, wty)
            end
      end
   fun mk_ppc2_pair l =
      let
         val l1 = mk_bool_list (List.take (l, 16))
         val l2 = mk_bool_list (List.drop (l, 16))
      in
         pairSyntax.mk_pair (l1, l2)
      end
   val pad_16 = pad_opcode 16
   val pad_32 = pad_opcode 32
   val hex_to_bits_16 =
      mk_bool_list o fst o pad_16 o bitstringSyntax.bitstring_of_hexstring
   val hex_to_bits_16x2 =
      mk_ppc2_pair o fst o pad_32 o bitstringSyntax.bitstring_of_hexstring
   val hex_to_bits_32 =
      fst o pad_32 o bitstringSyntax.bitstring_of_hexstring
  val ty_32 = ``:32``
in
   val split_ppc2_pat = mk_ppc2_pair o dest_bool_list
   fun hex_to_bits s = hex_to_bits_32 s
   fun mk_opcode v = bitstringSyntax.mk_v2w(v,ty_32)
end

local
   val lem = Q.prove (
      `(!p. ((if p then v2w [b1; b2; b3] else v2w [b4; b5; b6]) = 7w : word3) =
             (if p then b1 /\ b2 /\ b3 else b4 /\ b5 /\ b6)) /\
       (!p. ((if p then v2w [b1; b2] else v2w [b3; b4]) = 0w : word2) =
             (if p then ~b1 /\ ~b2 else ~b3 /\ ~b4))`,
      lrw []
      \\ CONV_TAC (Conv.LHS_CONV bitstringLib.v2w_eq_CONV)
      \\ decide_tac)

   val CONC_RULE =
     SIMP_RULE (srw_ss()++boolSimps.LET_ss)
        [bitstringTheory.fixwidth_def, bitstringTheory.field_def,
         bitstringTheory.shiftr_def, bitstringTheory.w2w_v2w, lem] o
     ONCE_REWRITE_RULE [bitstringTheory.word_concat_v2w_rwt]

   val lem =
      Drule.LIST_CONJ
        [simpLib.SIMP_CONV (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
            ``(15 >< 13) (((w1:word8) @@ (w2:word8)) : word16) : word3``,
         simpLib.SIMP_CONV (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
            ``(12 >< 11) (((w1:word8) @@ (w2:word8)) : word16) : word2``,
         simpLib.SIMP_CONV (srw_ss()) [] ``a + 2w + 1w : word32``]

   val rule =
      CONC_RULE o
      ASM_REWRITE_RULE [cond_rand_thms, lem,
         bitstringTheory.word_extract_v2w, bitstringTheory.word_bits_v2w]

   val ALIGNED_PLUS_RULE =
      MATCH_HYP_RW [alignmentTheory.aligned_add_sub_123,
                    alignmentTheory.aligned_numeric]
        ``aligned c (a + b : 'a word)``

   val ppc2_test_tm =
      fix_datatype
       ``((15 >< 13) (FST (MemA (^st.PC,2) s): word16) = 7w: word3) /\
          (12 >< 11) (FST (MemA (^st.PC,2) s): word16) <> 0w: word2``

   val not_ppc2_test_tm = boolSyntax.mk_neg ppc2_test_tm

   fun bytes4 l =
      let
         val (b1, l) = Lib.split_after 8 l
         val (b2, l) = Lib.split_after 8 l
         val (b3, b4) = Lib.split_after 8 l
      in
         (b1, b2, b3, b4)
      end

   fun build_byte n l =
      List.tabulate (8,
         fn i => (bitstringSyntax.mk_bit (7 - i + n) |-> List.nth (l, i)))

   val assign_ppc = fn v =>
      let
         val (b1, b2, b3, b4) = bytes4 v
      in
         build_byte 24 b1 @ build_byte 16 b2 @
         build_byte 8 b3 @ build_byte 0 b4
      end

in
  fun fetch l =
    if List.length l = 32
    then rule (Thm.INST (assign_ppc l) IMP_Fetch)
    else raise ERR "fetch" "length must be 32"
  fun fetch_tm tm = fetch (dest_bool_list tm)
end

val fetch_hex = fetch o hex_to_bits;

(*

val l = hex_to_bits "7C221A14" (* add 1,2,3 *)

fetch_hex "7C221A14" (* add 1,2,3 *)

*)

(* ========================================================================= *)

(* Decode *)

val DecodeInst =
    DecodeInst_def
        |> Thm.SPEC (bitstringSyntax.mk_vec 32 0)
        |> Conv.RIGHT_CONV_RULE
             (REWRITE_CONV [ppcTheory.boolify32_v2w, Decode_simps]
              THENC Conv.DEPTH_CONV PairedLambda.let_CONV)

local
   val v = fst (bitstringSyntax.dest_v2w (bitstringSyntax.mk_vec 32 0))
in
   fun DecodeInst_rwt pat =
      let
         val (thm, s) = (DecodeInst, fst (Term.match_term v pat))
      in
         Thm.INST s thm
      end
end

(* -- *)

val ppc_patterns = List.map (I ## utilsLib.pattern)
  [("Add",    "FTTTTT_______________FTFFFFTFTFF")
  ]

(* -- *)

local
   val sep1 = String.tokens (Lib.equal #",")
   val sep2 = String.tokens (fn c => c = #"-" orelse Char.isSpace c)
   fun err s = raise ERR "index" ("bad index: " ^ s)
   fun index s = case Int.fromString s of
                    SOME i => (i < 32 orelse err s; i)
                  | NONE => err s
   fun reg_array s =
      let
         val a = Array.array (32, boolSyntax.F)
         fun set i = Array.update (a, i, boolSyntax.T)
      in
         List.app
            (fn r => case sep2 r of
                        [i] => set (index i)
                      | [i, j] =>
                          let
                             val x = index i
                             val y = index j
                          in
                             Lib.for_se (Int.min (x, y)) (Int.max (x, y)) set
                          end
                      | _ => raise ERR "reg_array" "syntax error") (sep1 s)
          ; a
      end
in
   fun reg_list_subst (n, p) s =
      let
         val a = reg_array s
      in
         List.tabulate
           (n, fn i => Term.mk_var ("x" ^ Int.toString (i + p), Type.bool) |->
                       Array.sub (a, n - 1 - i))
      end
end

local
   val ppc_pats = Redblackmap.fromList String.compare ppc_patterns
   fun printn s = TextIO.print (s ^ "\n")
   fun lsub s i = Char.toUpper (String.sub (s, i))
   val splitAtSemi = utilsLib.splitAtChar (Lib.equal #";")
   fun sharePrefix3 s1 s2 =
      let
         val n = Int.min (3, Int.min (String.size s1, String.size s2))
         val f1 = lsub s1
         val f2 = lsub s2
         fun loop i = i >= n orelse f1 i = f2 i andalso loop (i + 1)
      in
         loop 0
      end
   fun comma i =
      let
         val is = Int.toString i
      in
         fn "" => is
          | s => is ^ "," ^ s
      end
   val reglist =
      snd o
      List.foldr
        (fn (t, (i, s)) =>
           (i + 1, if Teq t then comma i s else s)) (0, "")
   fun insertRegList i = fn s => (s:string)
in
   fun list_instructions () = Redblackmap.listItems ppc_pats
   val list_mnemonics = List.map fst o list_instructions
   val print_instructions = List.app printn o list_mnemonics
   fun mk_ppc_opcode s =
      let
         val (s1, s2) = splitAtSemi s
         val m = if s2 = ""
                 then []
                 else raise ERR "mk_ppc_opcode" ("bad suffix: " ^ s)
      in
         case Redblackmap.peek (ppc_pats, s1) of
            SOME pat => Term.subst m pat
          | NONE =>
              let
                 val p = list_mnemonics ()
                         |> List.filter (sharePrefix3 s1)
                         |> Lib.commafy
                         |> String.concat
                 val p = if p = "" then "." else ". Try: " ^ p
              in
                 raise ERR "mk_ppc_opcode" ("Not found: " ^ s1 ^ p)
              end
      end
   fun ppc_instruction opc =
      let
         val f = case Lib.total listSyntax.dest_list opc of
                    SOME (i, _) => insertRegList i
                  | NONE => Lib.I
         fun mtch s = Term.match_term (mk_ppc_opcode s) opc
      in
         case List.filter (Lib.can mtch) (list_mnemonics()) of
            [] => raise ERR "ppc_instruction" "no match found"
          | [s] => f s
          | ["ADD", s as "ADD (pc)"] => s
          | ["MOV", s as "MOV (pc)"] => s
          | _ => raise ERR "ppc_instruction" "more than one match!"
      end
end

(* -- *)

local
   fun f ps = List.map (DecodeInst_rwt o snd) ps
   val rwts_32 = f ppc_patterns
   val DecodeInst_tm = mk_ppc_const "DecodeInst"
   fun mk_decode_ppc t = Term.list_mk_comb (DecodeInst_tm, [t])
   val rewrites =
      [v2w_13_15_rwts,
       bitstringLib.v2n_CONV ``v2n [F;F;F;F;F]``,
       blastLib.BBLAST_PROVE
         ``((v2w [T;T;b;T] = 13w: word4) \/ (v2w [T;T;b;T] = 15w: word4)) = T``]
   val raise_tm = mk_ppc_const "raise'exception"
   val avoid =
      List.filter
         (not o Lib.can (HolKernel.find_term (Term.same_const raise_tm) o rhsc))
   val FINISH_RULE =
      List.map
        (utilsLib.ALL_HYP_CONV_RULE (REWRITE_CONV [boolTheory.DE_MORGAN_THM]) o
         Conv.RIGHT_CONV_RULE
            (REG_CONV THENC REWRITE_CONV [GSYM bitstringTheory.n2w_v2n]
                      THENC Conv.DEPTH_CONV bitstringLib.v2n_CONV
                      THENC REWRITE_CONV [bitstringTheory.n2w_v2n]))
   val rwconv = REWRITE_CONV rewrites
   val x = (DATATYPE_CONV, fix_datatypes [])
   fun gen_rws m r = rewrites @ utilsLib.specialized m x r
   val rw = REWRITE_CONV (gen_rws "decode PPC" rwts_32)
   val FALL_CONV =
       REWRITE_CONV
           (datatype_thms [v2w_ground4,v2w_ground5] @
            gen_rws "decode PPC (fallback)" [DecodeInst])
in
   fun ppc_decode v =
       let
           val tm = mk_decode_ppc (mk_opcode v)
       in
           (rw tm
            handle Conv.UNCHANGED =>
                   (WARN "ppc_decode" "fallback (slow) decode"
                  ; FALL_CONV tm))
           |> utilsLib.split_conditions
           |> avoid
           |> FINISH_RULE
           |> (fn l => if List.null l
                          then raise ERR "ppc_decode"
                                     ("unpredictable: " ^
                                      utilsLib.long_term_to_string v)
                       else l)
       end
end

val ppc_decode_hex = ppc_decode o mk_bool_list o hex_to_bits;

(*

ppc_decode_hex "7C221A14" (* add 1,2,3 *)

*)

(* ========================================================================= *)

(* Run *)

fun add_simple_dfn th = let
  val tm = th |> SPEC_ALL |> concl |> dest_eq |> fst
  val tm2 = mk_comb(tm,st)
  val lemma = EV [th,write'R_def,IncPC_rwt,R_def] [] [] tm2
  val _ = addThms lemma
  in lemma end

val res = map add_simple_dfn
  [dfn'Add_def
  ,dfn'Addi_def
  ,dfn'Or_def
  ,dfn'Ori_def
  ,dfn'B_def
  ,dfn'Bc_def
  ,dfn'Blr_def
  ,dfn'Cmpwi_def
  ,dfn'Mflr_def
  ,dfn'Mtlr_def
  ,dfn'Rlwinm_def
  ,dfn'Lwz_def
  ,dfn'Lwzu_def
  ,dfn'Lwzx_def
  ,dfn'Stw_def |> SIMP_RULE (srw_ss()) [write'mem_def,LET_THM]
  ,dfn'Stwu_def |> SIMP_RULE (srw_ss()) [write'mem_def,LET_THM]]

(* Evaluator *)

local
   val word_bit_8 =
      bitstringLib.word_bit_CONV
         ``word_bit 8 (v2w [b8; b7; b6; b5; b4; b3; b2; b1; b0] : word9)``
   val both_rwts = [v2w_13_15_rwts]
   val hyps_rwts = word_bit_8 :: both_rwts
   val conc_rwts = [] @ both_rwts
   val eval_simp_rule =
      REWRITE_RULE conc_rwts o
      utilsLib.ALL_HYP_CONV_RULE (REWRITE_CONV hyps_rwts)
   fun ev tm rwt =
       let
           val thm = eval_simp_rule (utilsLib.INST_REWRITE_CONV1 rwt tm)
       in
           if utilsLib.vacuous thm then NONE else SOME thm
       end
   val net = utilsLib.mk_rw_net utilsLib.lhsc (getThms [])
in
   fun eval tm =
       (case List.mapPartial (ev tm) (utilsLib.find_rw net tm) of
            [] => raise ERR "eval" "no valid step theorem"
          | [x] => x
          | (x::_) => x (*
          | l => (Parse.print_term tm
                ; print "\n"
                ; raise ERR "eval" "more than one valid step theorem") *) )
       handle HOL_ERR {message = "not found",
                       origin_function = "find_rw", ...} =>
              raise (Parse.print_term tm
                   ; print "\n"
                   ; ERR "eval" "instruction instance not supported")
end


(*
 val tm = thm3 |> Drule.SPEC_ALL |> rhsc
*)

(*
val v = (mk_bool_list o hex_to_bits) "7C221A14" (* add 1,2,3 *)
*)

val EXPAND_CONV =
  SIMP_CONV std_ss [BranchTo_def]

local
   val u2 = wordsSyntax.mk_wordii (2, 32)
   val u4 = wordsSyntax.mk_wordii (4, 32)
   val get_val = snd o dest_eq o concl
   val get_state = rhsc
   val state_exception_tm =
       mk_ppc_const $
         TypeBasePure.mk_recordtype_fieldsel
           {tyname = "ppc_state", fieldname = "exception"}
   fun mk_proj_exception r = Term.mk_comb (state_exception_tm, r)
   fun eval_sw2sw th = let
     val tms = find_terms wordsSyntax.is_sw2sw (concl th)
     in REWRITE_RULE (map EVAL tms) th end
   val mask_pat = “ppc$mask _”
   fun eval_mask th = let
     val tms = find_terms (can (match_term mask_pat)) (concl th)
     in REWRITE_RULE (map EVAL tms) th end
   val MP_Next = eval_mask o
                 eval_sw2sw o
                 SIMP_RULE std_ss [wordsTheory.WORD_OR_CLAUSES, wordsTheory.w2w_0,
                                   ppc_step_simps,v2w_field_rwts1,v2w_field_rwts2] o
                 CONV_RULE EXPAND_CONV o
                 Drule.MATCH_MP (ppc_stepTheory.NextStatePPC |> UNDISCH)
   val Run_CONV = utilsLib.Run_CONV ("ppc", st) o get_val
   fun is_ineq tm =
      boolSyntax.is_eq (boolSyntax.dest_neg tm) handle HOL_ERR _ => false
   val n = 0
   val pat = “FST (branch_cond_met _ _)”
in
   val eval_ppc =
      let
         val tms = [T]
         val ftch = fetch o fst o listSyntax.dest_list
         val dec = ppc_decode
      in
         fn n => fn v =>
            let
               val mp = MP_Next
               val thm1 = ftch v
               val thm2 = List.nth (dec v, n)
               val thm3 = Run_CONV thm2
               val thm4 = thm3 |> Drule.SPEC_ALL |> rhsc |> eval
               val ineq_hyps =
                  List.mapPartial
                     (fn tm => if is_ineq tm then SOME (ASSUME tm) else NONE)
                     (Thm.hyp thm4)
               val (thm2, thm4) =
                  if List.null ineq_hyps
                     then (thm2, thm4)
                  else
                     (utilsLib.ALL_HYP_CONV_RULE (REWRITE_CONV ineq_hyps) thm2,
                      REWRITE_RULE ineq_hyps thm4)
               val r = get_state thm4
                       handle HOL_ERR {origin_function = "dest_pair", ...} =>
                         (Parse.print_thm thm4
                          ; print "\n"
                          ; raise ERR "eval_ppc" "failed to fully evaluate")
               val thm5 = (EXPAND_CONV THENC STATE_CONV) (mk_proj_exception r)
               val thm = Drule.LIST_CONJ [thm1, thm2, thm3, thm4, thm5]
                         |> SIMP_RULE std_ss [branch_cond_always_met,mem_def]
               val thms = let
                 val tm = find_term (can (match_term pat)) (concl thm)
                 val thm1 = DISCH tm thm |> SIMP_RULE std_ss []
                            |> SIMP_RULE std_ss [branch_cond_met_simp] |> UNDISCH
                 val thm2 = DISCH (mk_neg tm) thm |> SIMP_RULE std_ss []
                            |> SIMP_RULE std_ss [branch_cond_met_simp] |> UNDISCH
                 in [thm1, thm2] end handle HOL_ERR _ => [thm]
            in
               map mp thms
            end
      end
end

local
   fun ev (s,v) = eval_ppc 0 v
in
   fun ppc_step s =
       let
           val v = mk_ppc_opcode s
       in
           ev (s, v)
       end
   fun ppc_step_hex h =
       let
           val v = mk_bool_list (hex_to_bits h)
       in
           ev ("", v)
       end
end

(*
fun ppc_step_code config =
   List.map (ppc_step_hex config) o
   (ppcAssemblerLib.ppc_code: string quotation -> string list)
*)

(* ---------------------------- *)

(* testing:

val h = "7C221A14"; (* add 1,2,3 *)
val h = "48000030"; (* b 90 <f+0x58> *)
val h = "48000001"; (* bl 78 <f+0x40> *)
val h = "4e800020"; (* blr *)
val h = "4081ffcc"; (* ble 64 <f+0x2c> *)
val h = "815f000c"; (* lwz r10,12(r31) *)
val h = "913f001c"; (* stw r9,28(r31) *)
val h = "9421ffe0"; (* stwu r1,-32(r1) *)
val h = "552a1838"; (* rlwinm r10,r9,3,0,28 *)
val h = "5529103a"; (* rlwinm r9,r9,2,0,29 *)
val h = "5529073e"; (* clrlwi  r9,r9,28 same as rlwinm r9, r9, 0, 28, 31 *)

val v = mk_bool_list (hex_to_bits h)

ppc_step_hex h

*)

end
