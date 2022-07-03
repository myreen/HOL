signature ppc_stepLib =
sig

   val ppc_instruction: Term.term -> string
   val ppc_step: bool * bool -> string -> Thm.thm list
   val ppc_step_code: bool * bool -> string quotation -> Thm.thm list list
   val ppc_step_hex: bool * bool -> string -> Thm.thm list
   val ppc_decode: bool -> Term.term -> Thm.thm list
   val ppc_decode_hex: bool -> string -> Thm.thm list
   val hex_to_bits: string -> Term.term
   val list_instructions: unit -> (string * Term.term) list
   val print_instructions: unit -> unit

   (*

     open ppc_stepLib
     val () = print_instructions ()
     val ev = ppc_step (true, true)
     fun pev s = (print (s ^ "\n"); Count.apply ev s);
     val _ = Count.apply (List.map ev) (list_instructions ())
     val _ = Count.apply (List.map (Lib.total pev)) (list_instructions ())
     ev "POP; 2"
     ev "ADD (pc)"

   *)
end
