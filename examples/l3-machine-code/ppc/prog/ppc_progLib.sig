signature ppc_progLib =
sig
   val ppc_tools    : helperLib.decompiler_tools
   val ppc_spec_hex : string -> Thm.thm list
end
