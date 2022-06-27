----------------------------------------------------------------------
-- Initial PowerPC test implementation
----------------------------- -----------------------------------------

define Run

--------------------
-- Instruction fetch
--------------------

construct MachineCode {
   Inst   :: word
}

MachineCode Fetch =
{  fpc = PC;
   inst = MemA (fpc, 4);
   Inst (inst)
}

-----------------------
-- Instruction decoding
-----------------------

pattern {
   A ` 5
   B ` 5
   C ` 5
   D ` 5
   imm2 ` 2
   imm3 ` 3
   imm4 ` 4
   imm5 ` 5
   imm6 ` 6
   imm7 ` 7
   imm8 ` 8
   imm11 ` 11
}

-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
-- 32-bit Instruction Decoder
-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

instruction DecodeInst (w::word) =
{  mc = Inst (w);
   match w
   {
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- ADD D, A, B (??)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '011111 D A B 01000010100' =>
        {  d = [D];
           a = [A];
           b = [B];
           Add (d, a, b)
        }


     -- ~~~~~~~~~~~~~~~
     -- Everything else
     -- ~~~~~~~~~~~~~~~

     case _ => Undefined (0)
   }
}

clear patterns

instruction Decode (mc::MachineCode) =
   match mc
   {
     case Inst (w) => { DecodeInst (w) }
   }

------------
-- Top-level
------------

unit Next = Run (Decode (Fetch))
