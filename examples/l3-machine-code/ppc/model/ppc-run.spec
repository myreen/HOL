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
   RA ` 5
   RB ` 5
   RT ` 5
   imm24 ` 24
}

-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
-- 32-bit Instruction Decoder
--
-- Instruction definitions based upon reference document
--   "Power ISA / Version 3.1B / September 14, 2021"
--   OPF_PowerISA_v3.1B.pdf
-- as found at
--   https://files.openpower.foundation/s/dAYSdGzTfW4j2r2
--
-- Page numbers are listed as found in page footers and
-- index entries; page '1' follows page 'xxvi'.
-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

instruction DecodeInst (w::word) =
{  mc = Inst (w);
   match w
   {
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- ADD RT, RA, RB (p77)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '011111 RT RA RB 0 100001010 0' =>
        {
           rt = [RT];
           ra = [RA];
           rb = [RB];
           Add (rt, ra, rb)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- B TARGET (p41)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '010010 imm24 0 0' =>
        {
           B (imm24)
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
