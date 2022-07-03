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
   A ` 5
   B ` 5
   C ` 5
   D ` 5
   S ` 5
   imm2 ` 2
   imm3 ` 3
   imm4 ` 4
   imm5 ` 5
   imm6 ` 6
   imm7 ` 7
   imm8 ` 8
   imm11 ` 11
   imm16 ` 16
   SIMM ` 16
   UIMM ` 16
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

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- addi D A SIMM
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '001110 D A SIMM' =>
        {  d = [D];
           a = [A];
           imm32 = SignExtend (SIMM);
           Addi (d, a, imm32)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- or S A B
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '011111 S A B 01101111000' =>
        {  s = [S];
           a = [A];
           b = [B];
           Or (s, a, b)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- ori S A UIMM
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '011000 S A UIMM' =>
        {  s = [S];
           a = [A];
           imm32 = ZeroExtend (UIMM);
           Ori (s, a, imm32)
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
