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
   RD ` 5
   RS ` 5
   BO ` 5
   BI ` 5
   BD ` 14
   SH ` 5
   MB ` 5
   ME ` 5
   imm24 ` 24
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
   z1 ` 1
   z2 ` 1
   z3 ` 1
   lr ` 1
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
     -- add RT, RA, RB (p77)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '011111 RT RA RB 0 100001010 0' =>
        {
           rt = [RT];
           ra = [RA];
           rb = [RB];
           Add (rt, ra, rb)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- b TARGET (p41)
     -- bl TARGET (p41)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '010010 imm24 0 lr' =>
        {
           B (imm24, [lr])
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- bc TARGET (p41)
     -- bcl TARGET (p41)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '010000 BO BI BD 0 lr' =>
        {
           Bc (BO, BI, BD, [lr])
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- blr (p42)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '010011 BO BI 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0' =>
        {
           Blr (BO, BI)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- cmpwi RA SIMM (p93)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '001011 000 0 0 RA SIMM' =>
        {  a = [RA];
           imm32 = SignExtend (SIMM);
           Cmpwi (a, imm32)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- addi D A SIMM
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '001110 RD RA SIMM' =>
        {  d = [RD];
           a = [RA];
           imm32 = SignExtend (SIMM);
           Addi (d, a, imm32)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- or S A B
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '011111 RS RA RB 01101111000' =>
        {  s = [RS];
           a = [RA];
           b = [RB];
           Or (s, a, b)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- ori S A UIMM
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '011000 RS RA UIMM' =>
        {  s = [RS];
           a = [RA];
           imm32 = ZeroExtend (UIMM);
           Ori (s, a, imm32)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- stw RS, D(RA) (p61)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '100100 RS RA SIMM' =>
        {  rs = [RS];
           ra = [RA];
           imm32 = SignExtend (SIMM);
           Stw (rs, ra, imm32)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- stwu RS, D(RA) (p61)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '100101 RS RA SIMM' =>
        {  rs = [RS];
           ra = [RA];
           imm32 = SignExtend (SIMM);
           Stwu (rs, ra, imm32)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- lwz RT, D(RA) (p55)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '100000 RT RA SIMM' =>
        {  rt = [RT];
           ra = [RA];
           imm32 = SignExtend (SIMM);
           Lwz (rt, ra, imm32)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- lwzu RT, D(RA) (p55)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '100001 RT RA SIMM' =>
        {  rt = [RT];
           ra = [RA];
           imm32 = SignExtend (SIMM);
           Lwzu (rt, ra, imm32)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- lwzx RT, RA, RB (p55)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '011111 RT RA RB 0000010111 0' =>
        {  rt = [RT];
           ra = [RA];
           rb = [RB];
           Lwzx (rt, ra, rb)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- mtlr RT (p127)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '011111 RT 01000 00000 0111010011 0' =>
        {  rt = [RT];
           Mtlr (rt)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- mflr RT (p129)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '011111 RT 01000 00000 0101010011 0' =>
        {  rt = [RT];
           Mflr (rt)
        }

     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     -- rlwinm RA,RS,SH,MB,ME (p107)
     -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     case '010101 RA RS SH MB ME 0' =>
        {  ra = [RA];
           rs = [RS];
           sh = [SH];
           mb = [MB];
           me = [ME];
           Rlwinm (ra,rs,sh,mb,me)
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
