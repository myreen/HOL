----------------------------------------------------------------------
-- Initial PowerPC test implementation
----------------------------------------------------------------------

-- Instruction semantics

define Add (rt :: ireg, ra :: ireg, rb :: ireg) =
{
   R (rt) <- R (ra) + R (rb);
   IncPC ()
}

define B (target :: bits(24)) =
{
   next = PC + SignExtend(target : '00');
   BranchTo (next)
}

define Addi (d :: ireg, a :: ireg, si :: bits(32)) =
{
   R (d) <- if a == 0 then si else R(a) + si;
   IncPC ()
}

define Or (s :: ireg, a :: ireg, b :: ireg) =
{
   R (a) <- R (s) || R (b);
   IncPC ()
}

define Ori (a :: ireg, s :: ireg, ui :: bits(32)) =
{
   R (a) <- R (s) || ui;
   IncPC ()
}

define Lwzx (rt :: ireg, ra :: ireg, rb :: ireg) =
{
   b = if ra == 0 then 0 else R (ra);
   EA = b + R (rb);
   -- DISCREPANCY: The spec defines this operation for 64-bit registers,
   -- not the 32-bit registers found in this model, so we omit the "zero
   -- the upper half of the register" step.
   R (rt) <- [mem (EA, 4)]
}

-------------------------------------------------------
-- Stubs for Hints and other Miscellaneous instructions
-------------------------------------------------------

define Undefined (imm32::word) = #UNDEFINED ("Unrecognised instruction", imm32)
