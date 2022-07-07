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

-------------------------------------------------------
-- Stubs for Hints and other Miscellaneous instructions
-------------------------------------------------------

define Undefined (imm32::word) = #UNDEFINED ("Unrecognised instruction", imm32)
