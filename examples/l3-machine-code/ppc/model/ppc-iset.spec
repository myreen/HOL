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

-------------------------------------------------------
-- Stubs for Hints and other Miscellaneous instructions
-------------------------------------------------------

define Undefined (imm32::word) = #UNDEFINED ("Unrecognised instruction", imm32)
