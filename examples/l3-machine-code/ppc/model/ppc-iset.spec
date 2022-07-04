----------------------------------------------------------------------
-- Initial PowerPC test implementation
----------------------------------------------------------------------

-- Instruction semantics

define Add (rt :: ireg, ra :: ireg, rb :: ireg) =
{
   R (rt) <- R (ra) + R (rb);
   IncPC ()
}

-------------------------------------------------------
-- Stubs for Hints and other Miscellaneous instructions
-------------------------------------------------------

define Undefined (imm32::word) = #UNDEFINED ("Unrecognised instruction", imm32)
