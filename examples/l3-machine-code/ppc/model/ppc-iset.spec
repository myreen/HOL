----------------------------------------------------------------------
-- Initial PowerPC test implementation
----------------------------------------------------------------------

-- Instruction semantics

define Add (d :: ireg, a :: ireg, b :: ireg) =
{
   R (d) <- R (a) + R (b);
   IncPC ()
}

-------------------------------------------------------
-- Stubs for Hints and other Miscellaneous instructions
-------------------------------------------------------

define Undefined (imm32::word) = #UNDEFINED ("Unrecognised instruction", imm32)
