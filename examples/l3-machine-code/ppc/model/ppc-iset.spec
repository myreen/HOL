----------------------------------------------------------------------
-- Initial PowerPC test implementation
----------------------------------------------------------------------

-- Instruction semantics

define Add (rt :: ireg, ra :: ireg, rb :: ireg) =
{
   R (rt) <- R (ra) + R (rb);
   IncPC ()
}

define B (target :: bits(24), lr :: bool) =
{
   LR <- if lr then PC + 4 else LR;
   next = PC + SignExtend(target : '00');
   BranchTo (next)
}

define Bc (bo :: bits(5), bi :: bits(5), target :: bits(14), lr :: bool) =
{
   cond_met = branch_cond_met(bo, bi);
   LR <- if lr and cond_met then PC + 4 else LR;
   next = if cond_met then PC + SignExtend(target : '00') else PC + 4;
   BranchTo (next)
}

define Blr (bo :: bits(5), bi :: bits(5)) =
{
   cond_met = branch_cond_met(bo, bi);
   next = if cond_met then LR else PC + 4;
   BranchTo (next)
}

define Cmpwi (a :: ireg, si :: bits(32)) =
{
   CR0 <- (R (a) < si);
   CR1 <- (R (a) == si);
   CR2 <- (R (a) > si);
   IncPC ()
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

define Stw (rs :: ireg, ra :: ireg, d :: bits(32)) =
{
   b = if ra == 0 then 0 else R (ra);
   EA = b + d;
   -- DISCREPANCY: The spec defines this operation for 64-bit registers,
   -- not the 32-bit registers found in this model, so we omit the only
   -- store the lower 32 bits.
   mem (EA, 4) <- [R (rs)]
}

define Stwu (rs :: ireg, ra :: ireg, d :: bits(32)) =
{
   EA = R (ra) + d;
   -- DISCREPANCY: The spec defines this operation for 64-bit registers,
   -- not the 32-bit registers found in this model, so we omit the only
   -- store the lower 32 bits.
   mem (EA, 4) <- [R (rs)];
   R (ra) <- EA
}

define Lwz (rt :: ireg, ra :: ireg, d :: bits(32)) =
{
   b = if ra == 0 then 0 else R (ra);
   EA = b + d;
   -- DISCREPANCY: The spec defines this operation for 64-bit registers,
   -- not the 32-bit registers found in this model, so we omit the "zero
   -- the upper half of the register" step.
   R (rt) <- [mem (EA, 4)]
}

define Lwzu (rt :: ireg, ra :: ireg, d :: bits(32)) =
{
   EA = R (ra) + d;
   -- DISCREPANCY: The spec defines this operation for 64-bit registers,
   -- not the 32-bit registers found in this model, so we omit the "zero
   -- the upper half of the register" step.
   R (rt) <- [mem (EA, 4)];
   R (ra) <- EA
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
