------------------------------------------------------------------------
-- Formal Specification of the ARMv8-A instruction set architecture   --
-- Rob Arthan (rob.arthan@drisq.com)                                  --
-- (c) D-RisQ Ltd.                                                    --
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Note: this specification is far from complete.                     --
-- No attempt is made to model the behaviour of exceptions and NaNs.  --
-- Only a limited selection of Loads, Stores, Moves and               --
-- data-processing operations is supported.                           --
-- Only 64-bit registers and operations are supported                 --
------------------------------------------------------------------------

---------------------------
-- Floating-point Registers
---------------------------

-- Floating-point Control Register

register FPCR :: word
{
   31-27,
    14,
    7-3  : RES0   -- Reserved
   26    : AHP    -- Alternative half-precision control bit
   25    : DN     -- Default NaN use for NaN propagation
   24    : FZ	  -- Flushing denormalized numbers to zero control bit
   23-22 : RMode  -- Rounding mode: 00 - RN, 01 - RP, 10 - RM 11 - RZ
   21-20 : Stride -- AArch64 - ignored, AArch32 - implementation defined
   19    : FZ16   -- As FZ for half-precision if implemented, else Reserved
   18-16 : Len    -- AArch64 - ignored, AArch32 - implementation defined
   15    : IDE    -- Input Denormal f-p exception trap enable
   13    : EBF    -- BFloat16 control if implemented, else Reserved
   12    : IXE    -- Inexact f-p exception trap enable
   11    : UFE    -- Underflow f-p exception trap enable
   10    : OFE    -- Overflow f-p exception trap enable
   9     : DZE    -- Divide by Zero f-p exception trap enable
   8     : IOE    -- Invalid Operation f-p exception trap enagle
   2     : NEP    -- Output element control for FEAT_AFP
   1     : AH     -- ALternate Handling control for FEAT_AFP
   0     : FIZ    -- Flush Inputs to Zero control for FEAT_AFP
}

-- Floating-point Status Register

register FPSR :: word
{
   26-8,
    6-5  : RES0   -- Reserved
   31    : N      -- Condition flag (Negative)
   30    : Z      -- Condition flag (Zero)
   29    : C      -- Condition flag (Carry)
   28    : V      -- Condition flag (Overflow)
   27    : QC     -- Cumlative saturation bit
   7     : IDC    -- Input Denormal cumulative f-p exception bit
   4     : IXC    -- Inexact cumulative f-p exception bit
   3     : UFC    -- Underflow cumulative f-p exception bit
   2     : OFC    -- Overflow cumulative f-p exception bit
   1     : DZC    -- Divide by zero cumulative f-p exception bit
   0     : IOC    -- Invalid Operation cumulative f-p exception bit
}

declare
{
   FPCR      :: FPCR
   FPSR      :: FPSR
}

declare
{
   FPREG  :: reg -> dword
}

component D (n::reg) :: dword
{
   value = [FPREG (n)]
   assign value = FPREG (n) <- [value]
}

--------------------
-- Helper Operations
--------------------

ieee_rounding RoundingMode =
   match FPCR.RMode
   {
      case '00' => roundTiesToEven
      case '01' => roundTowardPositive
      case '10' => roundTowardNegative
      case '11' => roundTowardZero
   }

dword FPAdd64 (op1::dword, op2::dword) = FP64_Add (RoundingMode, op1, op2)
dword FPSub64 (op1::dword, op2::dword) = FP64_Sub (RoundingMode, op1, op2)
dword FPMul64 (op1::dword, op2::dword) = FP64_Mul (RoundingMode, op1, op2)

bool * bool * bool * bool FPCompare64 (op1::dword, op2::dword) =
   -- See ARM ARM J1-11445
   if FP64_IsNan (op1) or FP64_IsNan (op2) then
      (false, false, true, true)                 -- '0011'
   else if FP64_Equal (op1, op2) then
      (false, true, true, false)                 -- '0110'
   else if FP64_LessThan (op1, op2) then
      (true, false, false, false)                -- '1000'
   else
      (false, false, true, false)                -- '0010'

bits(64) FPZero64 (sign::bits(1)) = sign : 0`63

------------------------
-- Instruction Semantics
------------------------

exception UNSUPPORTED :: string

------------------------
-- FADD <Dd>, <Dn>, <Dm>
------------------------

define Data > FloatingPointAddSub(
  op :: bits(1), ftype :: bits(2), d :: reg, n :: reg, m :: reg) =
{
   match (ftype)
   {
      case '01' =>
         match (op)
         {
            case '0' => D(d) <- FPAdd64(D(n), D(m))
            case '1' => D(d) <- FPSub64(D(n), D(m))
         }
      case _  => #UNSUPPORTED "Floating-point op not double-precision"
   }
}

------------------------
-- FMOV Dd, Xn
-- FMOV Xd, Dn
------------------------

define Data > FloatingPointMov(
  sf :: bits(1), ftype :: bits(2), opcode0 :: bits(1), d :: reg, n :: reg) =
{
   match (sf, ftype)
   {
      case ('1', '11') =>
         match (opcode0)
            {
               case '0' => D(d) <- X(n)
               case '1' => X(d) <- D(n)
            }
      case _  => #UNSUPPORTED "Floating-point op not double-precision"
   }
}

------------------------
-- FCMP Dn, Dm
-- FCMP Dn, #0.0
-- FCMPE Dn, Dm
-- FCMPE Dn, #0.0
------------------------

define Data > FloatingPointCompare(
  ftype :: bits(2), opc :: bits(2), m :: reg, n :: reg) =
{
   match (ftype)
   {
      case '01' =>
         match (opc<0:0>)
            {
               case '0' =>
                  SetTheFlags(true, FPCompare64(D(n), D(m)))
               case '1' =>
                  SetTheFlags(true, FPCompare64(D(n), FPZero64('0')))
            }
      case _  => #UNSUPPORTED "Floating-point op not double-precision"
   }
}

------------------------
-- LDR Dt, [<Xn|SP>, #pimm]
-- STR Dt, [<Xn|SP>, #pimm]
------------------------

define LoadStore > LoadStoreRegisterFloatingPoint(
   size :: bits(2), opc :: bits(2), imm12 :: bits(12), n :: reg, t :: reg) =
{
   address = if n == 31 then
                SP
             else
                X(n);
   address =  address + ZeroExtend(imm12);
   match (size)
   {
      case '11' =>
         match (opc<0:0>) -- bit 22: 0 => store / 1 => load
            {
               case '0' =>
                  {
                     data = D(t);
                     Mem(address, 8, AccType_NORMAL) <- data
                  }
               case '1' =>
                  {
                     data`64 = Mem(address, 8, AccType_NORMAL);
                     D(t) <- data
                  }
            }
      case _  => #UNSUPPORTED "Floating-point op not double-precision"
   }
}

