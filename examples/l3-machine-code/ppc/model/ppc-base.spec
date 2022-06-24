-- Bare-bones PPC skeleton
-- Originally based on 

-- Preliminaries

-----------------------------------
-- Word sizes (32-bit architecture)
-----------------------------------

type crbit = bits(2)
type ireg  = bits(5)
type freg  = bits(5)
type byte = bits(8)
type word = bits(32)

---------------------------
-- Specification exceptions
---------------------------

exception ASSERT :: string
exception UNPREDICTABLE :: string

---------------------------------
-- Memory mapped system registers
---------------------------------

-- [deleted]

------------------------
-- Mode/state operations
------------------------

-- [deleted]

---------------------------
-- ARM exceptions
---------------------------

-- [deleted]

-------------------------------------
-- General Purpose Registers (banked)
-------------------------------------

declare REG :: ireg -> word
declare LR  :: word
declare CTR :: word
declare PC  :: word

component R (n::ireg) :: word
{  value = REG(n)
   assign value = REG(n) <- value
}


--------------
-- Main Memory
--------------

declare MEM :: word -> byte

bool list mem1 (address::word) = [MEM(address)]

component mem (address::word, size::nat) :: bool list
{  value =
      match size
      { case 1 => (mem1(address + 0))<7:0>
        case 2 => (mem1(address + 1) : mem1(address + 0))<15:0>
        case 4 => (mem1(address + 3) : mem1(address + 2) :
                   mem1(address + 1) : mem1(address + 0))<31:0>
        case _ => #ASSERT("mem: size not in {1, 2, 4}")
      }
   assign value =
      match size
      { case 1 =>   MEM(address + 0) <- [value<7:0>]
        case 2 => { MEM(address + 0) <- [value<7:0>];
                    MEM(address + 1) <- [value<15:8>]
                  }
        case 4 => { MEM(address + 0) <- [value<7:0>];
                    MEM(address + 1) <- [value<15:8>];
                    MEM(address + 2) <- [value<23:16>];
                    MEM(address + 3) <- [value<31:24>]
                  }
        case _ => #ASSERT("mem: size not in {1, 2, 4}")
      }
}

bits(N) Align (w::bits(N), n::nat) = return [n * ([w] div n)]

bool Aligned (w::bits(N), n::nat) = return ( w == Align (w, n) )

component MemA (address::word, size::nat) :: bits(N) with N in 8,16,32
{  value =
      if not Aligned (address, size) then
      {
         #ASSERT("MemA: unaligned address")
      }
      else
      {
         value = mem(address, size);
         return [value]
      }

   assign value =
      if not Aligned (address, size) then
      {
         #ASSERT("MemA: unaligned address")
      }
      else
         mem(address, size) <- [value]
}

component MemU (address::word, size::nat) :: bits(N) with N in 8,16,32
{
   value = MemA(address, size)
   assign value = MemA(address, size) <- value
}

-------------------------------------
-- Branching and Exceptions (approx.)
-------------------------------------

unit BranchTo (address::word) = PC <- address

unit IncPC() = BranchTo (PC + 4)

--------------------------------
-- Bit and arithmetic operations
--------------------------------

-- Decode 1 instruction?
