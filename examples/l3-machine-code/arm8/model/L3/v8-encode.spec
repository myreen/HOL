-----------------------------------------------------------------------
-- Formal Specification of the ARMv8-A instruction set architecture  --
-- (c) Anthony Fox, University of Cambridge                          --
-----------------------------------------------------------------------

-----------------------------------------------------------------------
-- Instruction encoding -----------------------------------------------
-----------------------------------------------------------------------

construct MachineCode
{
   ARM8 :: word
   BadCode :: string
}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

nat CountTrailing (b::bool, w::bits(N))
   HOL "CountTrailing.terminates" measure [w] =
   if w<0> == b or if b then w == 0 else w == -1 then 0
   else 1 + CountTrailing (b, w >>+ 1)

nat * nat * nat EncodeBitMaskAux (imm::bits(N)) with N in 32, 64 =
{
   pref0 = CountTrailing (true, imm);
   if pref0 == 0 then
   {
      pref1 = CountTrailing (false, imm);
      run0 = CountTrailing (true, imm #>> pref1);
      run1 = CountTrailing (false, imm #>> (pref1 + run0));
      (run0 + run1, run1, run1 - pref1)
   }
   else
   {
      run1 = CountTrailing (false, imm #>> pref0);
      run0 = CountTrailing (true, imm #>> (pref0 + run1));
      (run0 + run1, run1, run0 + run1 - pref0)
   }
}

-- Algorithm courtesy of Shaked Flur --
(bits(1) * bits(6) * bits(6)) option
   EncodeBitMask (imm::bits(N)) with N in 32, 64 =
{
   e, S, R = EncodeBitMaskAux (imm);
   immN, imms, immr = if e == 64 then (1, [S - 1], [R])
                      else (0, ~[e * 2 - 1] || [S - 1], [R]);
   match DecodeBitMasks (immN, imms, immr, true)
   {
      case Some (imm2, _) =>
         if imm == imm2 then Some (immN, imms, immr) else None
      case None => None
   }
}

bits(1) e_sf (sf::bits(N)) = [N == 64]

bits(2) option EncodeLogicalOp (opc::LogicalOp, setflags::bool) =
   match opc, setflags
   {
      case LogicalOp_AND, false => Some (0)
      case LogicalOp_ORR, false => Some (1)
      case LogicalOp_EOR, false => Some (2)
      case LogicalOp_AND, true  => Some (3)
      case _ => None
   }

MachineCode e_data (i::Data) =
   match (i)
   {
      case AddSubShiftedRegister@32 (_, opc, s, sh, rm, imm6, rn, rd) =>
         if imm6<5> then
            BadCode ("AddSubShiftedRegister32")
         else
            ARM8 ('0' : [opc]`1 : [s]`1 : '01011' : [sh]`2 : '0' : rm : imm6 :
                  rn : rd)
      case AddSubShiftedRegister@64 (_, opc, s, sh, rm, imm6, rn, rd) =>
         ARM8 ('1' : [opc]`1 : [s]`1 : '01011' : [sh]`2 : '0' : rm : imm6 :
               rn : rd)
      case AddSubExtendRegister@32 (sf, opc, s, rm, sty, imm3, rn, rd)
        or AddSubExtendRegister@64 (sf, opc, s, rm, sty, imm3, rn, rd) =>
         ARM8 (e_sf (sf) : [opc]`1 : [s]`1 : '01011001' : rm : [sty]`3 : imm3 :
               rn : rd)
      case AddSubImmediate@32 (sf, opc, s, imm, rn, rd)
        or AddSubImmediate@64 (sf, opc, s, imm, rn, rd) =>
         if imm && ~0xFFF == 0 then
           ARM8 (e_sf (sf) : [opc]`1 : [s]`1 : '10001_00' : imm<11:0> : rn : rd)
         else if imm && ~0xFFF000 == 0 then
           ARM8 (e_sf (sf) : [opc]`1 : [s]`1 : '10001_01' : imm<23:12> :
                 rn : rd)
         else
           BadCode ("AddSubImmediate")
      case AddSubCarry@32 (_, opc, s, rm, rn, rd) =>
         ARM8 ('0' : [opc]`1 : [s]`1 : '11010000' : rm : '000000' : rn : rd)
      case AddSubCarry@64 (_, opc, s, rm, rn, rd) =>
         ARM8 ('1' : [opc]`1 : [s]`1 : '11010000' : rm : '000000' : rn : rd)
      case LogicalShiftedRegister@32(sf, opc, invert, s, sh, imm, rm, rn, rd)
        or LogicalShiftedRegister@64(sf, opc, invert, s, sh, imm, rm, rn, rd) =>
         match EncodeLogicalOp (opc, s)
         {
           case Some (opc) =>
           {
              imm6 = [imm];
              if imm == [imm6] then
                 ARM8 (e_sf (sf) : opc : '01010' : [sh]`2 : [invert]`1 : rm :
                       imm6 : rn : rd)
              else
                 BadCode ("LogicalShiftedRegister")
           }
           case None => BadCode ("LogicalShiftedRegister")
         }
      case LogicalImmediate@32 (_, opc, s, imm, rn, rd) =>
         match EncodeBitMask (imm), EncodeLogicalOp (opc, s)
         {
           case Some (_, imms, immr), Some (opc) =>
              ARM8 ('0' : opc : '1001000' : immr : imms : rn : rd)
           case _ => BadCode ("LogicalImmediate32")
         }
      case LogicalImmediate@64 (_, opc, s, imm, rn, rd) =>
         match EncodeBitMask (imm), EncodeLogicalOp (opc, s)
         {
           case Some (N, imms, immr), Some (opc) =>
              ARM8 ('1' : opc : '100100' : N : immr : imms : rn : rd)
           case _ => BadCode ("LogicalImmediate64")
         }
      case Shift@32 (_, sh, rm, rn, rd) =>
         ARM8 ('00011010110' : rm : '0010' : [sh]`2 : rn : rd)
      case Shift@64 (_, sh, rm, rn, rd) =>
         ARM8 ('10011010110' : rm : '0010' : [sh]`2 : rn : rd)

      case MoveWide@32 (_, opc, hw, imm16, rd) =>
      {
         opc = match opc
               {
                  case MoveWideOp_N => '00'
                  case MoveWideOp_Z => '10'
                  case MoveWideOp_K => '11'
               };
         ARM8 ('0' : opc : '100101' : hw : imm16 : rd)
      }
      case MoveWide@64 (_, opc, hw, imm16, rd) =>
      {
         opc = match opc
               {
                  case MoveWideOp_N => '00'
                  case MoveWideOp_Z => '10'
                  case MoveWideOp_K => '11'
               };
         ARM8 ('1' : opc : '100101' : hw : imm16 : rd)
      }
      case BitfieldMove@32
             (sf, inzero, extend, wmask, tmask, immr, imms, rn, rd)
        or BitfieldMove@64
             (sf, inzero, extend, wmask, tmask, immr, imms, rn, rd) =>
      {
         sz = e_sf (sf);
         opc =
            match inzero, extend
            {
               case true, true   => Some ('00')
               case false, false => Some ('01')
               case true, false  => Some ('10')
               case _ => None
            };
         match opc
         {
            case Some (opc) =>
            {
               r = [immr]`6;
               s = [imms]`6;
               if immr == [r] and imms == [s] and
                  DecodeBitMasks (sz, s, r, false) == Some (wmask, tmask) then
                  ARM8 (sz : opc : '100110' : sz : r : s : rn : rd)
               else
                  BadCode ("BitfieldMove")
            }
            case None => BadCode ("BitfieldMove")
         }
      }
      case ConditionalCompareImmediate@32(sf, opc, imm, cd, (n, z, c, v), rn)
        or ConditionalCompareImmediate@64(sf, opc, imm, cd, (n, z, c, v), rn) =>
      {
         imm5 = [imm];
         if imm == [imm5] then
            ARM8 (e_sf (sf) : [opc]`1 : '111010010' : imm5 : cd : '10' : rn :
                  '0' : [n]`1 : [z]`1 : [c]`1 : [v]`1)
         else
            BadCode ("ConditionalCompareImmediate")
      }
      case ConditionalCompareRegister@32(sf, opc, cd, (n, z, c, v), rm, rn)
        or ConditionalCompareRegister@64(sf, opc, cd, (n, z, c, v), rm, rn) =>
         ARM8 (e_sf (sf) : [opc]`1 : '111010010' : rm : cd : '00' : rn :
               '0' : [n]`1 : [z]`1 : [c]`1 : [v]`1)
      case ConditionalSelect@32 (_, op, o2, cd, rm, rn, rd) =>
         ARM8 ('0' : [op]`1 : '011010100' : rm : cd : '0' : [o2]`1 : rn : rd)
      case ConditionalSelect@64 (_, op, o2, cd, rm, rn, rd) =>
         ARM8 ('1' : [op]`1 : '011010100' : rm : cd : '0' : [o2]`1 : rn : rd)
      case CountLeading@32 (_, op, rn, rd) =>
         ARM8 ('010110101100000000010' : [op]`1 : rn: rd)
      case CountLeading@64 (_, op, rn, rd) =>
         ARM8 ('110110101100000000010' : [op]`1 : rn: rd)
      case ExtractRegister@32 (_, imms, rm, rn, rd) =>
         if imms<5> then
            BadCode ("ExtractRegister32")
         else
            ARM8 ('00010011100' : rm : imms : rn : rd)
      case ExtractRegister@64 (_, imms, rm, rn, rd) =>
         ARM8 ('10010011110' : rm : imms : rn : rd)
      case Division@32 (_, o1, rm, rn, rd) =>
         ARM8 ('00011010110' : rm : '00001' : [not o1]`1 : rn : rd)
      case Division@64 (_, o1, rm, rn, rd) =>
         ARM8 ('10011010110' : rm : '00001' : [not o1]`1 : rn : rd)
      case MultiplyAddSub@32 (_, o0, rm, ra, rn, rd) =>
         ARM8 ('00011011000' : rm : [o0]`1 : ra : rn : rd)
      case MultiplyAddSub@64 (_, o0, rm, ra, rn, rd) =>
         ARM8 ('10011011000' : rm : [o0]`1 : ra : rn : rd)
      case MultiplyAddSubLong (o0, u, rm, ra, rn, rd) =>
         ARM8 ('10011011' : [not u]`1 : '01' : rm : [o0]`1 : ra : rn : rd)
      case MultiplyHigh (u, rm, rn, rd) =>
         ARM8 ('10011011' : [not u]`1 : '10' : rm : '011111' : rn : rd)
      case Reverse@32 (_, opc, rn, rd) =>
         if opc == RevOp_REV64 then
            BadCode ("Reverse32")
         else
            ARM8 ('01011010110000000000' : [opc]`2 : rn : rd)
      case Reverse@64 (_, opc, rn, rd) =>
         ARM8 ('11011010110000000000' : [opc]`2 : rn : rd)
      case FloatingPointAddSub (op, ftype, rd, rn, rm) =>
         ARM8 ('00011110' : ftype : '1' : rm : '001' : op : '10' : rn : rd)
      case FloatingPointMov (sf, ftype, opcode0, rd, rn) =>
         ARM8 (sf : '0011110' : ftype : '10011' : opcode0 : '000000' : rn : rd)
      case FloatingPointCompare (ftype, opc, rm, rn) =>
         ARM8 ('00011110' : ftype : '1' : rm : '001000' : rn : opc : '000')
   } -- e_data

word e_debug (i::Debug) =
   match (i)
   {
      case Breakpoint (imm16) => '11010100001' : imm16 : '00000'
      case DebugRestore => '11010110101111110000001111100000'
      case DebugSwitch (LL) => '11010100101' : 0`16 : '000' : LL
      case Halt (imm16) => '11010100010' : imm16 : '00000'
   }

word e_crc (i::CRCExt) =
   match (i)
   {
      case CRC@8  (_, c, rm, rn, rd) =>
         '00011010110' : rm : '010' : [c]`1 : '00' : rn : rd
      case CRC@16 (_, c, rm, rn, rd) =>
         '00011010110' : rm : '010' : [c]`1 : '01' : rn : rd
      case CRC@32 (_, c, rm, rn, rd) =>
         '00011010110' : rm : '010' : [c]`1 : '10' : rn : rd
      case CRC@64 (_, c, rm, rn, rd) =>
         '10011010110' : rm : '010' : [c]`1 : '11' : rn : rd
   }

MachineCode e_branch (i::Branch) =
   match (i)
   {
      case BranchConditional (imm, cd) =>
      {
         imm19 = imm<20:2>;
         if imm == SignExtend (imm19 : '00') then
            ARM8 ('01010100' : imm19 : '0' : cd)
         else
            BadCode ("BranchConditional")
      }
      case BranchImmediate (imm, btype) =>
      {
         imm26 = imm<27:2>;
         if imm == SignExtend (imm26 : '00') and
            btype in set {BranchType_CALL, BranchType_JMP} then
            ARM8 ([btype == BranchType_CALL]`1 : '00101' : imm26)
         else
            BadCode ("BranchImmediate")
      }
      case BranchRegister (rn, btype) =>
      {
         opc = match btype
               {
                  case BranchType_JMP  => '00'
                  case BranchType_CALL => '01'
                  case BranchType_RET  => '10'
                  case _ => '11'
               };
         if opc == '11' then
            BadCode ("BranchRegister")
         else
            ARM8 ('110101100' : opc : '11111000000' : rn : '00000')
      }
      case CompareAndBranch@32 (_, iszero, offset, rt) =>
      {
         imm19 = offset<20:2>;
         if offset == SignExtend (imm19 : '00') then
            ARM8 ('0011010' : [not iszero]`1 : imm19 : rt)
         else
            BadCode ("CompareAndBranch32")
      }
      case CompareAndBranch@64 (_, iszero, offset, rt) =>
      {
         imm19 = offset<20:2>;
         if offset == SignExtend (imm19 : '00') then
            ARM8 ('1011010' : [not iszero]`1 : imm19 : rt)
         else
            BadCode ("CompareAndBranch64")
      }
      case TestBitAndBranch@32 (_, bit_pos, bit_val, offset, rt) =>
      {
         imm14 = offset<15:2>;
         if offset == SignExtend (imm14 : '00') and not bit_pos<5> then
            ARM8 ('0011011' : [bit_val]`1 : bit_pos<4:0> : imm14 : rt)
         else
            BadCode ("TestBitAndBranch32")
      }
      case TestBitAndBranch@64 (_, bit_pos, bit_val, offset, rt) =>
      {
         imm14 = offset<15:2>;
         if offset == SignExtend (imm14 : '00') and bit_pos<5> then
            ARM8 ('1011011' : [bit_val]`1 : bit_pos<4:0> : imm14 : rt)
         else
            BadCode ("TestBitAndBranch64")
      }
   }

word e_system (i::System) =
   match (i)
   {
      case MoveSystemRegister (l, op0, op1, op2, crn, crm, rt) =>
         '1101010100' : [l]`1 : '1' : [op0 - 2]`1 : op1 : crn : crm : op2 : rt
      case MoveImmediateProcState (PSTATEField_SP, crm) =>
         '11010101000000000100' : crm : '10111111'
      case MoveImmediateProcState (PSTATEField_DAIFSet, crm) =>
         '11010101000000110100' : crm : '11011111'
      case MoveImmediateProcState (PSTATEField_DAIFClr, crm) =>
         '11010101000000110100' : crm : '11111111'
      case ExceptionReturn => '11010110100111110000001111100000'
      case SupervisorCall (imm16) => '11010100000' : imm16 : '00001'
      case HypervisorCall (imm16) => '11010100000' : imm16 : '00010'
      case SecureMonitorCall (imm16) => '11010100000' : imm16 : '00011'
      case SystemInstruction (op1, op2, crn, crm, l, rt) =>
         '1101010100' : [l]`1 : '01' : op1 : crn : crm : op2 : rt
   }

MachineCode e_LoadStoreImmediate
   (size::bits(2), regsize_word::bool, memop::MemOp, acctype::AccType,
    signed::bool, wback::bool, postindex::bool, unsigned_offset::bool,
    offset::dword, rn::reg, rt::reg) =
{
   sz = if memop == MemOp_PREFETCH then '11' else size;
   imm9 = offset<8:0>;
   imm12 = (LSR (offset, [sz]))<11:0>;
   opc = if memop == MemOp_STORE then '00'
         else if memop == MemOp_LOAD and not signed then '01'
         else '1' : [regsize_word]`1;
   if wback then
   {
      if offset == SignExtend (imm9) and acctype == AccType_NORMAL then
         ARM8 (sz : '111000' : opc : '0' : imm9 : [not postindex]`1 : '1' :
               rn : rt)
      else
         BadCode ("LoadStoreImmediate")
   }
   else if postindex then
      BadCode ("LoadStoreImmediate")
   else if unsigned_offset and offset == LSL (ZeroExtend (imm12), [sz]) and
           acctype == AccType_NORMAL then
      ARM8 (sz : '111001' : opc : imm12 : rn : rt)
   else if offset == SignExtend (imm9) then
      ARM8 (sz : '111000' : opc : '0' : imm9 : [acctype == AccType_UNPRIV]`1 :
            '0' : rn : rt)
   else
      BadCode ("LoadStoreImmediate")
}

MachineCode e_LoadStoreRegister
   (size::bits(2), regsize_word::bool, memop::MemOp, signed::bool, rm::reg,
    extend_type::ExtendType, shift::nat, rn::reg, rt::reg) =
{
   opc = if memop == MemOp_STORE then '00'
         else if memop == MemOp_LOAD and not signed then '01'
         else '1' : [regsize_word]`1;
   sz = if memop == MemOp_PREFETCH then '11' else size;
   ARM8 (sz : '111000' : opc : '1' : rm : [extend_type]`3 :
         [shift <> 0]`1 : '10' : rn : rt)
}

MachineCode e_load_store (i::LoadStore) =
   match (i)
   {
      case LoadStoreImmediate@8
             (size, regsize_word, memop, acctype, signed, wb_unknown,
              rt_unknown, wback, postindex, unsigned_offset, offset, rn, rt)
        or LoadStoreImmediate@16
             (size, regsize_word, memop, acctype, signed, wb_unknown,
              rt_unknown, wback, postindex, unsigned_offset, offset, rn, rt)
        or LoadStoreImmediate@32
             (size, regsize_word, memop, acctype, signed, wb_unknown,
              rt_unknown, wback, postindex, unsigned_offset, offset, rn, rt)
        or LoadStoreImmediate@64
             (size, regsize_word, memop, acctype, signed, wb_unknown,
              rt_unknown, wback, postindex, unsigned_offset, offset, rn, rt) =>
         e_LoadStoreImmediate
            ([size], regsize_word, memop, acctype, signed, wback, postindex,
             unsigned_offset, offset, rn, rt)
      case LoadStoreRegister@8
             (size, regsize_word, memop, signed, rm, extend_type, shift, rn, rt)
        or LoadStoreRegister@16
             (size, regsize_word, memop, signed, rm, extend_type, shift, rn, rt)
        or LoadStoreRegister@32
             (size, regsize_word, memop, signed, rm, extend_type, shift, rn, rt)
        or LoadStoreRegister@64
             (size, regsize_word, memop, signed, rm, extend_type, shift,
              rn, rt) =>
         e_LoadStoreRegister
            ([size], regsize_word, memop, signed, rm, extend_type, shift,
             rn, rt)
      case LoadLiteral@32 (_, memop, signed, offset, rt) =>
      {
         imm19 = offset<20:2>;
         opc = match memop, signed
               {
                  case MemOp_LOAD, false => Some ('00')
                  case MemOp_LOAD, true  => Some ('10')
                  case MemOp_PREFETCH, false => Some ('11')
                  case _ => None
               };
         if IsSome (opc) and offset == SignExtend (imm19 : '00') then
            ARM8 (ValOf (opc) : '011000' : imm19 : rt)
         else
            BadCode ("LoadLiteral32")
      }
      case LoadLiteral@64 (_, MemOp_LOAD, false, offset, rt) =>
      {
         imm19 = offset<20:2>;
         if offset == SignExtend (imm19 : '00') then
            ARM8 ('01011000' : imm19 : rt)
         else
            BadCode ("LoadLiteral64")
      }
      case LoadLiteral@64 (_) => BadCode ("LoadLiteral64")
      case LoadStorePair@32
             (size, memop, acctype, signed, wb_unknown, rt_unknown, wback,
              postindex, offset, rn, rt, rt2)
        or LoadStorePair@64
             (size, memop, acctype, signed, wb_unknown, rt_unknown, wback,
              postindex, offset, rn, rt, rt2) =>
      {
         sf = [size]`1;
         scale = 0n2 + [sf];
         imm7 = (LSR (offset, scale))<6:0>;
         if (sf == '1') == (Size (size) == 64) and
            memop in set {MemOp_LOAD, MemOp_STORE} and
            acctype in set {AccType_STREAM, AccType_NORMAL} and
            offset == LSL (SignExtend (imm7), scale) then
            ARM8 (sf : [signed]`1 : '10100' : [not postindex]`1 : [wback]`1 :
                  [memop == MemOp_LOAD]`1 : imm7 : rt2 : rn : rt)
         else
            BadCode ("LoadStorePair")
      }
      case LoadStoreAcquire@8
             (size, memop::MemOp, acctype::AccType, excl::bool, rn_unknown,
              rt_unknown, rs, rn, rt)
        or LoadStoreAcquire@16
             (size, memop::MemOp, acctype::AccType, excl::bool, rn_unknown,
              rt_unknown, rs, rn, rt)
        or LoadStoreAcquire@32
             (size, memop::MemOp, acctype::AccType, excl::bool, rn_unknown,
              rt_unknown, rs, rn, rt)
        or LoadStoreAcquire@64
             (size, memop::MemOp, acctype::AccType, excl::bool, rn_unknown,
              rt_unknown, rs, rn, rt) =>
      {
         sizeok = match Size(size)
                  {
                     case 8  => size == 0
                     case 16 => size == 1
                     case 32 => size == 2
                     case _  => size == 3
                  };
         if sizeok and memop in set {MemOp_LOAD, MemOp_STORE} and
            acctype in set {AccType_ORDERED, AccType_ATOMIC} then
            ARM8 ([size]`2 : '001000' : [not excl]`1 : [memop == MemOp_LOAD]`1 :
                  '0' : rs : [acctype == AccType_ORDERED] : '11111' : rn : rt)
         else
            BadCode ("LoadStoreAcquire")
      }
      case LoadStoreAcquirePair@64
             (size, memop::MemOp, acctype::AccType, rn_unknown, rt_unknown,
              rs, rn, rt, rt2)
        or LoadStoreAcquirePair@128
             (size, memop::MemOp, acctype::AccType, rn_unknown, rt_unknown,
              rs, rn, rt, rt2) =>
      {
         sizeok = size == (if Size(size) == 64 then 2 else 3);
         if sizeok and memop in set {MemOp_LOAD, MemOp_STORE} and
            acctype in set {AccType_ORDERED, AccType_ATOMIC} then
            ARM8 ([size]`2 : '0010000' : [memop == MemOp_LOAD]`1 :
                  '1' : rs : [acctype == AccType_ORDERED] : rt2 : rn : rt)
         else
            BadCode ("LoadStoreAcquirePair")
      }
   }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

MachineCode Encode (i::instruction) =
   match (i)
   {
      case Address (page, imm, rd) =>
      if page then
      {
         immlo = imm<13:12>;
         immhi = imm<32:14>;
         if SignExtend (immhi : immlo : 0`12) == imm then
            ARM8 ('1' : immlo : '10000' : immhi : rd)
         else
            BadCode ("Address")
      }
      else
      {
         immlo = imm<1:0>;
         immhi = imm<20:2>;
         if SignExtend (immhi : immlo) == imm then
            ARM8 ('0' : immlo : '10000' : immhi : rd)
         else
            BadCode ("Address")
      }
      case Data (x) => e_data (x)
      case Branch (x) => e_branch (x)
      case LoadStore (x) => e_load_store (x)
      case CRCExt (x) => ARM8 (e_crc (x))
      case Debug (x) => ARM8 (e_debug (x))
      case System (x) => ARM8 (e_system (x))
      case MemoryBarrier (opc, crm) =>
         ARM8 ('11010101000000110011' : crm : '1' : [opc]`2 : '11111')
      case ClearExclusive (crm) =>
         ARM8 ('11010101000000110011' : crm : '01011111')
      case Hint (opc) =>
         ARM8 ('110101010000001100100000' : [opc]`3 : '11111')
      case Unallocated => BadCode ("Unallocated")
      case Reserved => BadCode ("Reserved")
   }
