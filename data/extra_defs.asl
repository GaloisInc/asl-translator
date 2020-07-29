// Shadowed arithmetic operations

bits(N) BVMul(bits(N) bv1, bits(N) bv2)
    return primitive(bv1 * bv2);

integer IntMul(integer i1, integer i2)
    return primitive(i1 * i2);

integer IntMod(integer i1, integer i2)
    return primitive(i1 MOD i2);

integer IntDiv(integer i1, integer i2)
    return primitive(i1 / i2);


bits(N) integerToSBV(integer i)
    return uninterpFnN("uu_integerToSBV", 1, N, i);

integerSizeBoundS(integer i, bits(N) x)
    bits(N) y = integerToSBV(i);
    assert (x == y);
    return;

bits(M) truncate(bits(N) bv, integer M);

// Only usable on statically-known ints (i.e. bitvector lengths)
integer log2(integer i);

// The target length may be larger than hi - lo, with
// the expectation that the resulting bitvector must be
// either zero or sign-extended (according to the signed flag) to the
// target length.

bits(length) getSlice(bits(N) inbv, boolean signed, integer lo, integer hi)
    assert length <= N;
    assert length >= 1;
    assert hi >= lo;
    assert hi <= length;
    assert lo >= 0;
    assert (hi - lo) <= length;

    bits(N) bv = inbv;
    // bv = [ bv_(N-1) .. bv_hi(hi) .. bv_lo(lo) .. bv_0](N)
    if signed then
        bv = primitive_ASR(bv, lo);
        // bv = [ 1 1 .. bv_hi(hi-lo) .. bv_lo(0) ] (N)
    else
        bv = bv >> lo;
        // bv = [ 0 0 .. bv_hi(hi-lo) .. bv_lo(0) ] (N)

    // where S == 1 iff signed
    // bv = [ S S .. bv_hi(hi-lo) .. bv_lo(lo) ] (N)
    bits(N) mask = Ones(N);
    // mask = [ 1 1 .. 1 1 ] (N)
    mask = NOT (mask << length);
    // mask = [ 0 0 .. 1(length) .. 1(0) ] (N)
    bv = bv AND mask;
    // bv = [ 0 0 .. S(length) S .. bv_hi(hi - lo) .. bv_lo(0) ] (N)
    return truncate(bv, length);
    // [ S(length) S .. bv_hi(hi - lo) .. bv_lo(0) ] (length)

// The length of the input bitvector may be larger than
// the range we are setting, in which case we simply drop
// any bits above hi - lo.

bits(N) setSlice(bits(N) basebv, integer lo, integer hi, bits(length) asnbv)
    assert length <= N;
    assert length >= 1;
    assert hi >= lo;
    assert hi <= length;
    assert lo >= 0;
    assert (hi - lo) <= length;

    bits(length) bv = asnbv;
    // bv = [bv(length) .. bv_hi(hi) .. bv_0(0)](length)

    bv = bv << (length - hi);
    // bv = [ bv_hi (length) .. bv_0(length - hi) .. 0 0 ](length)

    bv = bv >> (length - hi);
    // bv = [ 0 0 .. bv_hi(hi) .. bv_0(0)](length)

    ebv = ZeroExtend(NOT(bv), N);
    // ebv = [0 0 0 .. -bv_hi(hi) .. -bv_0(0)](N)

    ebv = NOT(ebv << lo);
    // ebv = [1 1 .. bv_hi(hi + lo) .. bv_0(lo) .. 1](N)

    result = basebv AND ebv;
    // [basebv_(N-1) .. bv_hi(hi + lo) .. bv_0(lo) .. basebv_0](N)
    return result;


// Toplevel flags for execution status

boolean __AssertionFailure;
boolean __EndOfInstruction;
boolean __UndefinedBehavior;
boolean __UnpredictableBehavior;

constant boolean KeepAssertions = FALSE;

doAssert(boolean b)
    if (NOT b) && KeepAssertions then
        __AssertionFailure = TRUE;
    else
        return;


initGlobals()
    setDefaultCond();

setDefaultCond()
    if __ThisInstrEnc == __A32 || PSTATE.IT<3:0> == Zeros(4) then
        __currentCond = 0xE<3:0>;
    else
        __currentCond = PSTATE.IT<7:4>;
    return;

setCond(bits(4) cond)
    __currentCond = cond;
    return;

// de-muxing the general registers into distinct globals

type regidx = bits(4);
//array bits(32) GPRS[regidx];
bits(148) GPRS;

_R[integer n] = bits(32) value
    assert n >= 0 && n <= 14;
    bits(37) idx = integerToSBV(n);
    GPRS = uninterpFn("uf_gpr_set", GPRS, truncate(idx, 4), value);
    return;

bits(32) _R[integer n]
    assert n >= 0 && n <= 14;
    bits(37) idx = integerToSBV(n);
    return uninterpFn("uf_gpr_get", GPRS, truncate(idx, 4));

bits(32) Rmode[integer n, bits(5) mode]
    assert n >= 0 && n <= 14;
    assert mode == M32_User;
    return _R[n];

Rmode[integer n, bits(5) mode] = bits(32) value
    assert n >= 0 && n <= 14;
    assert mode == M32_User;
    _R[n] = value;

R[integer n] = bits(32) value
    if n == 15 then
        assert FALSE;
        return;
    else
        _R[n] = value;
        return;

bits(32) R[integer n]
    if n == 15 then
        return PC;
    else
        return _R[n];

bits(32) PC
    offset = (if CurrentInstrSet() == InstrSet_A32 then 8 else 4);
    return _PC + offset;

type simdidx = bits(8);
//array bits(128) SIMDS[simdidx];
bits(149) SIMDS;

_V[integer n] = bits(128) value
    assert n >= 0 && n <= 31;
    bits(37) idx = integerToSBV(n);
    SIMDS = uninterpFn("uf_simd_set", SIMDS, truncate(idx, 8), value);
    return;

bits(128) _V[integer n]
    assert n >= 0 && n <= 31;
    bits(37) idx = integerToSBV(n);
    return uninterpFn("uf_simd_get", SIMDS, truncate(idx, 8));

bits(32) _PC;

PC[] = bits(32) value
    _PC = value;
    return;

bits(32) PC[]
    return _PC;

finishInstruction()
    if !__BranchTaken then
        _PC = NextInstrAddr();

// Allow us to model the internal PC as a 32 bit value
bits(N) ThisInstrAddr()
    if N == 32 then
        return PC[];
    else
        assert FALSE;
        return bits(N) UNKNOWN;

bits(N) NextInstrAddr()
    if N == 32 then
        off = if __ThisInstrEnc == __T16 then 2 else 4;
        return (_PC + off);
    else
        assert FALSE;
        return bits(N) UNKNOWN;

// Allow us to model the internal PC as a 32 bit value
BranchToAddr(bits(N) target, BranchType branch_type)
    __BranchTaken = TRUE;
    Hint_Branch(branch_type);
    assert UsingAArch32();

    if N == 32 then
        PC[] = target;
        return;
    else
        assert FALSE;
        return;
    return;


// This flag is checked every time a function call
// might have written to it to see if we should stop
// processing the instruction early.

EndOfInstruction()
  __EndOfInstruction = TRUE;
  return;

// These are overridden in the translation to terminate
// the calling function early.

// Unlike the above flag, these are not checked on every
// function call. The resulting global state after either
// flag is tripped should be treated as undefined.

// UNDEFINED is rewritten into this
ASLSetUndefined()
  if KeepAssertions then
    __UndefinedBehavior = TRUE;
  else
    return;

// UNPREDICTABLE is rewritten into this
ASLSetUnpredictable()
  if KeepAssertions then
    __UnpredictableBehavior = TRUE;
  else
    return;

// Concretizing some IMPLEMENTATION_DEFINED blocks

// Memory model

bits(146) __Memory;

Mem_Internal_Set(bits(32) address, integer size, bits(8*size) value)
  case size of
       when 1
            __Memory = uninterpFn("write_mem_8", __Memory, address, value);
       when 2
            __Memory = uninterpFn("write_mem_16", __Memory, address, value);
       when 4
            __Memory = uninterpFn("write_mem_32", __Memory, address, value);
       when 8
            __Memory = uninterpFn("write_mem_64", __Memory, address, value);
       otherwise
            assert FALSE;
  return;

bits(8*size) Mem_Internal_Get(bits(32) address, integer size)
  case size of
       when 1
            return uninterpFn("read_mem_8", __Memory, address);
       when 2
            return uninterpFn("read_mem_16", __Memory, address);
       when 4
            return uninterpFn("read_mem_32", __Memory, address);
       when 8
            return uninterpFn("read_mem_64", __Memory, address);
       otherwise
            assert FALSE;
            return bits(8*size) UNKNOWN;

// Overriding memory access functions to short-circuit address translation

bits(8*size) MemA[bits(32) address, integer size]
    return Mem_Internal_Get(address, size);

MemA[bits(32) address, integer size] = bits(8*size) value
    Mem_Internal_Set(address, size, value);
    return;

bits(8*size) MemU_unpriv[bits(32) address, integer size]
    return Mem_Internal_Get(address, size);

MemU_unpriv[bits(32) address, integer size] = bits(8*size) value
    Mem_Internal_Set(address, size, value);
    return;

bits(8*size) MemU[bits(32) address, integer size]
    return Mem_Internal_Get(address, size);

MemU[bits(32) address, integer size] = bits(8*size) value
    Mem_Internal_Set(address, size, value);
    return;

bits(8*size) MemO[bits(32) address, integer size]
    return Mem_Internal_Get(address, size);

MemO[bits(32) address, integer size] = bits(8*size) value
    Mem_Internal_Set(address, size, value);
    return;

bits(size*8) AArch32.MemSingle[bits(32) address, integer size, AccType acctype, boolean wasaligned]
    return Mem_Internal_Get(address, size);

AArch32.MemSingle[bits(32) address, integer size, AccType acctype, boolean wasaligned] = bits(size*8) value
    Mem_Internal_Set(address, size, value);
    return;

// We model _Dclone instead using _Vclone as a simple alias to the original value of SIMDS at the start
// of the instruction.

CheckAdvSIMDEnabled()
    fpexc_check = TRUE;
    advsimd = TRUE;

    AArch32.CheckAdvSIMDOrFPEnabled(fpexc_check, advsimd);
    SIMDS_clone = SIMDS;
    return;

// Swap out _Dclone for _Vclone by inlining the D getter inside of Din

//array bits(128) SIMDS_clone[simdidx];
bits(149) SIMDS_clone;

bits(64) Din[integer n]
    assert n >= 0 && n <= 31;
    bits(37) idx = integerToSBV(n DIV 2);
    base = (n MOD 2) * 64;
    bits(128) result = uninterpFn("simd_get", SIMDS_clone, truncate(idx, 8));
    return result<base+63:base>;

// Since IsExclusiveGlobal is stubbed to be FALSE, this will always be FALSE
boolean AArch32.ExclusiveMonitorsPass(bits(32) address, integer size)
    return FALSE;

// Since MarkExclusiveVA simply asserts FALSE, this will always assert FALSE
AArch32.SetExclusiveMonitors(bits(32) address, integer size)
    assert FALSE;
    return;

// Constant lifted from mra_tools

constant integer LOG2_TAG_GRANULE=4;
constant integer TAG_GRANULE=2 ^ LOG2_TAG_GRANULE;

// Bitvector primitives

bits(N*M) Replicate(bits(N) bv)
    return Replicate(bv, M);

integer sizeOf(bits(N) bv)
    return N;


bits(width) BigEndianReverse (bits(width) value)
    assert width IN {8, 16, 32, 64, 128};
    integer half = width DIV 2;
    StaticBind(half, width DIV 2); // hint to resolve dependent type
    if width == 8 then return value;
    return BigEndianReverse(value<half-1:0>) : BigEndianReverse(value<width-1:half>);

// Shifting Overrides

// These should be semantically equivalent to the functions in
// the standard ASL spec, but have been rewritten to not require
// intermediate arbitrarily-sized bitvectors.

(bits(N), bit) LSL_C(bits(N) x, integer shift)
    assert shift > 0;
    integerSizeBoundS(shift, x);

    shift = if shift > N then N else shift;
    carry_out = x<N - shift>;
    result = LSL(x, shift);
    return (result, carry_out);

bits(N) LSL(bits(N) x, integer shift)
    assert shift >= 0;
    integerSizeBoundS(shift, x);

    shift = if shift > N then N else shift;
    if shift == 0 then
        result = x;
    else
        result = x << shift;
    return result;

(bits(N), bit) LSR_C(bits(N) x, integer shift)
    assert shift > 0;
    integerSizeBoundS(shift, x);

    shift = if shift > N then N else shift;
    carry_out = x<shift-1>;
    result = LSR(x, shift);
    return (result, carry_out);

bits(N) LSR(bits(N) x, integer shift)
    assert shift >= 0;
    integerSizeBoundS(shift, x);

    if shift == 0 then
        result = x;
    else
        result = x >> shift;
    return result;

(bits(N), bit) ASR_C(bits(N) x, integer shift)
    assert shift > 0;
    integerSizeBoundS(shift, x);

    shift = if shift > N then N else shift;
    carry_out = x<shift-1>;
    result = ASR(x, shift);
    return (result, carry_out);

bits(N) ASR(bits(N) x, integer shift)
    assert shift >= 0;
    integerSizeBoundS(shift, x);

    shift = if shift > N then N else shift;
    if shift == 0 then
        result = x;
    else
        result = primitive_ASR(x, shift);
    return result;

bits(N) UnsignedRSqrtEstimate(bits(N) operand)
    assert N IN {16,32};
    return uninterpFnN("unsignedRSqrtEstimate", 1, N, operand);

// FPCRType == bits(32)

bits(N) FPAdd(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpAdd", 1, N, op1, op2, fpcr);

boolean FPCompareUN(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpCompareUN", 1, N, op1, op2, fpcr);

bits(N) FPMin(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpMin", 1, N, op1, op2, fpcr);

bits(N) FPProcess(bits(N) input)
    assert N IN {16,32,64};
    return uninterpFnN("fpProcess", 1, N, input);

boolean FPCompareNE(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpCompareNE", 1, N, op1, op2, fpcr);

boolean FPCompareGT(bits(N) op1, bits(N) op2, FPCRType fpcr)
    // static unrolling can't figure out that 8 is invalid
    assert N IN {8,16,32,64};
    //assert N IN {16,32,64};
    return uninterpFnN("fpCompareGT", 1, N, op1, op2, fpcr);

bits(N) FPSub(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpSub", 1, N, op1, op2, fpcr);

bits(M) FPToFixed(bits(N) op, integer fbits, boolean unsigned, FPCRType fpcr, FPRounding rounding)
    assert N IN {16,32,64};
    assert M IN {16,32,64};
    assert fbits >= 0;
    assert rounding != FPRounding_ODD;
    bits(32) fbitsB = integerToSBV(fbits);
    return uninterpFnN("fpToFixed", 2, N, M, op, fbitsB, unsigned, fpcr, rounding);

bits(N) FixedToFP(bits(M) op, integer fbits, boolean unsigned, FPCRType fpcr, FPRounding rounding)
    assert N IN {16,32,64};
    assert M IN {16,32,64};
    assert fbits >= 0;
    assert rounding != FPRounding_ODD;
    bits(32) fbitsB = integerToSBV(fbits);
    return uninterpFnN("fixedToFP", 2, M, N, op, fbitsB, unsigned, fpcr, rounding);

bits(N) FPRecpX(bits(N) op, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpRecpX", 1, N, op, fpcr);

bits(N) FPMul(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpMul", 1, N, op1, op2, fpcr);

bits(N) FPRecipStep(bits(N) op1, bits(N) op2)
    assert N IN {16,32};
    return uninterpFnN("fpRecipStep", 1, N, op1, op2);

bits(N) FPMulAddH(bits(N) addend, bits(M) op1, bits(M) op2, FPCRType fpcr)
    assert N IN {32,64};
    assert M == (N DIV 2);
    return uninterpFnN("fpMulAddH", 1, N, op1, op2, fpcr);

bits(N) FPMinNum(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpMinNum", 1, N, op1, op2, fpcr);

bits(N) FPMax(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpMax", 1, N, op1, op2, fpcr);

bits(N) FPMaxNum(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpMaxNum", 1, N, op1, op2, fpcr);

bits(N) FPScale(bits (N) op, integer scale, FPCRType fpcr)
    assert N IN {16,32,64};
    bits(32) scaleB = integerToSBV(scale);
    return uninterpFnN("fpScale", 1, N, op, scaleB, fpcr);

bits(N) FPRoundIntN(bits(N) op, FPCRType fpcr, FPRounding rounding, integer intsize)
    assert rounding != FPRounding_ODD;
    assert N IN {16,32,64};
    bits(32) intsizeB = integerToSBV(intsize);
    return uninterpFnN("fpRoundIntN", 1, N, op, fpcr, rounding, intsizeB);

bits(4) FPCompare(bits(N) op1, bits(N) op2, boolean signal_nans, FPCRType fpcr)
    assert N IN {16,32,64};    
    return uninterpFnN("fpCompare", 1, N, op1, op2, signal_nans, fpcr);

boolean FPCompareGE(bits(N) op1, bits(N) op2, FPCRType fpcr)
    // static unrolling can't figure out that 8 is invalid
    assert N IN {8,16,32,64};
    //assert N IN {16,32,64};
    return uninterpFnN("fpCompareGE", 1, N, op1, op2, fpcr);

bits(N) FPRSqrtStepFused(bits(N) op1, bits(N) op2)
    assert N IN {16, 32, 64};    
    return uninterpFnN("fprSqrtStepFused", 1, N, op1, op2);

boolean FPCompareEQ(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};   
    return uninterpFnN("fpCompareEQ", 1, N, op1, op2, fpcr);

bits(N) FPRecipEstimate(bits(N) operand, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpRecipEstimate", 1, N, operand, fpcr);

bits(N) FPSqrt(bits(N) op, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpSqrt", 1, N, op, fpcr);

bits(M) FPConvert(bits(N) op, FPCRType fpcr, FPRounding rounding)
    assert M IN {16,32,64};
    assert N IN {16,32,64};   
    return uninterpFnN("fpConvert", 2, N, M, op, fpcr, rounding);

bits(N) FPDiv(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpDiv", 1, N, op1, op2, fpcr);

bits(N) FPRSqrtEstimate(bits(N) operand, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpSqrtEstimate", 1, N, operand, fpcr);

bits(N) FPTrigSMul(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpTrigSMul", 1, N, op1, op2, fpcr);

bits(N) FPHalvedSub(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpHalvedSub", 1, N, op1, op2, fpcr);

bits(N) FPRSqrtStep(bits(N) op1, bits(N) op2)
    assert N IN {16,32};
    return uninterpFnN("fprSqrtStep", 1, N, op1, op2);

bits(N) FPMulAdd(bits(N) addend, bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpMulAdd", 1, N, addend, op1, op2, fpcr);

bits(N) FPRecipStepFused(bits(N) op1, bits(N) op2)
    assert N IN {16, 32, 64};
    return uninterpFnN("fpRecipStepFused", 1, N, op1, op2);

bits(32) FPToFixedJS(bits(64) op, FPCRType fpcr, boolean Is64)
    return uninterpFn("fpToFixedJS", op, fpcr, Is64);

bits(N) FPMulX(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert N IN {16,32,64};
    return uninterpFnN("fpMulX", 1, N, op1, op2, fpcr);

bits(N) FPRoundInt(bits(N) op, FPCRType fpcr, FPRounding rounding, boolean exact)
    assert rounding != FPRounding_ODD;
    assert N IN {16,32,64};
    return uninterpFnN("fpRoundInt", 1, N, op, fpcr, rounding, exact);


// We assume that the MMU is disabled and that general address translation
// is not going to occur. These functions appear to be too complex to translate.

TLBRecord AArch64.TranslationTableWalk(bits(52) ipaddress, bit s1_nonsecure, bits(64) vaddress,
                                       AccType acctype, boolean iswrite, boolean secondstage,
                                       boolean s2fs1walk, integer size)
  assert FALSE;
  TLBRecord result;
  return result;

TLBRecord AArch32.TranslationTableWalkLD(bits(40) ipaddress, bits(32) vaddress,
                                         AccType acctype, boolean iswrite, boolean secondstage,
                                         boolean s2fs1walk, integer size)
  assert FALSE;
  TLBRecord result;
  return result;

TLBRecord AArch32.TranslationTableWalkSD(bits(32) vaddress, AccType acctype, boolean iswrite,
                                         integer size)
  assert FALSE;
  TLBRecord result;
  return result;

// Misc stubs for system and debug functions

DCPSInstruction(bits(2) target_el)
    return;

ConsumptionOfSpeculativeDataBarrier()
    return;

SpeculativeStoreBypassBarrierToPA()
    return;

SpeculationBarrier()
    return;

SpeculativeStoreBypassBarrierToVA()
    return;

SynchronizeErrors()
    return;

bits(64) AArch64.SysRegRead(integer op0, integer op1, integer crn, integer crm, integer op2)
    assert FALSE;
    reg = bits(64) UNKNOWN;
    return reg;

ReservedEncoding()
    return;

boolean IsPhysicalSErrorPending()
    ret = boolean UNKNOWN;
    return ret;

(boolean,boolean) AArch32.BreakpointValueMatch(integer n, bits(32) vaddress, boolean linked_to)
  return (FALSE, FALSE);

boolean AArch64.BreakpointValueMatch(integer n, bits(64) vaddress, boolean linked_to)
  return FALSE;

boolean IsBlockDescriptorNTBitValid()
  return FALSE;

bits(11) LSInstructionSyndrome()
  assert FALSE;
  ret = bits(11) UNKNOWN;
  return ret;

TraceSynchronizationBarrier()
  assert FALSE;
  return;

__abort()
  assert FALSE;
  return;

boolean AArch32.WatchpointMatch(integer n, bits(32) vaddress, integer size, boolean ispriv,
                                 boolean iswrite)
  return FALSE;

boolean AArch64.WatchpointMatch(integer n, bits(64) vaddress, integer size, boolean ispriv,
                                AccType acctype, boolean iswrite)
  return FALSE;

bits(N) Align(bits(N) x, integer y)
    case y of
        when 4
            x = x >> 2;
            x = x << 2;
            return x;
        when 8
            x = x >> 3;
            x = x << 3;
            return x;
        when 16
            x = x >> 4;
            x = x << 4;
            return x;
        otherwise
            return Align(UInt(x), y)<N-1:0>;
