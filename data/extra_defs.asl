// Shadowed arithmetic operations

bits(N) BVMul(bits(N) bv1, bits(N) bv2)
    return primitive(bv1 * bv2);

integer IntMul(integer i1, integer i2)
    return primitive(i1 * i2);

integer IntMod(integer i1, integer i2)
    return primitive(i1 MOD i2);

integer IntDiv(integer i1, integer i2)
    return primitive(i1 / i2);

// Undefined values. UNKNOWN actually loops back to just calling these, so
// we need to tie this off somewhere.

bits(N) UNDEFINED_bitvector()
    return bits(N) UNKNOWN;

integer UNDEFINED_integer()
    return integer UNKNOWN;

boolean UNDEFINED_boolean()
    return boolean UNKNOWN;

array [0..0] of bits(N) UNDEFINED_IntArray()
    return array [0..0] of bits(N) UNKNOWN;

// Defining slicing with primitive bitvector operations

bits(M) truncate(bits(N) bv, integer M);

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


// de-muxing the general registers into distinct globals

type GPRStruct is (
  bits(32) R0,
  bits(32) R1,
  bits(32) R2,
  bits(32) R3,
  bits(32) R4,
  bits(32) R5,
  bits(32) R6,
  bits(32) R7,
  bits(32) R8,
  bits(32) R9,
  bits(32) R10,
  bits(32) R11,
  bits(32) R12,
  bits(32) R13,
  bits(32) R14
)

GPRStruct GPRS;

demuxRSet(integer n, bits(32) value)
    case n of
        when 0
            GPRS.R0 = value;
        when 1
            GPRS.R1 = value;
        when 2
            GPRS.R2 = value;
        when 3
            GPRS.R3 = value;
        when 4
            GPRS.R4 = value;
        when 5
            GPRS.R5 = value;
        when 6
            GPRS.R6 = value;
        when 7
            GPRS.R7 = value;
        when 8
            GPRS.R8 = value;
        when 9
            GPRS.R9 = value;
        when 10
            GPRS.R10 = value;
        when 11
            GPRS.R11 = value;
        when 12
            GPRS.R12 = value;
        when 13
            GPRS.R13 = value;
        when 14
            GPRS.R14 = value;
    return;

bits(32) demuxRGet(integer n)
    case n of
        when 0
            return GPRS.R0;
        when 1
            return GPRS.R1;
        when 2
            return GPRS.R2;
        when 3
            return GPRS.R3;
        when 4
            return GPRS.R4;
        when 5
            return GPRS.R5;
        when 6
            return GPRS.R6;
        when 7
            return GPRS.R7;
        when 8
            return GPRS.R8;
        when 9
            return GPRS.R9;
        when 10
            return GPRS.R10;
        when 11
            return GPRS.R11;
        when 12
            return GPRS.R12;
        when 13
            return GPRS.R13;
        when 14
            return GPRS.R14;

_R[integer n] = bits(32) value
    assert n >= 0 && n <= 14;
    demuxRSet(n, value);

bits(32) _R[integer n]
    assert n >= 0 && n <= 14;
    return demuxRGet(n);

// de-muxing the vector registers into distinct globals

type SIMDStruct is (
  bits(128) V0,
  bits(128) V1,
  bits(128) V2,
  bits(128) V3,
  bits(128) V4,
  bits(128) V5,
  bits(128) V6,
  bits(128) V7,
  bits(128) V8,
  bits(128) V9,
  bits(128) V10,
  bits(128) V11,
  bits(128) V12,
  bits(128) V13,
  bits(128) V14,
  bits(128) V15,
  bits(128) V16,
  bits(128) V17,
  bits(128) V18,
  bits(128) V19,
  bits(128) V20,
  bits(128) V21,
  bits(128) V22,
  bits(128) V23,
  bits(128) V24,
  bits(128) V25,
  bits(128) V26,
  bits(128) V27,
  bits(128) V28,
  bits(128) V29,
  bits(128) V30,
  bits(128) V31
)

SIMDStruct SIMD;

demuxVSet(integer n, bits(128) value)
    case n of
        when 0
            SIMD.V0 = value;
        when 1
            SIMD.V1 = value;
        when 2
            SIMD.V2 = value;
        when 3
            SIMD.V3 = value;
        when 4
            SIMD.V4 = value;
        when 5
            SIMD.V5 = value;
        when 6
            SIMD.V6 = value;
        when 7
            SIMD.V7 = value;
        when 8
            SIMD.V8 = value;
        when 9
            SIMD.V9 = value;
        when 10
            SIMD.V10 = value;
        when 11
            SIMD.V11 = value;
        when 12
            SIMD.V12 = value;
        when 13
            SIMD.V13 = value;
        when 14
            SIMD.V14 = value;
        when 15
            SIMD.V15 = value;
        when 16
            SIMD.V16 = value;
        when 17
            SIMD.V17 = value;
        when 18
            SIMD.V18 = value;
        when 19
            SIMD.V19 = value;
        when 20
            SIMD.V20 = value;
        when 21
            SIMD.V21 = value;
        when 22
            SIMD.V22 = value;
        when 23
            SIMD.V23 = value;
        when 24
            SIMD.V24 = value;
        when 25
            SIMD.V25 = value;
        when 26
            SIMD.V26 = value;
        when 27
            SIMD.V27 = value;
        when 28
            SIMD.V28 = value;
        when 29
            SIMD.V29 = value;
        when 30
            SIMD.V30 = value;
        when 31
            SIMD.V31 = value;
    return;


bits(128) demuxVGet(integer n)
    case n of
        when 0
            return SIMD.V0;
        when 1
            return SIMD.V1;
        when 2
            return SIMD.V2;
        when 3
            return SIMD.V3;
        when 4
            return SIMD.V4;
        when 5
            return SIMD.V5;
        when 6
            return SIMD.V6;
        when 7
            return SIMD.V7;
        when 8
            return SIMD.V8;
        when 9
            return SIMD.V9;
        when 10
            return SIMD.V10;
        when 11
            return SIMD.V11;
        when 12
            return SIMD.V12;
        when 13
            return SIMD.V13;
        when 14
            return SIMD.V14;
        when 15
            return SIMD.V15;
        when 16
            return SIMD.V16;
        when 17
            return SIMD.V17;
        when 18
            return SIMD.V18;
        when 19
            return SIMD.V19;
        when 20
            return SIMD.V20;
        when 21
            return SIMD.V21;
        when 22
            return SIMD.V22;
        when 23
            return SIMD.V23;
        when 24
            return SIMD.V24;
        when 25
            return SIMD.V25;
        when 26
            return SIMD.V26;
        when 27
            return SIMD.V27;
        when 28
            return SIMD.V28;
        when 29
            return SIMD.V29;
        when 30
            return SIMD.V30;
        when 31
            return SIMD.V31;

_V[integer n] = bits(128) value
    assert n >= 0 && n <= 31;
    demuxVSet(n, value);

bits(128) _V[integer n]
    assert n >= 0 && n <= 31;
    return demuxVGet(n);


bits(32) _PC;

PC[] = bits(32) value
    _PC = value;
    return;

bits(32) PC[]
    return _PC;

//Consistent treatment for GPRs and PC
bits(32) RGen[integer n]
    if n == 15 then
        return _PC;
    else
        return R[n];

RGen[integer n] = bits(32) value
    if n == 15 then
        _PC = value;
    else
        R[n] = value;

// Allow us to model the internal PC as a 32 bit value
bits(N) ThisInstrAddr()
    if N == 32 then
        return PC[];
    else
        assert FALSE;
        return bits(N) UNKNOWN;

bits(N) NextInstrAddr()
    if N == 32 then
        return (_PC + (ThisInstrLength() DIV 8))<N-1:0>;
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
  __UndefinedBehavior = TRUE;
  return;

// UNPREDICTABLE is rewritten into this
ASLSetUnpredictable()
  __UnpredictableBehavior = TRUE;
  return;

// Memory model

__RAM(32) __Memory;

// Fake functions used for globals collection.
// To be overridden by the translator

Mem_Internal_Set(bits(32) address, integer size, bits(8*size) value)
  __Memory[address] = bits(8) UNKNOWN;
  return;

bits(8*size) Mem_Internal_Get(bits(32) address, integer size)
  bits(8) somebit = __Memory[address];
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
    shift = if shift > N then N else shift;
    carry_out = x<N - shift>;
    result = LSL(x, shift);
    return (result, carry_out);

bits(N) LSL(bits(N) x, integer shift)
    assert shift >= 0;
    shift = if shift > N then N else shift;
    if shift == 0 then
        result = x;
    else
        result = x << shift;
    return result;

(bits(N), bit) LSR_C(bits(N) x, integer shift)
    assert shift > 0;
    shift = if shift > N then N else shift;
    carry_out = x<shift-1>;
    result = LSR(x, shift);
    return (result, carry_out);

bits(N) LSR(bits(N) x, integer shift)
    assert shift >= 0;
    if shift == 0 then
        result = x;
    else
        result = x >> shift;
    return result;

(bits(N), bit) ASR_C(bits(N) x, integer shift)
    assert shift > 0;
    shift = if shift > N then N else shift;
    carry_out = x<shift-1>;
    result = ASR(x, shift);
    return (result, carry_out);

bits(N) ASR(bits(N) x, integer shift)
    assert shift >= 0;
    shift = if shift > N then N else shift;
    if shift == 0 then
        result = x;
    else
        result = primitive_ASR(x, shift);
    return result;

// FIXME: This can't reasonably be simulated

integer RecipSqrtEstimate(integer a)
  assert FALSE;
  return integer UNKNOWN;

// Stubbed floating point operations to allow proper signature calculations

bits(N) FPAdd(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

boolean FPCompareUN(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return boolean UNKNOWN;

bits(N) FPMin(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPProcess(bits(N) input)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPTwo(bit sign)
    assert FALSE;
    return bits(N) UNKNOWN;

boolean FPCompareNE(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return boolean UNKNOWN;

bits(N) FPMinNormal(bit sign)
    assert FALSE;
    return bits(N) UNKNOWN;

boolean FPCompareGT(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return boolean UNKNOWN;

bits(N) FPSub(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(M) FPToFixed(bits(N) op, integer fbits, boolean unsigned, FPCRType fpcr, FPRounding rounding)
    assert FALSE;
    return bits(M) UNKNOWN;

bits(N) FixedToFP(bits(M) op, integer fbits, boolean unsigned, FPCRType fpcr, FPRounding rounding)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPRecpX(bits(N) op, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPMul(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPRecipStep(bits(N) op1, bits(N) op2)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPMulAddH(bits(N) addend, bits(M) op1, bits(M) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPMinNum(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPMax(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPMaxNum(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPScale(bits (N) op, integer scale, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPRoundIntN(bits(N) op, FPCRType fpcr, FPRounding rounding, integer intsize)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(4) FPCompare(bits(N) op1, bits(N) op2, boolean signal_nans, FPCRType fpcr)
    assert FALSE;
    return bits(4) UNKNOWN;

boolean FPCompareGE(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return boolean UNKNOWN;

bits(N) FPRSqrtStepFused(bits(N) op1, bits(N) op2)
    assert FALSE;
    return bits(4) UNKNOWN;

boolean FPCompareEQ(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return boolean UNKNOWN;

(boolean, bits(N)) FPProcessNaNs3(FPType type1, FPType type2, FPType type3,
                                  bits(N) op1, bits(N) op2, bits(N) op3,
                                  FPCRType fpcr)
    assert FALSE;
    return (boolean UNKNOWN, bits(N) UNKNOWN);

bits(N) FPRecipEstimate(bits(N) operand, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPSqrt(bits(N) op, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(M) FPConvert(bits(N) op, FPCRType fpcr, FPRounding rounding)
    assert FALSE;
    return bits(M) UNKNOWN;

bits(M) FPConvert(bits(N) op, FPCRType fpcr)
    assert FALSE;
    return bits(M) UNKNOWN;

bits(M) FPConvertSVE(bits(N) op, FPCRType fpcr, FPRounding rounding)
    assert FALSE;
    return bits(M) UNKNOWN;

bits(M) FPConvertSVE(bits(N) op, FPCRType fpcr)
    assert FALSE;
    return bits(M) UNKNOWN;

bits(N) FPDiv(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPRSqrtEstimate(bits(N) operand, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPTrigSMul(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPHalvedSub(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPRSqrtStep(bits(N) op1, bits(N) op2)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPMulAdd(bits(N) addend, bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPRecipStepFused(bits(N) op1, bits(N) op2)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPToFixedJS(bits(M) op, FPCRType fpcr, boolean Is64)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPMulX(bits(N) op1, bits(N) op2, FPCRType fpcr)
    assert FALSE;
    return bits(N) UNKNOWN;

bits(N) FPRoundInt(bits(N) op, FPCRType fpcr, FPRounding rounding, boolean exact)
    assert FALSE;
    return bits(N) UNKNOWN;


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

