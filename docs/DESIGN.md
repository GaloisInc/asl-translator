# Introduction

This document details the architecture of the asl translator, as well as
detailing some of the design decisions that were made and the technical
challenges that were encountered during its development.

The goal of this translator is to convert the imperative-style code from
the [Arm Architecture Specification Language (ASL)][fn:asl-description] into
a closed-form [What4][fn:what4] function in order to serve as the formal semantics
for the AArch32 architecture for the purpose of perform binary analysis on
compiled executables.

This document outlines some of the key technical challenges addressed by 
the translator

# Architecture
The ASL translator provides a formal semantics to the ASL specification from
[mra-tools][fn:mra_tools] using symbolic execution with
[Crucible][fn:crucible]. These semantics (given as serialized [What4][fn:what4]
functions) are then used by [semmc][fn:semmc] to create an architecture
instantiation for AArch32.

```
    +--------------+  mra_tools  +----------+
    |              |             |          |
    | ARM-XML Spec +----+------->+ ASL Spec |
    |              |    |        |          |
    +------+-------+    |        +-----+----+
           |            |              |
           | Dismantle  |              | asl-parser
           v            |              v
    +------+-------+    |     +--------+--------+
    |              |    |     |                 |
    | Disassembler |    |     | Parsed ASL Spec |
    |              |    |     | (s-expressions) |
    +--------------+    |     |                 |
                        |     +--+-------+------+
                        v        |       |
 +----------------------+--+     |       |
 |                         |     |       | asl-translator
 |     aslEncodingMap      +<----+       |
 |(Opcode -> ASL Encoding) |             |
 |                         |        +----+--------------+
 +------------+------------+        |                   |
              |                     |   ARM semantics   |
              v                     | (what4 functions) |
+-------------+------------+        |                   |
|                          |        +-------+-----------+
|      ARM semantics       |                |
| (Parameterized Formulas) +<---------------+
|                          |
+--------------------------+       semmc-asl
```
# ASL Translation Pipeline
The `asl-translation-exec` executable (`./exe/Main.hs`) and driver library (`Language.ASL.Translation.Driver`) 
implements the pipeline to transform the parsed ASL specification into formal semantics (as a collection
of What4 functions). Translation proceeds as follows:

1. Read in the parsed ASL specification.
2. Preprocess the ASL AST, performing rewrites and calculating function signatures.
3. Translate an ARM instruction from ASL into a Crucible CFG, noting any function calls.
4. For each called function, translate from ASL into a Crucible CFG, noting any function calls.
5. Repeat step 4 until all functions have been translated.
6. Symbolically execute each Crucible CFG into a What4 function.
7. Repeat 3-6 for each AArch32 instruction.
8. Serialize all What4 functions into s-expressions.

After translation, the specification is _normalized_ to have the required shape for
the rest of the binary analysis toolsuite. Normalization reads back in the serialized
formulas and writes out the final normalized formulas which are used by `semmc`.


```
   +-----------------+
   |                 |
   | Parsed ASL Spec |
   |                 |
   +--------+--------+
            |
            |  Preprocessing
            |
            |  * Language.ASL.Preprocess
            |  * Language.ASL.SyntaxTraverse
            |  * Language.ASL.StaticExpr
            v
+-----------+-------------+
|                         | * Language.ASL.Signature.SimpleFunctionSignature
|  Preprocessed ASL Spec  | * Language.ASL.Signature.SomeInstructionSignature
|                         |
+-----------+-------------+
            |
            |  Translation
            |
            |  * Language.ASL.Translation
            |  * Language.ASL.Crucible
            |  * Language.ASL.Globals
            v
    +-------+-------+
    |               | * Language.ASL.Function
    | Crucible CFGs | * Language.ASL.Instruction
    |               | * Language.ASL.Signature.FunctionSignature
    +-------+-------+
            |
            |  Symbolic Execution
            |
            |  * Language.ASL
            v
   +--------+--------+
   |                 |
   |  ASL Semantics  | * What4.ExprSymFn
   |                 |
   +--------+--------+
            |
            |  Serialization
            |
            |  * Language.ASL.Formulas.Serialize
            |  * What4.Serialize.Printer
            |
    +-------+-------+
    |               |
    |  Serialized   | * Data.SCargot.SExpr
    | ASL Semantics |
    |               |
    +-------+-------+
            |
            |  Normalization
            |  * Language.ASL.Formulas.Normalize
            |  * Language.ASL.Formulas.Serialize
            |  * What4.Serialize.Parser
            v
    +-------+-------+
    |               |
    |  Normalized   | * Data.SCargot.SExpr
    | ASL Semantics |
    |               |
    +---------------+
```


# Preprocessing

Preprocessing transforms the ASL AST into a semantically equivalent AST, but
with a simplified representation in order to ease translation. Additionally, it
computes necessary static information about the ASL specification, such as function
signatures and user-defined types.

## Getters/Setters

One syntactic transformation performed during preprocessing is rewriting ASL
_getters_ and _setters_ into standard function calls. For example, the `S`
getter is defined as follows:

```
bits(32) S[integer n]
    assert n >= 0 && n <= 31;
    base = (n MOD 4) * 32;
    return _V[n DIV 4]<base+31:base>;
```
And the setter is has a similar corresponding definition:
```
S[integer n] = bits(32) value
    assert n >= 0 && n <= 31;
    base = (n MOD 4) * 32;
    _V[n DIV 4]<base+31:base> = value;
    return;
```
Preprocessing rewrites these into standard function calls:
```
bits(32) S_GETTER(integer n)
    assert n >= 0 && n <= 31;
    base = (n MOD 4) * 32;
    return _V[n DIV 4]<base+31:base>;
    
S_SETTER(integer n, bits(32) value)
    assert n >= 0 && n <= 31;
    base = (n MOD 4) * 32;
    _V[n DIV 4]<base+31:base> = value;
    return;
```

In most cases rewriting uses of getters and setters is straightforward. e.g. `x
= S[n]` becomes `x = S_GETTER(n)` and `S[n] = x` becomes `S_SETTER(n, x)`.
However, a combination getter/setter is required for calculating a slice
assignment. e.g. `S[n]<2:1> = x;` is rewritten into the following block of
statements:

```
s = S_GETTER(n);
s<2:1> = x;
S_SETTER(n, s);

```

## Function Signatures

Preprocessing also computes a signature for each function, which is
used during translation. A signature specifies the natural
arguments and natural return type for a function, but also the
set of _global reads_ and _global writes_ that a function may perform.

In the above example, both `S_GETTER` and `S_SETTER` access the
global variable `_V` (representing the vector registers), which can
be calculated by a simple syntacic analysis. The `GlobalReads` and
`GlobalWrites` of each are calculated as follows:

* `GlobalReads(S_GETTER) = {_V}`
* `GlobalWrites(S_GETTER) = {}`
* `GlobalReads(S_SETTER) = {_V}`
* `GlobalWrites(S_SETTER) = {_V}`

Note that `S_SETTER` has `_V` in its `GlobalReads` set, as every write
implies a potential read.


## Types

An equivalent Crucible type is required to represent each ASL type. For the most part
this is a straightforward one-to-one translation, with some notable exceptions:

* ASL enumeration types are transformed into an equivalent bitvector representation
* ASL struct types have named fields, requiring additional `ExtendedTypeData` in order
to retain the association between field names and their struct index.
* ASL system registers are treated as both raw bitvectors as well as structs
(with named slices), requiring additional `ExtendedTypeData` to resolve a struct
field into a bitvector slice.
* Crucible bitvectors are polymorphic and dependently typed in their width
(i.e. their width may be a variable that is the result of some computation). In
contrast, Crucible bitvectors must have a fixed and statically-known width. To resolve
this, the translator produces multiple _monomorphized_ copies of polymorphic functions.
In some cases, code blocks must be copied into multiple monomorphized variants.

## Monomorphization

Polymorphic and dependently-typed bitvectors in ASL are a significant source of
complexity when translating into Crucible, which requires that all bitvector
widths be statically-known. To address this, the signature calculation for each
function is divided into two stages: _simple_ and _monomorphized_. Each ASL
function corresponds to a `SimpleFunctionSignature`, which is calculated during
preprocessing.  In a `SimpleFunctionSignature`, the function arguments and
return type are represented as (variable-width bitvector) ASL types.

During the translation of some ASL function or instruction, the
`SimpleFunctionSignature` for each called function is unified against the
_concrete_ bitvector widths given as arguments. These concrete widths are then
used to compute a _monomorphic_ `FunctionSignature`, with Crucible types for the
function arguments and return type. With the bitvector width concretized, each monomorphic
variant of a function is independently translated into Crucible with a distinct identifier.
A single `SimpleFunctionSignature` may therefore result in multiple `FunctionSignature`s
depending on how the function is used.

For example, the following ASL function reverses the bits of any bitvector:

```
bits(N) BitReverse(bits(N) data)
    bits(N) result;
    for i = 0 to N-1
        result<N-i-1> = data<i>;
    return result;
```

This function is called by the `CRC32_A` instruction with the contents of some GPR.

```
acc = R[n]; 
tempacc = BitReverse(acc):Zeros(size);
```

Since `R[n]` is known to return a `bits(32)`, during translation we know that the
variable `acc` is 32 bits wide and can then translate a copy of `BitReverse` where
`N` is 32.

```
bits(32) BitReverse_N_32(bits(32) data)
    bits(32) result;
    for i = 0 to 32-1
        result<32-i-1> = data<i>;
    return result;
```

In this case, this also provides an upper bound on the `for` loop which allows it to be unrolled.

Concretizing bitvector widths is not always this straightforward, as a bitvector may be the
result of some _slice_. In the same `CRC32_A` instruction we see `BitReverse` called with a bitvector
slice whose width cannot be statically computed.

```
_field sz 4 +: 2
...
size = 8 << UInt(sz);
if size == 64 then UNPREDICTABLE;
...
val = R[m]<size-1:0>;
tempval = BitReverse(val):Zeros(32);
```

In this case, the width of `val` is the result of the `sz` operand to the
instruction and is therefore not statically known. To resolve this, we require
some lightweight static analysis on the instruction body in order to compute
possible values for `size`. This is handled by the `Language.ASL.StaticExpr`
module, which determines that `sz` may be `00` `01` or `10`, while excluding
`11` as a valid assignment as it would result in a `size` of 64 and hit the
`UNPREDICTABLE` error case.

The instruction body is then rewritten during preprocessing with a copy for each
valid assignment of `sz`:

```
_field sz 4 +: 2

case sz of
    when '00'
        size = 8;
        ...
        val = R[m]<7:0>;
        tempval = BitReverse(val):Zeros(32);
        ...
    when '01'
        size = 16;
        ...
        val = R[m]<15:0>;
        tempval = BitReverse(val):Zeros(32);
        ...
    when '10'
        size = 32;
        ...
        val = R[m]<31:0>;
        tempval = BitReverse(val):Zeros(32);
        ...
```

In each of these cases `val` now has a statically-known width, and translating
each call to `BitReverse` will result in a monomorphized copy
(i.e. `BitReverse_N_8`, `BitReverse_N_16` and `BitReverse_N_32`).

# Translation

Translation is the core functionality of the ASL translator - taking
preprocessed ASL syntax with function signatures, and producing
a Crucible control flow graph representing its execution semantics.
Most of the complexity in this transformation arises from variable-width
and dependently-typed bitvector widths, as well as representing the
ASL global state.

Translation occurs primarily via a wrapped `Crucible.CFG.Generator` monad
defined in `Language.ASL.Translation`, which adds modified error handling and
logging behavior to the original generator. The state of the translation
is defined by `Language.ASL.TranslationState` which includes intermediate
information about the current translation context (e.g. local variables),
the current function (e.g. function arguments), and the global ASL environment
(e.g. in-scope callable functions).

An ASL function (or instruction) is a sequence of _statements_
(`Language.ASL.Syntax.Stmt`) which are mostly standard elements of any
imperative language: function calls, variable assignments, for-loops,
if-then-else blocks, etc. A statement may contain zero or more _expression_s
(`Language.ASL.Syntax.Expr`) as subcomponents: arithmetic, literal values,
struct accesses, value comparison, functions, etc. Translation proceeds by
simply converting each ASL statement in order into a `Generator` action, and
each ASL expression into an appropriately-typed `Atom`.

The result of translation is a Crucible `Crucible.CFG.Core.CFG` via
`Language.ASL.Crucible` with either `functionToCrucible` or
`instructionToCrucible`. The result is wrapped in either a `Function` or
`Instruction`, which contains information about the intended type signature for
the What4 function that will be used to represent the semantics of the given ASL
element.

Additionally, translation produces a set of function dependencies for the given
instruction or function. These dependencies are each a monomorphized
specialization of some ASL function, which was unified against a concrete
calling context during translation. The `Language.ASL.Driver` checks the new
dependencies against the set of already-translated functions, and translates any
additional functions as needed.

Notably, this implies that ASL functions are translated on-demand, driven at the
top-level by the translation of some instruction. The overrides in
`extra_defs.asl` and `Language.ASL.Translation.Overrides` restrict the set of
possible code paths by concretizing pieces of the ASL global state or providing
replacements for some functions. This effectively reduces the set of functions
which are required to be translated. The output of the translator is therefore
not necessarily every function in `arm_defs.asl`, but rather a subset of those
functions which are required for the specific Aarch32 semantics that we are
modelling.


## Global State

Similar to most imperative languages, ASL allows functions to refer to
globally-scoped variables whose value is expected to persist across function
calls (and between instruction executions, in this case). In ASL global state is
used to represent the processor state, various execution flags, as well as
general-purpose registers, the program counter, etc.

During preprocessing, the global reads and writes for each ASL function and
instruction are calculated as part of their signature. Turing translation,
global _reads_ are put in scope as bound variables, which can be modified like
any other local variable. As the final step of translation, the final value of
all possible global _writes_ are combined with the _natural_ return value of the
function into a struct representing all of the function effects.

```
+--------------------+  +--------------+
| Function Arguments |  | Global Reads |
+---------+----------+  +-------+------+
          |                      |
          +-----------+----------+
                      |
                      v
              +-------+------+
              | Crucible CFG |
              +-------+------+
                      |
                      v
 +--------------------+------------------+
 | +-----------------+ +---------------+ |
 | | Function Return | | Global Writes | |
 | +-----------------+ +---------------+ |
 +---------------------------------------+
```

## Function Calls

During translation, function calls are represented as explicit _uninterpreted_
functions, whose signature is calculated by taking the `SimpleFunctionSignature`
of the function name and unifying its formal arguments against the types of the
given arguments. The resulting binding environment is then paired with the
function name and recorded as a function call, noting it as a dependency that
will be translated later.

After unification, we create an uninterpreted function with the appropriate
signature, and with a name that will allow us to later associate it with its
translated semantics.  The function signature tells us which global variables to
provide to the function (i.e. its global reads), and what global variables may
have been modified after its execution (i.e. its global writes). We collect 
the global reads from the current register state of the CFG and package them
into a single struct. This is passed to the uninterpreted function, along with
its natural arguments. The output of the uninterpreted function is then
unpacked into its natural return value, as well as the resulting set of 
global writes. Each global write is then assigned to the corresponding register
state of the CFG, and the natural return value is finally given as the value
of the function evaluation.

```
+-------------------+ +-----------------------+
| Function Arguments| |Crucible Register State|
|       (args)      | +-----------+-----------+
+----------------+--+             |
                 |                |  GlobalReads(f)
                 |                v
                 |          +-----+-----+
                 |          |globalreads|
                 |          +-----+-----+
                 |                |
                 v                v
             +---+----------------+--+
             |uf.f(args, globalreads)|
             +-----------+-----------+
                         |
                         v
       +-----------------+----------------+
       | +--------------+ +-------------+ |
       | |Natural Return| |Global Writes| |
       | +--------------+ +-------------+ |
       +----------------------------------+
              |                      |
              | field(0)             | field(1)
              v                      v
      +-------+-------+   +----------+------------+
      |Function Return|   |Crucible Register State|
      +---------------+   +-----------------------+
```

## Instructions - Tracked vs. Untracked Global State

Most of the translator is agnostic of whether or not the given ASL syntax
corresponds to an ASL function vs. an ASL instruction specification.
Similar to a function, the natural arguments to an instruction are simply
its operands, and it has no natural return value, while its global writes
are any effects it has on the machine state.

Each what4 function representing an instruction, however, is standardized to
take and produce the same standard set of globals. These globals are considered
_tracked_, or semantically relevant to our model of the processor state.

The set of tracked global variables is manually defined in
`Language.ASL.Globals.Definitions`. It consists of the processor state,
the user registers, vector registers, the program counter, the system memory,
as well as various execution flags.

In contrast to a tracked global, an _untracked_ global is any piece of global
state that is not expected to change, or where changes are not relevant to our
semantics. The set of untracked globals is also manually defined in
`Language.ASL.Globals.Definitions`, which is the minimal set required to build
the fragment of Aarch32 that we are targeting.

Most of the available global ASL state is unmodified during normal execution,
and therefore not necessary to be tracked as part of our semantics. The majority
of the untracked globals have an undefined value that is not expected to be read
during normal execution. During translation, untracked globals are initialized
with a distinguished uninterpreted function (e.g. `INIT_CPACR()`). Updates to
these values (i.e. across intermediate function calls) are persistent for the
duration of a single instruction, but their final value is discarded after the
instruction execution is finished.

Both kinds of globals are defined as a `Language.ASL.Globals.Types.Global`,
which optionally allows for a valid set of values to be defined as a
`GlobalDomain`. During translation for each instruction, each global (both
tracked an untracked) is asserted to belong to their expected domain both at the
beginning and end of execution. For example, we assume that the processor is
always executing in user mode, and therefore any references to the current mode
(`PSTATE_M`) are always `M32_User`, and any changes to `PSTATE_M` will raise an
assertion failure.

## Global References

The `Language.ASL.Globals` module provides an interface to the struct
representing the global ASL state (taken as input and given as the output of
each instruction).  It uses template haskell to generate the type signature for
the struct out of the definitions present in
`Language.ASL.Globals.Definitions`. The `GlobalRef` datatype represents a
reference to a tracked global in ASL. Its type parameter is the name of the ASL
global that it refers to.

## Registers and Memory Global Variables

The general-purpose registers, vector registers and RAM are all represented by
an array-typed global variable. Access to these globals, however, is only via
special-purpose uninterpreted functions. The resulting `__Memory` global
variable after any instruction execution is therefore guaranteed to be a
collection of (uninterpreted) `write_mem` functions. Further processing of this
specification is free to assign semantics to these functions without necessarily
involving any theory of arrays.

In `Language.ASL.Globals` there is a distinct `GlobalRef` for each
general-purpose register (GPR) and vector register (SIMD). The global struct
representing the entire CPU state, however, contains a single array-typed
variable for each register set. The functions `flattenGlobalsStruct` and
`destructGlobals` from `Language.ASL.Globals` provide an interface for
projecting between both views of the registers.

## Exceptions

ASL has a few different sources of exceptional control flow. The most
straightforward is the `assert` statement, which simply asserts that the
provided boolean expression is true. Additionally the `UNDEFINED` and
`UNPREDICTABLE` statements are error conditions resulting from unexpected
input, underspecified processor features or state.

In the translated semantics, these are each represented by flags in the set of
tracked globals (i.e. `__AssertionFailure`, `__UndefinedBehavior` and
`__UnpredictableBehavior`). Rather than explicitly modelling exceptional control
flow, a corresponding flag is set to `True` when an exception is raised and
execution proceeds as normal. This avoids the state explosion that would be
caused by having every expression conditional on those flags. Although the
functions representing the instruction semantics are total, if any of the
exception flags are `True` then the resulting values are not necessarily
meaningful. The intention is that these flags will be checked externally by
any clients of these semantics.

## Undefined Values

Undefined or uninitialized values are represented by nullary uninterpreted
functions. Occasionally an undefined/uninitialized value will be returned by a
function, with the intention that its value will be discarded by the calling
context. This precludes the use of more standard features (i.e. using an
uninitialized register in Crucible), since these values need to persist outside
the scope of a given function.

An undefined value can be explicitly created in ASL with the `UNKNOWN` primitive.
It is also possible, however, to create an undefined value by returning a variable
without initializing it.

For example, in the following ASL code either the first or second element of
the resulting tuple is undefined depending on the given `b`.
```
(integer, integer) f(boolean b)
    if b then
        foo = 1
    else
        baz = 1
    return (foo, baz)
```

In this case, the translator implicitly sets both `foo` and `baz` to be
undefined integers before the `if` statement.

Although function calls and undefined values are both represented as
uninterpreted functions, they have different behaviors with respect
to their "fresh"ness in the underlying what4 representation. The Crucible
extension used by the translator (defined in `Language.ASL.Crucible.Extension`)
adds a `UF` primitive for creating explicit calls to uninterpreted functions.
An uninterpreted function can be introduced as either "fresh" or "cached".
Undefined values are represented by fresh uninterpreted functions, indicating
that they are all formally distinct. Two undefined values are therefore not
necessarily equivalent. Function calls, however, are represented by cached
uninterpreted functions: all function calls are represented by the same
formal what4 function and are therefore equivalent given the same arguments.

## Types - Constraints and Extensions

Each ASL expression is resolved to some Crucible expression or atom during
translation, which assigns it a What4 base type (i.e. a boolean, integer,
struct, or fixed-width bitvector). The fields of an ASL struct, however, are
accessed by name, while What4 structs are accessed by index. Additionally,
system registers are treated as both raw bitvectors as well as structs, where a
field access represents some slice of the bitvector.

Along with its Crucible representation, each ASL expression is therefore given
some `ExtendedTypeData` which tracks additional type information. In the case
of a struct, it contains a mapping from struct names to indexes. When
the translator is initialized for a function, an `ExtendedTypeData` is provided
for each argument based on its ASL type. This extended data is propagated 
during translation, and used to resolve named field accesses.

Each ASL expression is also translated under some `TypeConstraint`, representing
any known constraints that can be inferred about the target type of the expression
based on the surrounding context. This is required to concretize bitvector widths
when this can't be determined from the expression itself.

For example, the `Zeros()` function returns a bitvector of any length. Since this
can't be monomorphized without a concrete width for the target size, we need to know
the context in which `Zeros()` has been called. In the simplest case, this is
either provided as an explicit type annotation or can be inferred as the result
of some assignment.

```
bits(32) foo = Zeros();
foo = Ones();
(result, carry) = AddWithCarry(foo, Zeros(), '1');
```

All of these cases are straightforward, as we can determine a specific target
type (i.e. a `ConstraintSingle`) before we translate each function call. In
the final case of `AddWithCarry` the first argument, `foo`, pins down the
bitvector width to 32, which can then be used to determine the type of `result`
as well as the second argument, `Zeros()`.

### Slicing

ASL allows for reading and writing to restriced "slices" of bitvectors with the
syntax: `var<3:0>`, representing a 4-bit slice of the low bits of `var`. A slice
may be used as a expression, or as an l-value in an assignment. e.g. `var<3:0>
= Zeros()` sets the lower 4 bits of `var` to `0`.

Bitvector slices are translated into explicit calls to the `getSlice` and
`setSlice` functions, which have been manually defined in
`extra_defs.asl`. These define bitvector slicing in terms of shifts and masks,
with runtime assertions that the provided indexes are wellformed.

Translation is straightforward when the width of the slice can be determined
statically. For example `var<i:i-4>` can be assumed to be 4 bits wide (given an
assertion `i >= 4`). The surrounding type information can be used to determine a
slice width even when the indexes are symbolic. e.g. `bits(4) a = var<i:j>`

Complications arise, however, when the size of a slice isn't apparent from the
surrounding context. For example, in the assignment `bits(32) a =
ZeroExtend(bv<i:j>)` a concrete width for `bv<i:j>` can't be determined since
`ZeroExtend` can take any bitvector width as an argument. The outer type
constraint of `bits(32)` can't be used directly, since `bv<i:j>` may not
necessarily be 32 bits wide.

In this case, the expression `bv<i:j>` is translated with a `ConstraintHint` as
its constrant. Here the provided hint is `HintMaxBVSize 32`, which indicates
that `bv<i:j>` may be _at most_ 32 bits. When `bv<i:j>` is then translated into
a call to `getSlice`, where the width of the resulting bitvector is concretized
to 32 bits. The `signed` argument to `getSlice` controls whether or not the
resulting slice is sign or zero-extended to the target width after slicing.

Simiularly, the `UInt(bits(N))` function translates its argument with a
`HintBVAnySize` constraint. This allows the resulting bitvector to have any
size, while providing a hint that any bitvector slice may be implicitly
zero-extended to the size of the source bitvector. For example, given
`UInt('1111'<i:j>)` we first translate `'1111'` and then use `HintBVAnySize` to
determine that the slice `'1111'<i:j>'` may be stored in a 4-bit bitvector and
have its actual value (given a concrete `i` and `j`) zero-extended to 4 bits.

The constraints for bitvector primitives are determined by a set of
manually-defined overrides in the translator
(`Language.ASL.Translation.Overrides`), but the set of supported cases is not
necessarily complete. For example, `LSL_C` from `arm_defs.asl` cannot be
automatically translated due to its use of an intermediate arbitrarily-wide
bitvector. We provide an alternative implementation in `extra_defs.asl` which is
equivalent, but can be automatically translated.

## Function Argument Type Unification

Matching a set of arguments to a function signature requires type _unification_
in order to resolve polymorphic bitvector lengths. This is complicated by the
fact that the type constraints imposed by the function signature may be
necessary to resolve the ASL expressions for the function arguments.
Unification therefore performs the dual function of calculating a monomorphized
variant of the called function, as well as providing necessary type constraints
in order to translate its arguments.

The three inputs to a unification problem are:

* A polymorphic function signature (e.g. `bits(L+M) f(bits(N*M) bv1, bits(N) bv2, integer M)`)
* A list of ASL expressions used as arguments to the given function (e.g. `(Zeros(16), baz<i:j>, 3-1)`)
* A type constraint for the function return value (e.g. `ConstraintSingle (BaseBVType 10)`)

Unification proceeds by first collecting any concretely known arguments. In this
example `3-1` is given as the `M` formal argument, which is concretely evaluated
to `2` and added to the binding environment `[M := 2]`.

From left to right, each expression is translated into a Crucible atom under the
type constraint imposed by the function signature, combined with any static
bindings that have been calculated so far during unification.

In our example, `Zeros(16)` is translated without constraints, since its
corresponding formal argument type `bits(N*M)` cannot be fully resolved under
the binding environment `[M := 2]`. 

Next the type of the resulting Crucible atom is unified against its argument
type, potentially discovering bindings for type variables.

In our example, `Zeros(16)` is translated into the Crucible type `BaseBVType
16`.  Under the bindinng environment `[M := 2]`, unifying `BaseBVType 16` with
`bits(N*M)` implies that `N` must be `8`. This is added to the binding
environment and unification then continues to the next argument. Here this
provides a necessary static upper bound of `8` on the bitvector width when
translating `baz<i:j>`.

After unifying the arguments, the return type from the function signature is
unified against the current type constraint. Here we unify `BaseBVType 10` with
`bits(L+M)` under the binding environment `[N := 8, M := 2]`, which implies that
`L` must be `8`.

The function signature is then evaluated in the binding environment to confirm
that all bitvector widths have been fully monomorphized. A variant name is
derived from the binding environment (e.g. `f_L_2_N_8_M_2`) as the formal
handle for the monomorphized variant of the function, and then translated 
into a function call. The function name and binding environment pair are
then recorded as a dependency of the current function, potentially creating
a future translation obligation.

Note that this unification strategy is sensitive to the order of the function
arguments. In our example, swapping the first and second arguments `f` would
have caused a translation failure due to `N` not having a static binding when
translating `baz<i:j>`. This does not appear to be an issue in practice,
however.

Here is an overview of the intermediate binding environments in our example
unification of `f`:

```
  +-------------------------------------------------------+
  | f(bits(N*M) bv1, bits(N) bv2, integer M) :: bits(L+M) |
  +--------+-------------+------------+-------------+-----+
           |             |            |             |
   [M := 2]|     [M := 2]|            |     [M := 2]|
           |     [N := 8]|            |     [N := 8]|
           |             |            |             |
  +--------v-------------v------------v-------------v-----+
  | f(Zeros(16),     baz<i:j>,       3-1)    :: bits(10)  |
  +--------+--------------------------+-------------+-----+
           |                          |             |
           v                          v             v
       [N := 8]                   [M := 2]      [L := 10]

```

# Simulation

Given a successfully-translated ASL function or instruction, represented as a
Crucible CFG wrapped in a `Language.ASL.Crucible.Function` or
`Language.ASL.Crucible.Instruction`, the final step in translation is to
symbolically execute that CFG into a closed-form What4 function.

This is handled by the `Language.ASL` module with either `simulateFunction` or
`simulateInstruction`. Here the primary distinction between a `Function` and and
`Instruction` is that an instruction has a uniform structure with respect to the
_tracked_ set of global ASL variables. All instructions are defined to read from
and write to the entire set of tracked globals, taking the instruction operands
as the natural function arguments. The symbolic expression representing the
result of an instruction is reshaped to conform to this standard signature. In
contrast, a function may read from and write to any global variable.

In both cases, a fresh both variable is initialized for each of the function's
natural arguments. These are use to initialize the Crucible registers to be
accessed during translation. A single bound variable (`globalReads`) is created
for the struct representing the global reads of the function. For each global
read, a `Crucible.Simulator.GlobalState.GlobalVar` is initialized with a
corresponding field access from `globalReads`.


The return value of each CFG is a struct containing both the natural return
value of the function, as well as the final state of the global variables. After
successfully symbolically executing the CFG, the resulting expression is then
simply used as the body of the function representing the semantics for the given
ASL instruction or function.

# Serialization

Once all the target instructions and dependent functions have been successfully
translated and simulated, they are serialized as s-expressions with
`Language.ASL.Formulas.Serialize`, which uses
[what4-serialize][fn:what4-serialize] as its backend. 
The `Language.ASL.Driver` produces two files by default: `functions.what4` and
`instructions.what4`, corresponding to the translated and serialized functions
from `arm_defs.asl` and the instructions from `arm_instrs.asl` respectively.

Recall that up until now there has been no formal connection between a function
_call_ and the _definition_ (i.e. its translated semantics) of a function. In
the final what4 function representing an ASL instruction or function, function
calls are still uninterpreted functions. This connection is made formal during
the deserialization of the function environment s-expression. As each function
is deserialized, it is added to an incrementally-built function environment that
puts all currently-serialized functions in-scope. The deserialization then
parses a function call by retrieving the actual function definition from this
environment and producing a what4 _defined_ function. Notably the serialized
function environment is already in toplogical order, so all necessary dependent
function definitions will be in-scope when a function is deserialized.

# Normalization

Normalization (implemented in `Language.ASL.Formulas.Normalize`) occurs as a
final post-processing step on the serialized semantics. Its purpose is to
rewrite the what4 functions produced by the translator into equivalent functions
which do not contain any structs or integers. Although it has been
designed to be used with the ASL semantics, the normalization process is
agnostic of most ARM or ASL-specific details.

Normalization is performed as a second call to the translator executable,
following a successful translation, which reads in the resulting
`functions.what4` and `instructions.what4` files and produces
`functions-norm.what4` and ``instructions-norm.what4`. These normalized,
serialized functions are then used as the basis for defining the ARM semantics
in [semmc][https://github.com/GaloisInc/semmc].

The functions in `functions.what4` are deserialized and normalized one at a
time, proceeding in topological order. For a given function the normalized
variant may have a modified signature: decomposing structs, replacing integers
with bitvectors and removing redundant arguments. We create a proxy function
which has the same signature as the original, but simply dispatches to the
normalized function.

For example, a function which takes and returns a single integer `integer
f(integer x) := x` would be rewritten to instead use a 65-bit bitvector (able to
hold a 64 bit value with an additional sign bit): `bits(65) f_norm(bits(65) x)
:= x`. The proxy function then simply projects to and from this bitvector to
re-create the original function: 
`integer f(integer x) := sbvToInteger(f_norm(integerToBV(x)))`.

This proxy function is then added to the environment instead of the original,
and marked to be inlined unconditionally. When deserializing subsequent functions,
calls to this proxy will therefore implicitly be rewritten to instead refer
to the normalized function.

For example, given the above proxy for `f` when we deserialize `boolean
g(integer x, integer y) := f(x) == f(y)` the result will instead be `boolean
g(integer x, integer y) := sbvToInteger(f_norm(integerToBV(x))) ==
sbvToInteger(f_norm(integerToBV(y)))`. The normalization process then can
eliminate calls to `sbvToInteger` and `integerToBV` in order to normalize `g`.
i.e. `boolean g_norm(bits(65) x, bits(65) y) := f_norm(x) == f_norm(y)`.

Once all the helper functions from `functions.what4` have been normalized, the
instructions are then read in from `instructions.what4` and normalized in the
resulting binding environment. This does not need to be done incrementally,
however, as instructions do not contain calls to each other.

Only the proxy functions corresponding to normalized instructions need to be
serialized: all proxy functions for helpers have already been inlined and
therefore there are no calls to them in the final normalized semantics.

## Struct Removal

The calling convention used to translate ASL into what4 introduces a large
number structs: every function call involves assembling a new struct to
represent the global variables passed to that function. In order to serve as the
ARM semantics for code discovery with
[macaw][https://github.com/GaloisInc/macaw] the semantics from the ASL
translator cannot contain any structs, as they are not supported by macaw.

Earlier we assumed that each function was normalized into a single, semantically
equivalent function. Functions which return structs, however, need to be
decomposed into a collection of functions: one per field in the resulting
struct. In the translated ASL, each function necessarily returns a struct,
representing writes to global variables. ASL functions may return structs as
their natural arguments (either a tuple or a user-defined struct type),
resulting in a _nested_ struct tree that needs to be decomposed during
normalization. Normalization therefore produces a new function for each
leaf in the struct tree for the return type of a given function.

The arguments to a function may also contain structs. Again, in the translated
ASL semantics each function necessarily takes at least one struct, representing
the accessible global state of that function. In general, struct-type arguments
may also be nested, usually when a user-defined struct is passed to a function.
These struct-type arguments therefore need to be flattened in order to produce a
single list of (non-struct) arguments. This normalized signature therefore
introduces an additional argument for each leaf of each struct-type argument in
the original signature.

For example, given the struct definition `mystruct := { fst :: boolean, snd :: boolean}` and
the function `f(mystruct s1, mystruct s2) := (s1.fst && s2.fst, s1.snd || s2.snd)`
the we produce the following normalized variants of `f`:
```
f_0(boolean s1_0, boolean s2_0) := s1_0 && s2_0
f_1(boolean s1_1, boolean s2_1) := s1_1 || s2_1
```

The resulting collection of normalized functions is then collected into a single proxy function,
which has the same signature of the original but is instead defined as a collection of normalized
functions. e.g.:

```
f(mystruct s1, mystruct s2) := (f_0 (s1.fst, s2.fst), f_1(s1.snd, s2.snd))
```

This proxy function is inlined unconditionally when deserializing and
normalizing subsequent functions, exposing the normalized functions instead and
allowing for the resulting struct to be normalized away.

For example:
```
g(boolean b1, boolean b2) := let (_, result) = f({ fst = b1, snd = b2}, {fst = b2, snd = b1}) in result
```
is immediately rewritten into:
```
g(boolean b1, boolean b2) := let (_, result) = (f_0 (b1, b2), f_1 (b2, b1)) in result
```
which can then be further simplified into:
```
g(boolean b1, boolean b2) := f_1 (b2, b1))
```

Some additional rewrites are necessary in order to normalize struct field
accesses across if-then-else branches, e.g.: `(if b then { fst = b1, snd = b2}
else (fst = b2, snd = b1)).fst` can always be simplified into `(if b then b1
else b2)`. This is arguably a simplification that What4 itself should perform,
but currently this rewrite step needs to be explicitly done during
normalization.

## Integer Removal

TODO
* replacing integers with `bits(65)` everywhere.
* rewriting integer arithmetic with guarded bitvector arithmetic
* rewriting `integerToBV`, `bvToInteger` and `sbvToInteger` as either
a bitvector truncation, sign-extend or zero-extend as appropriate, with 
assertions that information is not thrown away.


## Duplication

TODO
* normalized functions contain duplicate expressions
* duplication could be avoided by factoring out common sub-expressions into helper functions
* may be strictly necessary for representing memory and register updates

# Static Expression Evaluation

TODO
* evaluate ASL expressions when all variables are concrete
  - necessary for resolving bitvector lengths (e.g. `bits(N+M)`) when
  unifying function arguments as well as translating bitvector slices
* symbolic execution of ASL directly to determine possible values for variables
after a block of statements has been executed
  - necessary for rewriting code blocks with variable-width bitvectors into
  multiple fixed-width variants

# Outstanding Issues

* EndOfInstruction 
  - what are the intended semantics of this function?
  - Does this affect the semantics of normal (user-mode) instructions?

* Inlining `getSlice` and `setSlice` for concrete arguments
  - normalization could avoid the bitshifting implementation in favor of standard
  bitvector primitives when the bitvector indexes are statically-known
  
* Removing dead code (especially old hacks)
  - hacks for renaming functions with clashing names
  
* Use What4 `ConcreteVal` instead of manually-defined `StaticExpr`
  - Possibly able to use What4 static evaluation?
  - Reduce risk of inconsistencies between the static ASL semantics and
  the Crucible-translated ASL semantics

* Avoid duplicate memory and register updates in normalized code
  - normalization currently obfuscates the control flow of the original
  function, which needs to be retained in order to represent memory
  writes and register updates in macaw


[fn:semmc]: https://github.com/GaloisInc/semmc
[fn:what4-serialize]: https://github.com/GaloisInc/what4-serialize/
[fn:asl-description]: https://alastairreid.github.io/dissecting-ARM-MRA/
[fn:what4]: https://github.com/GaloisInc/crucible/tree/master/what4/
