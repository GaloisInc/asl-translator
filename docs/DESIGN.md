# Introduction

This document details the architecture of the asl translator, as well as
detailing some of the design decisions that were made and the technical
challenges that were encountered during its development.

The goal of this translator is to convert the imperative-style code from
the [Arm Architecture Specification Language (ASL)][fn:asl-description] into
a closed-form [What4][fn:what4] function in order to serve as the formal semantics
for the AArch32 architecture for the purpose of perform binary analysis on
compiled executables.

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
## ASL Translation Pipeline
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


## Preprocessing

Preprocessing transforms the ASL AST into a semantically equivalent AST, but
with a simplified representation in order to ease translation. Additionally, it
computes necessary static information about the ASL specification, such as function
signatures and user-defined types.

### Getters/Setters

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

### Function Signatures

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


### Types

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


### Monomorphization

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

## Translation

Translation is the core functionality of the ASL translator - taking
preprocessed ASL syntax with function signatures, and producing
a Crucible control flow graph representing its execution semantics.
Most of the complexity in this transformation arises from variable-width
and dependently-typed bitvector widths, as well as representing the
ASL global state.

### Global State

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

### Function Calls

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

### Instructions - Tracked vs. Untracked Global State

Most of the translator is agnostic of whether or not the given ASL syntax
corresponds to an ASL function vs. an ASL instruction specification.
Similar to a function, the natural arguments to an instruction are simply
its operands, and it has no natural return value, while its global writes
are any effects it has on the machine state.

Each what4 function representing an instruction, however, is standardized to
take and produce a fixed set of globals. These globals are considered _tracked_,
or semantically relevant to our model of the processor state. 

The set of tracked global variables is manually defined in
`Language.ASL.Globals.Definitions`. It consists of the processor state,
the user registers, vector registers, the program counter, the system memory,
as well as various execution flags.

In contrast to a tracked global, an _untracked_ global is any piece of global
state that is not expected to change. Most of the available global ASL state is
unmodified during normal execution, and therefore not necessary to be tracked as
part of our semantics. For example, if we assume that the processor is always
executing in user mode then we can assume any references to the current mode
(`PSTATE_M`) are always `M32_User` and that any assignments to it are invalid.
Other registers may simply have an undefined value that we don't expect to be
read for



[fn:asl-description]: https://alastairreid.github.io/dissecting-ARM-MRA/
[fn:what4]: https://github.com/GaloisInc/crucible/tree/master/what4/
