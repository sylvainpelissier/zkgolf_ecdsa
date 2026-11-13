# What the ECDSA P-256 proof contains

This document states exactly what is machine-checked in this repository, what
has to be trusted for those statements to mean anything, and what is not proved.
It describes commit `85b78f1`. For how each proof works internally, see the
[soundness](soundness.md) and [completeness](completeness.md) summaries.

## Summary

The repository contains one R1CS circuit over the P-256 base field and seven
Lean theorems about it. Together they say:

- **Correctness.** For every native input, the circuit's constraints can be
  satisfied exactly when that input satisfies Longfellow's `ValidEcdsaWitness`
  relation. Soundness gives one direction, completeness the other.
- **Cost.** The circuit allocates exactly 9,296 witness cells and has exactly
  10,334 constraint rows (score 19,630), and every row is a genuine R1CS row.
- **Well-formedness.** Witness generation is expressed in the challenge's IR,
  reads only earlier cells, and the circuit uses no lookups, channels or
  subcircuits.

All seven theorems depend only on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). There is no `sorry`, no `native_decide`, and
no added axiom.

The proof does **not** show that the relation is equivalent to standard ECDSA
verification. It shows that the optimized circuit accepts the same inputs as
Longfellow's circuit model. See [What is not proved](#what-is-not-proved).

## What must be trusted

The theorems are only as meaningful as the definitions they mention. These are
the files a reviewer has to read; everything else is checked by Lean.

| Trusted item | Location | Role |
| --- | --- | --- |
| Target relation `ValidEcdsaWitness` | [EcdsaCircuit.lean](../vendor/longfellow/ECDSA/EcdsaCircuit.lean) (vendored, pinned to Longfellow commit `4fe092b`) | Defines what "accepted" means |
| Curve arithmetic `addE`, `doubleE` | [EC.lean](../vendor/longfellow/ECDSA/EC.lean) (vendored) | Used by the relation |
| Scalar reconstruction `reconstructE/R/S`, `natR`, `natS` | [Nat.lean](../vendor/longfellow/ECDSA/Nat.lean) (vendored) | Used by the relation |
| P-256 constants and wrapper `Spec` | [ECDSAP256.lean](../Challenge/Specs/ECDSAP256.lean) | Fixes `p`, `n`, `a`, `b`, `G`, 256 bits |
| Native interface | [Interface.lean](../Challenge/Instances/ECDSA_P256_Digest/Interface.lean) | Input layout, assumptions, specs |
| Theorem statements | [Challenge.lean](../Challenge/Instances/ECDSA_P256_Digest/Challenge.lean) | The seven types the submission must inhabit |
| Cost and IR definitions | [CostR1CS.lean](../Challenge/Utils/CostR1CS.lean), [WitgenIR.lean](../Challenge/Utils/WitgenIR.lean) | Define "cost", "R1CS row", "IR witness" |
| Clean framework | pinned in [lakefile.lean](../lakefile.lean) | Defines circuits, `Soundness`, `Completeness` |
| Lean 4.34.0 kernel and Mathlib | [lean-toolchain](../lean-toolchain), [lakefile.lean](../lakefile.lean) | Checks the proofs |

The primality of `p` is not trusted: it is proved by the vendored Pratt
certificate in [Pratt.lean](../vendor/longfellow/ECDSA/Pratt.lean).

## The seven theorems

All are exported from
[Solution/ECDSA_P256_Digest/Main.lean](../Solution/ECDSA_P256_Digest/Main.lean)
with exactly the types required by the challenge template. The proofs live
under [Baseline/ECDSA_P256_Digest/](../Baseline/ECDSA_P256_Digest/).

| Theorem | What it says | Proof |
| --- | --- | --- |
| `soundness` | If the constraints hold under any witness assignment, the input satisfies `ValidEcdsaWitness` | [Soundness/Main.lean](../Baseline/ECDSA_P256_Digest/Soundness/Main.lean) |
| `completeness` | If the input satisfies `ValidEcdsaWitness`, the circuit's own witness generators satisfy every constraint | [Completeness/Main.lean](../Baseline/ECDSA_P256_Digest/Completeness/Main.lean) |
| `mainCost` | Exactly 9,296 allocations and 10,334 constraints, for every input and offset | [Cost.lean](../Baseline/ECDSA_P256_Digest/Cost.lean) |
| `isR1CS` | Every assertion has at most one product of two affine expressions | [R1CS.lean](../Baseline/ECDSA_P256_Digest/R1CS.lean) |
| `witgenIsIR` | Every witness is computed by an IR program, not an opaque Lean function | [Plain.lean](../Baseline/ECDSA_P256_Digest/Plain.lean) |
| `computableWitness` | Each witness generator reads only cells below its own offset | [CompWit.lean](../Baseline/ECDSA_P256_Digest/CompWit.lean) |
| `requirementsChannelsLawful` | The circuit has no channel obligations (it uses none) | [Plain.lean](../Baseline/ECDSA_P256_Digest/Plain.lean) |

### Soundness, precisely

```lean
theorem soundness :
  GeneralFormalCircuit.Soundness (F circuitPrime) main Assumptions Spec
```

For every offset, every environment (an arbitrary assignment of all cells) and
every input: if the input variables evaluate to `input` and all constraints
hold, then

```lean
ValidEcdsaWitness (witness input) { X := input.pkX, Y := input.pkY } input.digest n params
```

Three properties of this statement matter:

- **No caller assumptions.** `Assumptions` is `True`. Selector ranges, curve
  membership, inverses, table entries and scalar bounds are all derived from
  constraints.
- **Pointwise.** The conclusion is about the supplied `rx`, `ry`, `pre`, `bi`
  and `int*` values themselves. It is not weakened to "some valid witness
  exists".
- **Adversarial internal wires.** The 9,296 internal cells are universally
  quantified. No assignment of them makes an invalid input pass.

### Completeness, precisely

```lean
theorem completeness :
  GeneralFormalCircuit.Completeness (F circuitPrime) main ProverAssumptions ProverSpec
```

`ProverAssumptions` is the same relation as the soundness `Spec`. For every
input satisfying it, an environment whose internal cells are filled by the
circuit's actual witness generators satisfies every constraint. `ProverSpec` is
`True`, since the circuit has unit output.

This is the honest-prover direction for the generators that ship with the
circuit. Showing that some satisfying assignment exists would not have been
enough to meet this statement.

## The relation, clause by clause

The native input has 1,037 field elements: `pkX`, `pkY`, `digest` (the
statement) and `rx`, `ry`, `rxInv`, `sInv`, `pkInv`, `pre[8]`, `bi[256]`,
`intX/Y/Z[255]` (Longfellow's source witness).

Each selector `bi[i]` is a value in `0..7`. Its three bits are, from low to
high, one bit of the scalars the relation calls E, R and S. The selector picks
the table point to add: `0` infinity, `1` G, `2` PK, `3` G+PK, `4` R, `5` G+R,
`6` R+PK, `7` G+R+PK, where R is the point `(rx, ry)`.

The table below lists every conjunct of `ValidEcdsaWitness`, the circuit rows
that enforce it, and the lemma that proves each direction. Costs are
allocations / constraints.

| Clause of the relation | Circuit rows | Cost | Soundness lemma | Completeness lemma |
| --- | --- | ---: | --- | --- |
| List lengths (256, 255, 255, 255, 8) | None; fixed by the vector types | 0 / 0 | `scalar_spec_circuit` | n/a |
| Every `bi[i]` is in `0..7` | `selectors`: two witnessed bits, a derived third, three boolean rows each | 512 / 768 | `selectors_sound` | `selectors_complete_of_input` |
| Table: `pre` holds G+PK, R+G, R+PK, G+RPK as affine points | Four additions, materialized, each with a two-row point-equality check | 29 / 37 | `table_sound` | `table_complete` |
| Loop step 0: `int[0] = ∞ + T(bi[0])` | `selectPoint`, `assertFirst` | 14 / 17 | `firstRow_sound` | `firstRow_complete` |
| Loop steps 1..254: `int[i] = 2·int[i-1] + T(bi[i])` | `middle`: double, select, add, compare | 8,636 / 9,398 | `middle_sound`, `loopConstraints_sound` | `middle_complete`, `loopConstraints_complete` |
| Final accumulator has `X = 0` and `Z = 0` | Last `step` and two `assertQuad` rows | 33 / 35 | `loopResult_sound` | `loopResult_complete` |
| `reconstructE bi = digest` | One linear row | 0 / 1 | `scalar_spec_circuit` | `scalar_reconstruction_complete` |
| `reconstructR bi = rx` | One linear row | 0 / 1 | `scalar_spec_circuit` | `scalar_reconstruction_complete` |
| PK is on the curve | `onCurve` | 2 / 3 | `scalar_spec_circuit` | `onCurve_complete` |
| `(rx, ry)` is on the curve | `onCurve` | 2 / 3 | `scalar_spec_circuit` | `onCurve_complete` |
| `rx · rxInv = 1` | `inverse` | 0 / 1 | `scalar_spec_circuit` | `inverse_complete` |
| `reconstructS bi · sInv = 1` | `inverse` | 0 / 1 | `scalar_spec_circuit` | `scalar_reconstruction_complete` |
| `pkX · pkInv = 1` | `inverse` | 0 / 1 | `scalar_spec_circuit` | `inverse_complete` |
| `natR bi < n` | `ltOrder` on bit column 1 | 34 / 34 | `ltOrder_sound` (via `scalar_spec_circuit`) | `ltOrder_complete` |
| `natS bi < n` | `ltOrder` on bit column 2 | 34 / 34 | `ltOrder_sound` (via `scalar_spec_circuit`) | `ltOrder_complete` |
| **Total** | | **9,296 / 10,334** | `main_soundness` | `main_completeness` |

Two details of the relation are preserved exactly and are easy to misread:

- The final check constrains only `X` and `Z` of the accumulator. Nothing is
  asserted about `Y`, in the relation or in the circuit.
- Only the R and S scalars are range-checked against `n`. The E scalar is bound
  to `digest` by an equality in the field, with no separate bound.

## What the optimizations required proving

The circuit is not a literal lowering of the relation. Each shortcut below
changes the constraint system, so each needed its own argument that the
accepted set is unchanged.

| Optimization | Why it is still correct | Where |
| --- | --- | --- |
| Third selector bit is computed as `(v − b0 − 2·b1)/4` instead of witnessed | Three boolean rows still force `v ∈ 0..7`; 4 is invertible in the field | [Soundness/Scalar.lean](../Baseline/ECDSA_P256_Digest/Soundness/Scalar.lean), `bits3_complete` |
| First step replaces `addE((0,1,0), T)` by `(x·y, y², y·z)` | Exact coordinate identity, not just projective equivalence | `assertFirst_sound`, `assertFirst_complete` |
| Addition outputs stay as unexpanded quadratics until compared with `int[i]` | Evaluated outputs equal Longfellow's `addE` and `doubleE` formulas | [Soundness/Curve.lean](../Baseline/ECDSA_P256_Digest/Soundness/Curve.lean) |
| Table additions with G or `Z = 1` fold constant products | Same formulas with constants substituted; `R + G` is matched to `G + R` by commutativity of `addE` | `table_sound`, `table_complete` |
| `< n` is checked as `≤ n − 1`, one quotient row per zero run of `n − 1` (34 runs) | A bit string exceeds `n − 1` only if it has a one inside a zero run while matching all higher one bits; counts of at most 256 bits cannot wrap modulo `p` | [Soundness/Range.lean](../Baseline/ECDSA_P256_Digest/Soundness/Range.lean), [Completeness/Range.lean](../Baseline/ECDSA_P256_Digest/Completeness/Range.lean) |

The loop is handled by induction over indexed transitions
(`loopConstraints_ofFn` and its converse `loopConstraints_rows_ofFn`), so the
254 middle iterations are never unrolled.

Facts about concrete constants (the zero runs of `n − 1`, small numerals being
nonzero in the field) are discharged with `decide +kernel`. This is evaluation
inside the Lean kernel and adds no axiom.

## Proof inventory

| Area | Files | Theorems and lemmas |
| --- | --- | ---: |
| Circuit definition and length lemmas | [Circuit.lean](../Baseline/ECDSA_P256_Digest/Circuit.lean) | 9 |
| Cost | [Cost.lean](../Baseline/ECDSA_P256_Digest/Cost.lean) | 23 |
| R1CS form | [R1CS.lean](../Baseline/ECDSA_P256_Digest/R1CS.lean) | 46 |
| Plain operations, IR witnesses, channels | [Plain.lean](../Baseline/ECDSA_P256_Digest/Plain.lean), [Elaborated.lean](../Baseline/ECDSA_P256_Digest/Elaborated.lean) | 44 |
| Computable witnesses | [CompWit.lean](../Baseline/ECDSA_P256_Digest/CompWit.lean) | 64 |
| Soundness | [Soundness/](../Baseline/ECDSA_P256_Digest/Soundness/) (9 files) | 72 |
| Completeness | [Completeness/](../Baseline/ECDSA_P256_Digest/Completeness/) (8 files) | 49 |

## What is not proved

- **Equivalence with standard ECDSA.** No theorem in this repository relates
  `ValidEcdsaWitness` to `StandardEcdsaVerify`. The latter is vendored but used
  only in a regression test. The claim here is "same accepted set as
  Longfellow's circuit model", not "accepts exactly the valid signatures".
- **Known differences from standard ECDSA are kept, not fixed.** The relation
  uses the direct-x rule and rejects exceptional table cases such as
  `PK = −G`. In the test corpus, 14 signatures valid under ordinary ECDSA are
  rejected by the circuit path. The proof preserves this behaviour.
- **The C++ implementation.** The Lean model is pinned to Longfellow's
  `verify_signature3`, but nothing proves the C++ code or its compiler correct.
  Agreement is tested on 276 vectors, not proved. The C++ code also encodes
  selectors as `2v − 7` rather than `0..7`.
- **Everything before the field elements.** Hashing, byte parsing, canonical
  scalar encoding and the mapping of the digest into the field are outside the
  relation.
- **Privacy and the proof system.** Zero-knowledge, which inputs are public,
  and the soundness of whatever SNARK consumes the R1CS are not modelled.
- **Optimality.** 19,630 is the exact cost of this circuit. No lower bound is
  claimed.
- **Production verification.** The comparator runs used the unsandboxed
  development shim. Acceptance in the production sandbox is not established.

## How it is checked

| Check | Scope | Last result |
| --- | --- | --- |
| `lake build Solution.ECDSA_P256_Digest.Main` | Lean kernel checks all seven theorems | Passes |
| `python3 scripts/check_axioms.py` | 26 audit roots in [Tests/Axioms.lean](../Tests/Axioms.lean): the relation, the primality proof, exported soundness and completeness, and 20 completeness lemmas | 26/26 on 2026-11-13, against existing build artifacts |
| Comparator on [configs/ECDSA_P256_Digest.json](../configs/ECDSA_P256_Digest.json) | All seven theorem types, both definitions, axiom policy, kernel replay | Accepted on 2026-11-10 (development shim) |
| `scripts/check.sh` | Source hashes, build, regressions, axiom audit, 276 Lean and Rust vectors | Passed on 2026-11-10 |

One gap in the persistent audit: `mainCost`, `isR1CS`, `witgenIsIR`,
`computableWitness` and `requirementsChannelsLawful` are not roots in
`Tests/Axioms.lean`. Their axiom use is enforced by the comparator only. A
manual `#print axioms` on 2026-11-13 showed the same three standard axioms for
all five, and for `elaborated` and `formalCircuit`.

See [validation.md](validation.md) for reproduction commands and the vector
corpus, and [references.md](references.md) for the provenance of the pinned
relation.
