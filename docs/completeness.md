# ECDSA P-256 Completeness Proof Progress

## Result and Scope

Completeness is proved and exported as
`Solution.ECDSA_P256_Digest.completeness`, without `sorryAx`.
`main_constraints_complete` assembles every constraint at the actual top-level
circuit binds. `main_completeness` wraps it in the unchanged
`GeneralFormalCircuit.Completeness` contract, including the trivial `ProverSpec`.
The assembly, wrapper, and exported theorem are persistently axiom-audited.

The required direction is the reverse of [soundness](soundness.md): for a native
input satisfying the unchanged specification, an environment using the circuit's
actual local witness generators must satisfy the completeness constraints.
The witness-use premise is `UsesLocalWitnessesCompleteness`; proving existence of
some suitable witnesses would not suffice.

This remains pointwise in the supplied ECDSA witness, including its table and
intermediate coordinates. It does not replace `ValidEcdsaWitness` by ordinary
signature validity or introduce an existentially chosen witness. The circuit,
trusted relation, and proved cost are unchanged: 8,787 witness allocations plus
9,825 constraints, for a score of 18,612.

Sources: [trusted relation](../Challenge/Specs/ECDSAP256.lean),
[native interface](../Challenge/Instances/ECDSA_P256_Digest/Interface.lean), and
[submission](../Solution/ECDSA_P256_Digest/Main.lean).

## Milestones

| Part | Current status | Proof location |
| --- | --- | --- |
| C1: product and quadratic gadgets | Proved and persistently axiom-audited. | [Gadgets.lean](../Baseline/ECDSA_P256_Digest/Completeness/Gadgets.lean) |
| C2: generated selector bits | Single-selector and all-256 completeness proved and persistently axiom-audited, including native selector and scalar reconstruction. | [Gadgets.lean](../Baseline/ECDSA_P256_Digest/Completeness/Gadgets.lean), [Scalar.lean](../Baseline/ECDSA_P256_Digest/Completeness/Scalar.lean) |
| C3: table and transition rows | Proved and integrated at the actual top-level offsets; covered by the assembly audit. | [Step.lean](../Baseline/ECDSA_P256_Digest/Completeness/Step.lean), [Table.lean](../Baseline/ECDSA_P256_Digest/Completeness/Table.lean), [Loop.lean](../Baseline/ECDSA_P256_Digest/Completeness/Loop.lean) |
| C4: order bound | Range completeness and native scalar bounds proved and integrated; covered by the assembly audit. | [Range.lean](../Baseline/ECDSA_P256_Digest/Completeness/Range.lean), [Scalar.lean](../Baseline/ECDSA_P256_Digest/Completeness/Scalar.lean) |
| C5: inverses and curve checks | Native premises transported through input evaluation and all checks assembled; covered by the assembly audit. | [Gadgets.lean](../Baseline/ECDSA_P256_Digest/Completeness/Gadgets.lean), [Scalar.lean](../Baseline/ECDSA_P256_Digest/Completeness/Scalar.lean) |
| Complete circuit | Constraint assembly, public wrapper, and export proved and axiom-audited. | [Main.lean](../Baseline/ECDSA_P256_Digest/Completeness/Main.lean), [submission](../Solution/ECDSA_P256_Digest/Main.lean) |

## Generated Arithmetic Witnesses: C1

[Gadgets.lean](../Baseline/ECDSA_P256_Digest/Completeness/Gadgets.lean) proves:

- `mul_complete`: the generated product satisfies `z - x*y = 0`.
- `mux_complete`: the generated interpolation satisfies its assertion for any
  selector, not only a boolean selector.
- `matQuad_complete`: both generated products satisfy the materialization rows.
- `assertQuad_complete`: generated witnesses satisfy the assertion when the
  evaluated quadratic equals the supplied target.

The target-equality premise of `assertQuad_complete` is essential: witness
generation cannot make an incorrect supplied target pass its assertion.

The same method now covers `matPoint_complete`, `mux8_complete`,
`selectPoint_complete`, `addE_complete`, `addAff_complete`, and
`doubleE_complete`. These arithmetic rows hold for arbitrary inputs when their
actual witnesses are generated. Boolean selector assumptions are needed later to
identify interpolation with the specification's discrete point selection, not
to satisfy the interpolation rows themselves.

## Selector Bits: C2

`bits3_complete` handles each native selector value from 0 through 7. The witness
generator produces the two low bits using `v.bits 2`; the third bit is derived:

$$
b_2 = 4^{-1}(v - b_0 - 2b_1).
$$

All three boolean assertions hold in every case. The inverse of 4 is justified
by a kernel-checked nonzero fact. Canonical field-value normalization explicitly
handles the numeral one, and tactic branch selection uses `solve` so an
alternative must close its goal rather than merely normalize it.

[Scalar.lean](../Baseline/ECDSA_P256_Digest/Completeness/Scalar.lean) lifts this
result to all 256 entries:

- `selectors_complete` uses `Circuit.mapFinRange.usesLocalWitnesses` and
  `Circuit.mapFinRange.forAll'` to establish every selector row at its actual
  offset, without unrolling the vector. It assumes each evaluated selector is
  in `0..7` and the environment uses the actual generated witnesses.
- `selectors_complete_of_input` transports native selector-list validity through
  `InputEval`. It returns completeness together with booleanity of every generated
  bit and exact recomposition of each supplied `input.bi[index]` as
  `b0 + 2*b1 + 4*b2`.

The generated-bit facts reuse `selectors_sound` only after completeness has
established the constraints, through the proved plain-operations bridge.

## Native Scalar Reconstruction

[Scalar.lean](../Baseline/ECDSA_P256_Digest/Completeness/Scalar.lean) connects the
boolean columns to the exact native reconstructions. The premises are booleanity
of every bit and recomposition of each supplied selector, as returned by
`selectors_complete_of_input`.

`native_scalar_prefixes` proves that `natE`, `natR`, and `natS` of
`input.bi.toList.map val3` equal the natural prefix values of columns 0, 1, and 2.
It first identifies each selector with the cast of its three-bit natural value,
uses `val3_cast_eq` below 8, and then shows that each native mux reads the
corresponding column. The list folds remain symbolic through
`natReconstruct_ofFn` and `prefVal_congr`.

These are equalities in the naturals, not only modulo the circuit prime. Thus
the native `natR < n` and `natS < n` bounds transfer directly to the premises of
`ltOrder_complete`, without a new no-wrap assumption about the whole scalar.

`native_scalar_recompositions` combines these equalities with the existing
`recompose_prefVal` and native reconstruction/cast lemmas. It proves that the
evaluated circuit recompositions equal `reconstructE`, `reconstructR`, and
`reconstructS` of the native selector digits.

`scalar_reconstruction_complete` then uses `InputEval`, those bit/selector facts,
`ScalarSpec input`, and the actual R/S range-witness premises to establish:

- The digest and R scalar-binding assertions.
- The inverse assertion for reconstructed S and the supplied `sInv`.
- Both order checks using the generated quotient witnesses.

All three lemmas are persistent axiom-audit roots. The audited
`scalar_spec_of_valid_witness` extracts `ScalarSpec input` directly from
`ValidEcdsaWitness` for the supplied interface witness. It keeps the lengths,
selector validity, scalar equations, curve membership, inverse equations, and
order bounds, discarding only the table and loop conjuncts. The challenge and
interface specifications unfold to this same native premise; no witness is
replaced and no assumptions are added.

`main_constraints_complete` applies `scalar_reconstruction_complete` at the
top-level circuit offsets. Curve checks and the other supplied inverse checks
are assembled separately using the existing local lemmas.

## Composition and Transition Rows: C3

`completeness_bind` splits constraints at the same offsets as circuit binds.
Clean's `Circuit.ConstraintsHold.bind_usesLocalWitnesses` splits the actual
witness-use premise at those offsets.

[Step.lean](../Baseline/ECDSA_P256_Digest/Completeness/Step.lean) also proves
`PlainOps.completeness_iff_soundness`. This applies only to operation lists proved
to contain IR witnesses and assertions, with no lookups, interactions, or
subcircuits. For those lists, completeness and soundness check the same rows.
Consequently, a proof can first establish constraints from generated witnesses,
then reuse an existing soundness identity to identify the resulting coordinates.
This does not assume the constraints that completeness is meant to prove.

The transition results are:

- `step_complete`: generated doubling, selection, and addition witnesses satisfy
  all arithmetic rows.
- `stepRow_complete`: boolean selector bits and the native transition equation
  suffice for the checked middle row, using `assertPoint_complete`.
- `assertFirst_complete` and `firstRow_complete`: the optimized first transition
  is complete for exact addition from infinity, without doubling.
- `middle_complete`: all 254 middle iterations satisfy their rows when their
  indexed transition equations hold. It uses symbolic `forEach` witness and
  constraint rules rather than expanding the loop.
- `lastRow_complete`: a valid final result satisfies exactly the X and Z checks.

The first transition uses the exact identity

$$
\operatorname{addE}((0,1,0),(x,y,z)) = (xy,y^2,yz).
$$

The final premise is only `result.X = 0` and `result.Z = 0`. No canonical value
for Y or additional nonzero-coordinate condition is imposed.

## Native Loop Integration

[Loop.lean](../Baseline/ECDSA_P256_Digest/Completeness/Loop.lean) discharges the
local transition premises from the native recursive predicate:

- `loopConstraints_rows_ofFn` is the symbolic converse of
  `loopConstraints_ofFn`: recursive validity gives every indexed transition.
  The induction preserves the special first step and supplied intermediate
  points without expanding the 256 selectors.
- `native_loop_rows` specializes this result to the fixed input vectors,
  yielding the first transition and all 254 middle transitions.
- `loop_spec_of_valid_witness` extracts the recursive loop predicate and final
  X/Z checks from the full native relation for the supplied interface witness.
- `loopConstraints_complete` transports the native transitions through
  `InputEval` and selector recomposition, then proves the first and middle rows
  using the actual local witness generators at arbitrary offsets.
- `loopResult_complete` uses the existing `loopResult_eq_last` identity to prove
  the last row from the native result's X/Z checks and actual generated witnesses.

All five are persistent axiom-audit roots. The completeness bridges take the
native loop premises on the evaluated table arguments, boolean selector bits,
and the supplied selectors' recomposition. `main_constraints_complete` rewrites
the evaluated table arguments to the native table and splits witness-use premises
at the actual circuit bind offsets. No new condition on final Y is imposed.

## Precomputation Table: C3

[Table.lean](../Baseline/ECDSA_P256_Digest/Completeness/Table.lean) proves
`matPointRow_complete`, `addAffRow_complete`, and `table_complete`.

`table_complete` starts from `ValidPreComputationExact` on evaluated inputs and
the witness-use premises for the four checked table additions. It establishes
completeness constraints for each addition, its materialized coordinates, and
its affine point-equality check. The four entries are G + PK, R + G, R + PK, and
G + RPK. The existing addition-commutativity lemma reconciles the native R + G
order with the circuit's constant-folded G + R formula.

The result is a conjunction of four local checked computations at arbitrary
offsets. `main_constraints_complete` connects these to the top-level circuit binds.

## Curve and Inverse Checks: C5

`inverse_complete` proves its row from the exact supplied equation
`value * inverseValue = 1`. It does not generate or replace the supplied inverse.

`onCurve_complete` uses the generated square and cube witnesses and the supplied
curve equation to discharge its rows. `pointEq_complete` similarly turns the
native projective-to-affine equality into its two assertions.

Their native curve and inverse premises are extracted from `ValidEcdsaWitness`
by `scalar_spec_of_valid_witness`. `main_constraints_complete` transports them
through input evaluation and applies the local lemmas at the actual bind offsets.

## Range Converse: C4

For each zero run of the bits of `n - 1`, the circuit generates a quotient

$$
q = S M^{-1}, \qquad \text{and asserts } S - Mq = 0,
$$

where M counts higher bound-one bits missing from the scalar and S sums the
scalar's bits within the zero run. Inversion at zero is defined in the field,
but it cannot satisfy the row for a nonzero S. Completeness therefore needs

$$
M = 0 \Longrightarrow S = 0.
$$

`runCheck_complete` already proves that this implication suffices for the actual
generated quotient. It handles zero and nonzero M separately.

The range proof uses three preceding lemmas:

- `zeroRuns_zero`: a `decide +kernel` fact that every recorded run contains only
  zero bits of `n - 1`.
- `prefVal_prefix_le`: a bound on the full bit string bounds every prefix.
- `runs_of_prefVal_le`: matching all higher bound-one bits forces a bounded
  scalar to be zero throughout a recorded zero run.

`missingOnes_zero_runSum_zero` connects these natural-number facts to the field
counts. It translates a zero missing-count to a natural sum using boolean bounds
and the existing no-wrap lemma `natSum_eq_zero`. Each relevant missing-bit term
is then zero, so the scalar matches the higher one-bits of the bound and vanishes
on the zero run.

`ltOrder_complete` applies `runCheck_complete` to every recorded run through the
symbolic `forEach` witness and constraint rules. Its premises are the actual
local witness-use condition, boolean evaluated bits, and a natural prefix value
strictly below the subgroup order. The complete range module now builds.

### Resolved Proof Blocker

The former blocker was an `omega` step inside the local `hmatched` proof in
`missingOnes_zero_runSum_zero`. For a selected position, the proof had

$$
1-b = 0, \qquad b \leq 1, \qquad \text{goal: } b = 1,
$$

with natural subtraction. The hypotheses `hmissingBit` and `hboundBit` used a
`Fin 256` index constructed as `Fin.mk position hfinite`, while the goal used
the natural index `position` through `bitNat`. A diagnostic run confirmed that
explicitly normalizing those hypotheses let `omega` close the goal.

The applied fix instead uses the direct inequality argument:

```lean
exact Nat.le_antisymm hboundBit (Nat.sub_eq_zero_iff_le.mp hmissingBit)
```

`Nat.sub_eq_zero_iff_le` extracts `1 <= b` from `1 - b = 0`, and antisymmetry
combines it with `b <= 1`. Lean handles the definitionally equal indices directly.
No theorem assumption or circuit equation was changed. The range module is
imported by the persistent audit and integrated into the exported completeness proof.

## Validation Snapshot

The completed gadget, selector, step, table, range, loop, and assembly modules build with:

```sh
lake build Solution.ECDSA_P256_Digest.Main Tests.Axioms
python3 scripts/check_axioms.py
```

The persistent [axiom audit](../Tests/Axioms.lean) has twenty-six roots, including the
five original C1/C2 lemmas, `ltOrder_complete`, `selectors_complete`, and
`selectors_complete_of_input`, plus `native_scalar_prefixes`,
`native_scalar_recompositions`, `scalar_reconstruction_complete`, and
`scalar_spec_of_valid_witness`, all five native-loop lemmas above,
`native_spec_of_valid_witness`, `main_constraints_complete`, `main_completeness`,
and `Solution.ECDSA_P256_Digest.completeness`. The assembly
root transitively audits the table, transition, curve, inverse, selector, scalar,
and range lemmas it uses. All roots use only `propext`, `Classical.choice`, and
`Quot.sound`; the exported completeness theorem has no `sorryAx` dependency.

The range module also builds independently:

```sh
lake build Baseline.ECDSA_P256_Digest.Completeness.Range
```

On 2026-11-10, `scripts/check.sh` passed in 71.42 seconds, including all 26
axiom roots, 276 Lean cases, 276 Rust cases, and 262 original-message checks.
The pinned C++ cross-check passed (200 evaluated cases and 76 byte-envelope
rejections), as did all four comparator fixtures. The actual submission passed
the pinned comparator and Lean kernel replay, printing "Your solution is okay!".
After `lake clean ECDSAGolf`, fresh project verification took 770.94 seconds,
below the 1200 s limit, with dependency caches retained. Comparison with existing
project artifacts took 77.59 seconds. These runs use the unsandboxed development
shim; see [validation](validation.md) for reproduction and scope.

## Top-Level Assembly

The first assembly step is isolated in
[Native.lean](../Baseline/ECDSA_P256_Digest/Completeness/Native.lean).
`native_spec_of_valid_witness` extracts `ScalarSpec`, the exact precomputation
predicate, the recursive loop predicate, and the final X/Z conditions from the
unchanged specification for the supplied witness. It reuses the scalar and loop
extraction lemmas and is a persistent axiom-audit root. The top-level proof in
[Main.lean](../Baseline/ECDSA_P256_Digest/Completeness/Main.lean) consumes this
result and proves `main_constraints_complete` from the unchanged native
specification and `UsesLocalWitnessesCompleteness`.

The proof splits witness-use and completeness constraints through the same bind
rules. It normalizes offsets with the existing gadget-length lemmas before
applying the local completeness results. The table additions begin at offsets
0, 6, 12, and 23 relative to the supplied circuit offset. Selectors begin at 29;
the first, middle, and final transitions begin at 541, 555, and 9191.
The scalar bindings start at 9224, the curve checks at 9224 and 9226, and the
range checks at 9228 and 9262. These offsets are checked against the actual
circuit operations by Lean, not assumed as extra premises.

Keeping conjunction results as projections avoids expensive nested case
elaboration. The complete proof compiles under the default heartbeat and
recursion budgets; no increased proof budget is needed.

`main_completeness` introduces the framework's offset, prover environment, input,
actual witness-use premise, input-evaluation equality, and `ProverAssumptions`.
Those assumptions unfold to the same native specification consumed by
`main_constraints_complete`. The wrapper pairs its constraint proof with the
trivial `ProverSpec`. The submission imports this wrapper and exports it under
the exact challenge theorem statement, without unfolding the circuit.

## Remaining Work

The full local suite, actual local comparator acceptance, fresh-project
verifier-time check, and external C++ cross-validation have passed. Production
sandbox acceptance and cold dependency-build performance remain outside these
local development-shim checks.
