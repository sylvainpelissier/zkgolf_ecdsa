# ECDSA P-256 Soundness Proof Summary

## Result and Scope

The exported theorem `Solution.ECDSA_P256_Digest.soundness` is proved without
`sorryAx`. It has the unchanged `GeneralFormalCircuit.Soundness` statement
required by the challenge.

For every circuit offset, environment, and native input, if the input expressions
evaluate to that input and all circuit constraints hold, then:

1. The input and its supplied witness satisfy Longfellow's `ValidEcdsaWitness`
   relation, with the fixed P-256 parameters and subgroup order.
2. The circuit's external requirements hold.

The caller assumptions are `True`. In particular, selector ranges, curve checks,
inverse checks, table equalities, scalar bounds, and intermediate-state checks
are proved from constraints rather than assumed.

This is pointwise soundness for the supplied witness. The proof does not replace
the relation with existence of some valid signature or with `StandardEcdsaVerify`.
It concerns the native field interface, not byte parsing or hashing.

Sources: [trusted relation](../Challenge/Specs/ECDSAP256.lean),
[native interface](../Challenge/Instances/ECDSA_P256_Digest/Interface.lean),
[exported theorem](../Solution/ECDSA_P256_Digest/Main.lean).

## Supporting Proofs

The following components were already available before the loop and final
assembly work described below. They supply the local implications needed to
recover each part of `ValidEcdsaWitness`.

| Component | Established fact |
| --- | --- |
| [Gadgets.lean](../Baseline/ECDSA_P256_Digest/Soundness/Gadgets.lean) | Boolean and multiplexer facts used by point selection. |
| [Curve.lean](../Baseline/ECDSA_P256_Digest/Soundness/Curve.lean) | Evaluated `doubleE` and `addE` outputs equal Longfellow's RCB formulas, including the pending quadratic coordinates. |
| [Input.lean](../Baseline/ECDSA_P256_Digest/Soundness/Input.lean) | `InputEval` extracts field-by-field evaluation equalities from `eval env inputVar = input`. |
| [Range.lean](../Baseline/ECDSA_P256_Digest/Soundness/Range.lean) | Boolean bits satisfying `ltOrder` represent a natural number at most `n - 1`. |
| [Scalar.lean](../Baseline/ECDSA_P256_Digest/Soundness/Scalar.lean) | `scalar_spec_circuit` collects lengths, selector validity, reconstructions, curve membership, inverses, and scalar bounds. |
| [Table.lean](../Baseline/ECDSA_P256_Digest/Soundness/Table.lean) | `table_sound` recovers `ValidPreComputationExact` from the four table additions and point-equality checks. |
| [Step.lean](../Baseline/ECDSA_P256_Digest/Soundness/Step.lean) | `selectPoint_sound`, `step_sound`, and `stepRow_sound` identify selection and individual middle transitions with the specification. |

The range argument works on natural-number bit prefixes. Zero-run constraints
prevent a scalar from first exceeding `n - 1` at a zero bit of the bound.
Small counting sums cannot wrap modulo the circuit prime. Constant facts about
the bound and zero-run coverage are checked with `decide +kernel`.

## First Iteration

Added `assertFirst_sound` in
[Step.lean](../Baseline/ECDSA_P256_Digest/Soundness/Step.lean).

The first iteration starts from infinity and does not double. Longfellow's
addition formula specializes exactly to:

$$
\operatorname{addE}((0,1,0),(x,y,z)) = (xy,y^2,yz).
$$

The lemma derives these coordinates from the three `assertFirst` rows. It is an
exact coordinate equality, not merely projective equivalence, and needs no
nonzero-coordinate assumption.

`firstRow_sound` in [Loop.lean](../Baseline/ECDSA_P256_Digest/Soundness/Loop.lean)
then composes `selectPoint_sound` with `assertFirst_sound`. Boolean selector bits
identify the selected point with the specification's `muxPointF`.

## Loop Assembly: S8

The loop proof lives in
[Loop.lean](../Baseline/ECDSA_P256_Digest/Soundness/Loop.lean).
There are 256 selectors and 255 supplied intermediate points:

- Selector 0 produces intermediate point 0, without doubling.
- Selectors 1 through 254 double the preceding intermediate point and add the
  selected table point, producing intermediate points 1 through 254.
- Selector 255 produces the final result, checked separately.

### Recursive and Indexed Bridges

`loopConstraints_iff_rows` proves, by induction, an equivalence between the
recursive `EcdsaLoopConstraintsF` predicate and a `List.Forall₂` relation of
transition equations. Equal list lengths are explicit, and the final selector
is reserved for the final-result calculation. This equivalence is available for
reuse; the concrete soundness assembly uses the indexed bridge below.

`loopConstraints_ofFn` proves that indexed transition equations imply the
recursive loop predicate for lists constructed with `List.ofFn`. It handles an
arbitrary number of intermediate points, rather than expanding 255 cases.

### Middle Transitions

`middle_sound` uses `Circuit.forEach.forAllNoOffset` to extract the constraints
for each index in `Fin 254`, at its corresponding witness offset. It applies
`stepRow_sound` to obtain all middle transition equations.

`loopConstraints_sound` combines the first and middle equations through
`loopConstraints_ofFn`. Selector decomposition rewrites the selected value to
the supplied `bi` value, and `InputEval` rewrites intermediate coordinates to the
supplied input fields. Vector-to-list conversions recover the exact lists used
by the trusted relation.

### Final Result Checks

`loopResult_ofFn` identifies the result of the recursive result function with
its last transition. This is a structural identity: earlier transition validity
is supplied separately by `loopConstraints_sound`.

`loopResult_eq_last` specializes that identity to the native vectors. The final
result is the addition of the point selected by `bi[255]` to the double of the
supplied intermediate point at index 254.

`lastRow_sound` derives the final X and Z equalities from the two `assertQuad`
checks. `loopResult_sound` combines this fact with `loopResult_eq_last` and input
evaluation to prove:

$$
\text{finalAcc.X} = 0 \quad\land\quad \text{finalAcc.Z} = 0.
$$

No additional check on Y is introduced. This preserves the exact boundary
conditions of the trusted relation.

## Complete Circuit Assembly: S10

[Soundness/Main.lean](../Baseline/ECDSA_P256_Digest/Soundness/Main.lean) contains
the complete assembly.

`main_spec` unfolds only the top-level circuit and uses `soundness_bind` to split
its constraints into 25 component facts. It then:

1. Obtains `InputEval` and all selector decomposition facts.
2. Applies `scalar_spec_circuit` to the scalar-side checks.
3. Applies `table_sound` to the precomputation checks.
4. Applies `loopConstraints_sound` and `loopResult_sound` to the loop checks.
5. Rewrites `tablePK`, `tablePre`, and `preList` into the native input fields and
   the supplied precomputation list.
6. Assembles every conjunct of `ValidEcdsaWitness` in the required order.

`PlainOps.requirements` proves that a plain operation list has no external
requirements to discharge: witness and assertion operations contribute only
trivial requirements, and interactions and subcircuits are excluded by
`PlainOps`.

`main_soundness` combines `main_spec` with this requirements proof to establish
the full `GeneralFormalCircuit.Soundness` obligation. The submission imports the
assembly module and exports `main_soundness` directly instead of a placeholder.

## Proof Engineering

The circuit and trusted statement were not changed. The score is now 18,612
(8,787 witness allocations and 9,825 constraints); see [optimization.md](optimization.md).
The loop proofs were adapted to the two optimized gadgets: `assertPoint_sound` takes the
`CrossShape` hypothesis that `addE` and `step` outputs satisfy.

`seal_gadgets` prevents implicit expansion of large circuits during elaboration.
Proofs open only the necessary definitions. Restricted simplification keeps
256-element `List.ofFn` expressions symbolic, and explicit `Fin` lookup
normalization reconciles indexed circuit rows with natural-number list positions.

## Validation and Remaining Work

The following checks passed when S10 was completed:

```sh
lake build Baseline.ECDSA_P256_Digest.Soundness.Main
lake build Solution.ECDSA_P256_Digest.Main
python3 scripts/check_axioms.py
git diff --check
```

[Tests/Axioms.lean](../Tests/Axioms.lean) now includes the exported soundness
theorem as a persistent audit root. All five audit roots passed the policy that
permits only `propext`, `Classical.choice`, and `Quot.sound`.

Completeness is now also proved and exported without `sorryAx`; the current
audit has 26 roots. On 2026-11-10, the full local suite, external C++ cross-check,
four comparator fixtures, and actual submission comparator acceptance all passed.
Fresh project verification, including Lean kernel replay, took 770.94 seconds
with dependency caches retained, below the 1200 s limit. See
[validation](validation.md) for reproduction and the local development-shim
scope; production sandbox acceptance is not established by these checks.
