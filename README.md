# Longfellow ECDSA P-256 zkGolf challenge

Optimize Longfellow’s native ECDSA constraint check as R1CS over the P-256 base
field. Preserve `ValidEcdsaWitness` **pointwise**, including exceptional-case
rejections and checks on every supplied witness. No byte interface or separate
signature envelope is added to the trusted relation.

[Challenge statement](CHALLENGE.md) · [Trusted relation](Challenge/Specs/ECDSAP256.lean)
· [Native interface](Challenge/Instances/ECDSA_P256_Digest/Interface.lean)
· [Comparator contract](configs/ECDSA_P256_Digest.json)

```sh
scripts/bootstrap.sh
scripts/check.sh
python3 scripts/check_cpp.py /path/to/longfellow-zk
python3 scripts/check_comparator.py /path/to/pinned/comparator
python3 scripts/package.py
```

The C++ checkout must be at `4fe092be7e8e9634cd3b27daf55695a3a416043e`
([PR #215](https://github.com/longfellow-zk/longfellow-zk/pull/215)).
External byte vectors remain test adapters: they generate source witnesses and
compare the Lean arithmetic path, RustCrypto and actual C++ constraint evaluator.
Their encoding rejection cases are not constraints of the native challenge.

This package defines a single signature-component optimization challenge and
includes an in-progress R1CS submission. The challenge metadata has no official
baseline score; the local submission's proved cost is recorded below. See
[validation](docs/validation.md), [provenance](docs/references.md), and
[handoff](docs/publication.md).

## Solution status

The submission module is [`Solution/ECDSA_P256_Digest/Main.lean`](Solution/ECDSA_P256_Digest/Main.lean).
It re-exports the circuit and proofs in [`Baseline/ECDSA_P256_Digest/`](Baseline/ECDSA_P256_Digest/).
The circuit's proved cost is 19,630: 9,296 allocations and 10,334 constraints.
All submission obligations are proved. The actual submission passes the pinned
comparator using its local, unsandboxed development shim.

| Obligation | Status | Proof |
| --- | --- | --- |
| `mainCost` | done | [`Cost.lean`](Baseline/ECDSA_P256_Digest/Cost.lean) |
| `isR1CS` | done | [`R1CS.lean`](Baseline/ECDSA_P256_Digest/R1CS.lean) |
| `witgenIsIR` | done | [`Plain.lean`](Baseline/ECDSA_P256_Digest/Plain.lean) |
| `requirementsChannelsLawful` | done | [`Plain.lean`](Baseline/ECDSA_P256_Digest/Plain.lean) |
| `computableWitness` | done | [`CompWit.lean`](Baseline/ECDSA_P256_Digest/CompWit.lean) |
| `soundness` | done | [`Soundness/Main.lean`](Baseline/ECDSA_P256_Digest/Soundness/Main.lean) |
| `completeness` | done | [`Completeness/Main.lean`](Baseline/ECDSA_P256_Digest/Completeness/Main.lean) |

The circuit and trusted statements are unchanged by the proof work. The exported
soundness and completeness theorems are audited in [Tests/Axioms.lean](Tests/Axioms.lean) and use
only `propext`, `Classical.choice`, and `Quot.sound`.

### Soundness

See the [detailed soundness summary](docs/soundness.md) for the proof structure,
the completed loop and assembly work, and validation scope.

Done, one file per part of `ValidEcdsaWitness`:

- [`Gadgets.lean`](Baseline/ECDSA_P256_Digest/Soundness/Gadgets.lean): field facts for the
  selector gadgets (`bool_iff`, `mux8_spec`, `nz_spec`).
- [`Curve.lean`](Baseline/ECDSA_P256_Digest/Soundness/Curve.lean): `doubleE` and `addE` equal
  Longfellow's RCB formulas.
- [`Range.lean`](Baseline/ECDSA_P256_Digest/Soundness/Range.lean) (S9): the `< n` range check.
- [`Input.lean`](Baseline/ECDSA_P256_Digest/Soundness/Input.lean): the evaluated input, field by field.
- [`Scalar.lean`](Baseline/ECDSA_P256_Digest/Soundness/Scalar.lean) (S1–S4): lengths, selector
  values in `0..7`, the scalar reconstructions, curve membership, the inverses and `natR`/`natS < n`
  (`scalar_spec_circuit`).
- [`Step.lean`](Baseline/ECDSA_P256_Digest/Soundness/Step.lean) (S6, S7): point selection is
  `muxPointF`, and one loop step with its `int[i+1]` check is the spec's step equation (`stepRow_sound`).
- [`Table.lean`](Baseline/ECDSA_P256_Digest/Soundness/Table.lean) (S5): the precomputed table is
  `ValidPreComputationExact` (`table_sound`).
- [`Loop.lean`](Baseline/ECDSA_P256_Digest/Soundness/Loop.lean) (S8): the first and 254 middle
  transitions imply the supplied-witness loop predicate (`loopConstraints_sound`); the last
  transition proves the final `X = 0`, `Z = 0` checks (`loopResult_sound`).
- [`Main.lean`](Baseline/ECDSA_P256_Digest/Soundness/Main.lean) (S10): combines the scalar,
  table and loop results, rewrites evaluated inputs with `InputEval`, and discharges
  external requirements using `PlainOps` (`main_soundness`). The submission exports this proof.

### Completeness

Proved and exported. The honest prover's actual witness generators satisfy every
constraint for every input satisfying the unchanged native specification.

See the [detailed completeness summary](docs/completeness.md) for the proved local
lemmas, top-level assembly, validation scope, and remaining acceptance checks.

- **C1, product gadgets: done.** [Gadgets.lean](Baseline/ECDSA_P256_Digest/Completeness/Gadgets.lean)
  proves `mul_complete`, `mux_complete`, `matQuad_complete` and `assertQuad_complete`
  from `UsesLocalWitnessesCompleteness`. The assertion lemma additionally requires
  that the target equals the evaluated quadratic. All four lemmas are axiom-audited.
- **C2, `bits3`: done.** `bits3_complete` proves that the generated low bits and
  derived third bit satisfy all three boolean assertions for every selector in
  `0..7`. [Scalar.lean](Baseline/ECDSA_P256_Digest/Completeness/Scalar.lean) lifts
  completeness to all 256 selectors and supplies boolean bits recomposing each
  native selector. All three selector lemmas are included in the axiom audit.
  The same module proves exact native E/R/S prefix and field reconstructions,
  and completes the scalar binding, S-inverse, and range rows from `ScalarSpec`.
  `scalar_spec_of_valid_witness` extracts this premise from the unchanged native
  specification for the supplied witness.
- **C3, local loop and table proofs: done.** [Step.lean](Baseline/ECDSA_P256_Digest/Completeness/Step.lean)
  proves the first, 254 middle, and final rows under their local transition premises.
  [Loop.lean](Baseline/ECDSA_P256_Digest/Completeness/Loop.lean) extracts those
  transitions and the final X/Z conditions from native validity and proves the
  first, middle, and final rows using the actual generated witnesses. Its five
  bridge lemmas are axiom-audited and integrated with evaluated table arguments
  at the actual top-level bind offsets.
  [Table.lean](Baseline/ECDSA_P256_Digest/Completeness/Table.lean) proves the four
  precomputation checks from the native table predicate; top-level integration is proved.
- **C4, range converse: done.** [Range.lean](Baseline/ECDSA_P256_Digest/Completeness/Range.lean)
  proves `ltOrder_complete` for bounded boolean bits and the actual generated
  quotient witnesses. The native scalar bounds are connected to these checks in
  `scalar_reconstruction_complete` and integrated at the top level. Both results
  are axiom-audited.
- **C5, local inverse and curve checks: done.** `inverse_complete` and
  `onCurve_complete` compile; their native premises are extracted into `ScalarSpec`.
  Input-evaluation transport and constraint assembly are proved in
  [Main.lean](Baseline/ECDSA_P256_Digest/Completeness/Main.lean).
- **Constraint assembly: done.** `main_constraints_complete` combines every row
  using the actual local witness generators and unchanged native specification.
  It builds under the default proof budgets and is persistently axiom-audited.
  `main_completeness` supplies the public wrapper and trivial prover postcondition;
  the submission exports it as `Solution.ECDSA_P256_Digest.completeness`.

### Validation

Run `scripts/check.sh` for source-integrity checks, deterministic vector import,
the Lean build, regressions, the permitted-axiom audit, and Lean/Rust vector checks.
It builds `Tests.Axioms` and its submission dependencies before auditing them;
the default `lake build` alone does not build the submission.

For a focused soundness and completeness check:

```sh
lake build Solution.ECDSA_P256_Digest.Main Tests.Axioms
python3 scripts/check_axioms.py
```

The completed submission passed `scripts/check.sh` on 2026-11-10 in 71.42 seconds,
including all twenty-six axiom-audit roots and the 276-case Lean/Rust vector suites.
The current axiom audit includes
including the completed selector, range, native scalar reconstruction, and
native-spec scalar extraction lemmas, the five native-loop bridges, and native
premise extraction, full constraint assembly, the public completeness wrapper,
and exported completeness. Neither exported correctness theorem depends on `sorryAx`.

The actual comparator accepted `configs/ECDSA_P256_Digest.json`, printing
"Your solution is okay!" after Lean kernel replay. A fresh project build and
comparison took 770.94 seconds, below the 1200 s verifier limit; dependency caches
were retained. With existing project artifacts, comparison took 77.59 seconds.
All four positive/negative comparator fixtures also passed. The pinned C++
cross-check passed all 276 cases (200 evaluated, 76 byte-envelope rejections).

These runs use the unsandboxed development shim, not production Landrun isolation.
They do not establish cold dependency-build or production performance. See
[validation](docs/validation.md) for reproduction commands and scope.

### Optimization follow-up

Keep circuit changes separate from the soundness milestone and finish completeness
before changing the accepted relation's implementation. Any cost reduction must
preserve every supplied-witness check and re-establish the affected proof obligations.

The proved `middle_count` in [Cost.lean](Baseline/ECDSA_P256_Digest/Cost.lean)
accounts for 8,636 allocations and 9,398 constraints: 18,034 of the 19,630 score
units, about 92%. These 254 iterations are the main target for future circuit
optimization; this breakdown does not establish that any checks can be removed.

[docs/optimization.md](docs/optimization.md) describes two changes to the loop body,
that bring the cost to 18,612 without removing any check. They are implemented in
[`Optimized/`](Optimized/ECDSA_P256_Digest/) with a proved cost and gadget soundness, but
are not yet the submitted circuit.

The proof already avoids unrolling the loop through indexed induction and sealed
gadgets. Retain the bidirectional `loopConstraints_iff_rows` lemma for completeness;
further proof simplification should be guided by measured elaboration costs.

### Conventions for proof files

- Start every soundness or completeness file with `seal_gadgets`
  ([`Seal.lean`](Baseline/ECDSA_P256_Digest/Seal.lean)), and open gadgets only with
  `simp only [g]`, `rw [g]` or `unfold g`. Without the seal, any hypothesis about a gadget's
  constraints gets reduced, which unfolds the whole operation list (e.g. `ltOrder`'s 34 runs of
  256-term sums) and times out.
- Write `ZMod.val x` rather than `x.val` on field elements.
- Avoid `set` on large goals.
- Avoid `rw` on inequalities whose sides are large terms: its closing `rfl` can evaluate them.
