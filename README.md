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

This package defines a single signature-component optimization challenge; no
contestant circuit or measured baseline is supplied. See
[validation](docs/validation.md), [provenance](docs/references.md), and
[handoff](docs/publication.md).

## Solution status

The submission module is [`Solution/ECDSA_P256_Digest/Main.lean`](Solution/ECDSA_P256_Digest/Main.lean).
It re-exports the circuit and proofs in [`Baseline/ECDSA_P256_Digest/`](Baseline/ECDSA_P256_Digest/).
The circuit scores 19,630: 9,296 allocations and 10,334 constraints.

| Obligation | Status | Proof |
| --- | --- | --- |
| `mainCost` | done | [`Cost.lean`](Baseline/ECDSA_P256_Digest/Cost.lean) |
| `isR1CS` | done | [`R1CS.lean`](Baseline/ECDSA_P256_Digest/R1CS.lean) |
| `witgenIsIR` | done | [`Plain.lean`](Baseline/ECDSA_P256_Digest/Plain.lean) |
| `requirementsChannelsLawful` | done | [`Plain.lean`](Baseline/ECDSA_P256_Digest/Plain.lean) |
| `computableWitness` | done | [`CompWit.lean`](Baseline/ECDSA_P256_Digest/CompWit.lean) |
| `soundness` | in progress | [`Soundness/`](Baseline/ECDSA_P256_Digest/Soundness/) |
| `completeness` | not started | — |

The comparator accepts the statements. It currently stops at `sorryAx`, which comes from the
two unfinished obligations.

### Soundness

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

Remaining:

- **S8, the loop.**
  - Prove a list lemma: `EcdsaLoopConstraintsF` from infinity holds exactly when the first step
    and every middle step hold.
  - Discharge the first step with `assertFirst`, since `addE (0, 1, 0) T` reduces to `(x·y, y², y·z)`.
  - Discharge the 254 middle steps with `stepRow_sound`, over the `forEach` in `middle`.
  - Discharge the last step and the final `X = 0`, `Z = 0` from `ecdsaLoopResultF`.
  - The vendored `EcdsaLoopConstraintsF_cast_eq` / `ecdsaLoopResultF_cast_eq` may help.
- **S10, assembly.**
  - Split `main`'s constraints with `soundness_bind`.
  - Feed the pieces to `scalar_spec_circuit`, `table_sound` and S8.
  - Rewrite `tablePK`, `tablePre` and `preList` into the input's fields with `InputEval`.
  - Prove `Solution.soundness` by unfolding `GeneralFormalCircuit.Soundness`.

### Completeness

Not started. The honest prover's witnesses must satisfy every constraint. Most of it reuses
the soundness algebra in the other direction:

- **C1, product gadgets:** `mul`, `mux`, `matQuad` and `assertQuad` follow directly from their
  witness generators.
- **C2, `bits3`:** for `bi ∈ 0..7`, the generator's `v.bits 2` gives the right bits.
- **C3, loop and table:** the identities of S5–S7, read the other way.
- **C4, `runCheck`:** needs the converse of S9: if the scalar is below `n`, every run check can be
  satisfied. This also needs a `decide +kernel` fact that the runs contain only zero bits of `n − 1`.
- **C5, inverses and curve checks:** these come directly from the spec.

### Final validation

- Run the comparator on `configs/ECDSA_P256_Digest.json` until it prints "Your solution is okay!".
- Check that the full build stays within the 1200 s verifier limit.
- Cross-check against Longfellow with `scripts/check_cpp.py`.

### Conventions for proof files

- Start every soundness or completeness file with `seal_gadgets`
  ([`Seal.lean`](Baseline/ECDSA_P256_Digest/Seal.lean)), and open gadgets only with
  `simp only [g]`, `rw [g]` or `unfold g`. Without the seal, any hypothesis about a gadget's
  constraints gets reduced, which unfolds the whole operation list (e.g. `ltOrder`'s 34 runs of
  256-term sums) and times out.
- Write `ZMod.val x` rather than `x.val` on field elements.
- Avoid `set` on large goals.
- Avoid `rw` on inequalities whose sides are large terms: its closing `rfl` can evaluate them.
