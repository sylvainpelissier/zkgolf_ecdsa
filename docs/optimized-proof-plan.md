# Plan: make the 18,612 circuit the proved submission

Notes written 2026-11-11. Nothing in this plan has been started.

## Where things stand

- Branch `baseline-sylvain` holds the finished 19,630 submission (soundness and
  completeness both proved) plus the cherry-picked commit `0695b1f` "Add Optimization".
  That commit is local only: the branch is one commit ahead of `origin/baseline-sylvain`.
- `lake build Optimized` passes on this branch.
- The optimized circuit `main10` lives in `Optimized/ECDSA_P256_Digest/`. Proved for it:
  the cost (`main10Cost`, 8,787 allocations + 9,825 constraints = 18,612) and the
  soundness of the two new gadgets (`doubleE10_sound`, `assertCross_sound`).
- The submission in `Solution/` still uses `Baseline.ECDSA_P256_Digest.main`, and the
  cost claim in `Challenge/Instances/ECDSA_P256_Digest/Cost.lean` is still 9296 / 10334.

## Approach: swap the two gadgets in place in `Baseline/`

Every proof above the loop body (`Loop`, `Table`, `Scalar`, `Range`, both `Main`s) talks
to the loop only through interface lemmas about `step`, `assertPoint` and `middle`. If
the optimized doubling and output check take over those names in
`Baseline/ECDSA_P256_Digest/Circuit.lean`, the interface statements stay the same and
only the leaf lemmas change.

Rejected alternative: a parallel `Optimized` proof tree. It would duplicate `main_r1cs`,
`main_cw`, `main_plain`, `main_spec`, the loop proofs and `main_constraints_complete`
(roughly 1,500 lines) only to rename `main` to `main10`. The 19,630 circuit stays
recoverable from git once it is tagged.

## The one real difficulty

The current `assertPoint_sound` holds for any `QPoint`. The five-product check
(`assertCross`) does not: it reads six fields of the point and is only correct when the
point has the shape `addTail` returns:

- X = `⟨s, A, −u, B⟩`
- Y = `⟨A, C, D, B⟩`
- Z = `⟨u, C, s, D⟩`

with `s = t3_2`, `A = X3t_3`, `u = t5_3`, `B = t4_5`, `C = Z3t_3`, `D = t1_4`
(`addTail`, `Circuit.lean` line 131). `assertPoint5` reads them as
`q.1.a, q.1.b, q.2.2.a, q.1.d, q.2.1.b, q.2.1.c`.

So the proofs need a shape predicate, say `CrossShape env q`, and a lemma that `addE`
and `step` outputs satisfy it. It only has to hold after evaluation:

- `eval q.1.c = −eval q.2.2.a`
- `eval q.2.1.a = eval q.1.b`
- `eval q.2.1.d = eval q.1.d`
- `eval q.2.2.b = eval q.2.1.b`
- `eval q.2.2.c = eval q.1.a`
- `eval q.2.2.d = eval q.2.1.c`

## Steps

| # | File | Change |
|---|---|---|
| 0 | git | Tag the current head (e.g. `baseline-19630`), work on a new branch. |
| 1 | `Baseline/…/Circuit.lean` | Replace the `doubleE` body with `doubleE10`'s; add `rootQ` and `assertCross`; make `assertPoint` call `assertCross`. Lengths: `doubleE_len` 11→10, `step_len` 31→30, `assertPoint_len` 3→2, `middle` 34→32. |
| 2 | `Baseline/…/Seal.lean` | Add `assertCross` to `seal_gadgets`. |
| 3 | `Baseline/…/Cost.lean`, `Challenge/Instances/…/Cost.lean` | Move the counts from `Optimized/…/Cost.lean`: doubling `⟨10,10⟩`, output check `⟨2,5⟩`, step `⟨30,30⟩`, middle `254*⟨32,35⟩`. Claim becomes 8787 / 9825. |
| 4 | `Soundness/Curve.lean` | Replace the `doubleE_sound` proof with the `doubleE10_sound` one, plus `rootQ_spec`. Statement unchanged. |
| 5 | `Soundness/Step.lean` | Add `CrossShape`, `addTail_crossShape`, `step_crossShape`. `assertPoint_sound` gains a `CrossShape` hypothesis and is proved from `assertCross_sound`. `stepRow_sound` keeps its statement and supplies the shape internally. |
| 6 | `R1CS.lean` | Re-run `doubleE_r1cs` and `doubleE_output` on the new body. `assertPoint_r1cs` becomes two `mul` rows and three `assertZero` rows. |
| 7 | `Plain.lean` | `assertPoint_plain` uses `mul_plain`; `doubleE_plain` should pass unchanged. |
| 8 | `CompWit.lean` | `doubleE_out_below`: `n + 11` → `n + 10`. `step_cw`: offsets `n+11+14` → `n+10+14`. `assertPoint_cw` has two witnesses now, so it needs `mul_cw` leaves. Fix offsets in `middle_cw` and `main_cw`. |
| 9 | `Completeness/Gadgets.lean` | `doubleE_complete` should pass as is. `assertPoint_complete` takes `CrossShape`; the two witnesses are products and the three rows follow from the point equality by `linear_combination`. |
| 10 | `Completeness/Step.lean`, `Completeness/Main.lean` | `stepRow_complete` passes the shape. `middle_len` 8636 → 8128 (254×32). Re-check the offset arithmetic in `main_constraints_complete`. |
| 11 | cleanup | Delete `Optimized/`, `Optimized.lean` and its `lean_lib` entry in `lakefile.lean`. Update the README status table and numbers, the "not applied" status in `docs/optimization.md`, and `docs/soundness.md`. |
| 12 | validation | `scripts/check.sh`, the axiom audit in `Tests/Axioms.lean`, `check_cpp.py`, `check_comparator.py`, `package.py`. |

## Order

1–3 first: a building circuit with the new cost. Then 4–5 (soundness), 6–8 (structural
proofs), 9–10 (completeness), 11–12. Each group builds on its own, so each can be its
own commit.

## Risks

- **Steps 5 and 9 (main risk):** if the syntactic `−u` in `addTail` does not reduce
  cleanly under `circuit_norm`, the shape lemma gets fiddly. Fallback: give
  `assertPoint` the six `addTail` forms directly instead of a `QPoint`.
- **Step 10:** `main_constraints_complete` has hard-coded offsets after the loop and may
  need more than a number change.
- **Steps 4, 6, 7, 8 (low risk):** they reuse proofs or tactics that already work on the
  same row shapes.
- **Axioms:** `rootQ_spec` and `2 ≠ 0` use `decide +kernel`. They build, but the audit
  must confirm nothing beyond `propext`, `Quot.sound`, `Classical.choice`.

## Open decisions

- Push `0695b1f` to `origin/baseline-sylvain`, or keep it local until the proofs land?
- Keep `Optimized/` as a reference after the swap, or delete it (step 11)?
