# Validation of the circuit target

Completed-submission local validation (2026-11-10):

| Check | Result |
| --- | --- |
| Lean 4.34.0 challenge and submission builds | Passed |
| Infinity/exceptional-affine regressions | Passed |
| Trusted axiom audit | 26 roots passed; standard axioms only |
| Lean circuit-path vectors | 276/276 |
| RustCrypto-based vector checks | 276/276; 262 original-message checks |
| External C++ byte-adapter diagnostics | 276/276 (200 C++, 76 envelope rejections) |
| Comparator positive/negative checks | 4/4 |
| Actual submission comparator and Lean kernel replay | Accepted; "Your solution is okay!" |
| Fresh project verification, dependency caches retained | 770.94 s; below 1200 s |
| Source hashes and deterministic corpus | Passed |

`scripts/check.sh` completed in 71.42 seconds initially and 115.71 seconds on the
final rerun after fresh project verification. Actual submission comparison took
77.59 seconds with existing project artifacts, and 770.94 seconds after
`lake clean ECDSAGolf`. Dependency build caches were retained. These runs use the
pinned comparator's unsandboxed development shim with Nanoda disabled, as
configured by the challenge. They do not establish production sandbox acceptance
or cold dependency-build performance.

After building the pinned comparator as described in
[publication.md](publication.md), reproduce actual submission verification with:

```sh
lake clean ECDSAGolf
COMPARATOR_LANDRUN=/tmp/ecdsa-comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=/tmp/ecdsa-comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
  /usr/bin/time -p lake env /tmp/ecdsa-comparator/.lake/build/bin/comparator \
  configs/ECDSA_P256_Digest.json
```

Local run logs are generated under `dist/comparator-checks/`, including
`actual-submission.log` and `actual-submission-fresh.log`.

The authoritative challenge relation wraps Longfellow's `ValidEcdsaWitness` at
commit `4fe092be7e8e9634cd3b27daf55695a3a416043e`. The circuit field is P-256's base
field. The wrapper directly checks the supplied native witness.

## Vector coverage

The 276 inputs comprise 262 unchanged Wycheproof cases and 14 local regressions.
The tested Longfellow path accepts 166 and rejects 110. Expected ordinary ECDSA,
direct-x and circuit-path results are stored separately. Fourteen inputs are
ordinary-ECDSA valid but rejected by the circuit path: three direct-x overflows
and eleven exceptional table cases (including existing upstream fixtures).

- RustCrypto p256 0.13.2 verifies the ordinary signatures and independently
  reconstructs the point and table exceptions for all 276 inputs. All 262
  upstream messages are also checked with the message API.
- The Lean oracle uses upstream projective arithmetic, affine equality checks,
  selectors and the circuit loop to test generated witnesses.
- `scripts/check_cpp.py` compiles a focused adapter against the pinned, unmodified
  C++ `verify_signature3` evaluator and witness generator. It evaluates 200 cases;
  the other 76 fail the declared byte/canonical-scalar envelope before the core
  circuit is called. See `cpp-validation.json`.

These tests establish observed agreement on the corpus, not a universal decision
procedure for existential witnesses. Challenge acceptance checks the supplied native witness directly using the
upstream relation, not an existential statement or executable oracle. The Lean model uses
selectors 0..7; C++ uses their centered encoding 2*v-7.

## Proof and integration checks

`scripts/check.sh` checks original/local source hashes, deterministic corpus
reconstruction, the Lean build, regressions, axiom policy and vector oracles.
`Tests/Regressions.lean` retains the PR's infinity-representation regression and
checks that G+(-G) has zero Z and nonzero Y. A general Lean lemma proves that such
a point cannot satisfy the affine point-equality assertion.

The trusted-root audit covers the wrapper, `ValidEcdsaWitness`, scalar
multiplication, the Pratt primality proof, and the soundness and completeness
proofs, including exported submission correctness. All 26 roots pass with only
`propext`, `Classical.choice`, and `Quot.sound` allowed. No BN254 or P-256
primality axiom is added.

The comparator checks acceptance of a valid proof using the actual target,
and rejection of an unfinished proof, changed statement and template submitted
as a solution. Its exact revisions and outcomes are recorded in
`comparator-validation.json`. It is tested with self-authored fixtures using the
upstream development shim, not a production sandbox. Separately, the actual
submission passed all seven configured theorem comparisons, both definition
comparisons, the permitted-axiom policy, and Lean kernel replay.

The local R1CS submission has proved cost 19,630 (9,296 witness allocations and
10,334 constraints), with all seven submission obligations proved. This does not
set an official challenge baseline score. No proof of the C++ compiler,
production deployment or full credential protocol is claimed. Contestants must
prove equivalence to the pinned circuit relation, not completeness for all
mathematical ECDSA inputs.

The 276 serialized fixtures remain external adapters after the native-interface
migration. Their 76 byte-envelope rejections do not establish native constraints.
The comparator positive fixture now proves definitional equivalence directly to
`ValidEcdsaWitness` for the supplied native input/witness tuple. The fixed 1,037
input elements are outside additional-allocation scoring.

The native regression also proves that a supplied witness with `rx_inv = 0`
cannot satisfy the target, independently of the key or digest.
