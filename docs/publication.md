# Challenge handoff

The deliverable is a challenge-authoring package and proved local R1CS submission
pinned to Longfellow PR #215 commit `4fe092be7e8e9634cd3b27daf55695a3a416043e`.
`CHALLENGE.md` supplies page copy, `challenge.json` metadata, and
`configs/ECDSA_P256_Digest.json` the exact proof contract. The implementation and
all seven submission proofs are included under `Baseline/` and `Solution/`.
The trusted challenge template's placeholders must not be submitted as a solution.

The target is Longfellow’s `ValidEcdsaWitness` circuit model over the P-256
base field, with the native pointwise interface in `Challenge/Specs/ECDSAP256.lean`.
Do not substitute the broader `StandardEcdsaVerify` proposition.

The supported toolchain is Lean 4.34.0, with exact Clean and Mathlib revisions
in `lakefile.lean` and transitive pins in `lake-manifest.json`. The inspected
zkGolf public repository uses 4.33.1; deployment would need a compatible cached
image. No deployment or remote registration is part of this deliverable.

## Reproduce comparator checks

```sh
git clone https://github.com/leanprover/comparator.git /tmp/ecdsa-comparator
cd /tmp/ecdsa-comparator
git checkout 51491237b1d2f96cca203af9c34bced6fe38e0d8
ELAN_TOOLCHAIN=leanprover/lean4:v4.34.0 lake build comparator lean4export
cd /path/to/zkgolf_ecdsa
python3 scripts/check_comparator.py /tmp/ecdsa-comparator
```

The script verifies Comparator and lean4export revision pins. Four checks cover
a valid theorem using the real acceptance relation, an unfinished proof, a
changed theorem statement, and misuse of the actual challenge template as a
solution. Logs are written to `dist/comparator-checks/`.

This local test uses upstream's development shim without Linux Landrun isolation;
use it only for the included self-authored fixtures. The deployed site's exact
checker revision and sandbox require deployment-specific validation.

## Source bundle

Run `python3 scripts/package.py`. The archive includes the `Baseline/` and
`Solution/` proof trees and their top-level Lean modules alongside the challenge,
tests, dependency pins, and reference adapters. It excludes local caches,
dependency checkouts, build outputs and credentials and contains a SHA-256 source
manifest. The comparator fixtures remain integration tests, separate from the
included R1CS submission.

With Lean/Elan, Python 3, Cargo, and dependency downloads available, extract and
verify the source bundle from the repository root:

```sh
python3 scripts/package.py
bundle_dir="$(mktemp -d)"
tar -xzf dist/ecdsa-p256-digest-source.tar.gz -C "$bundle_dir"
cd "$bundle_dir/ecdsa-p256-digest"
shasum -a 256 -c SHA256SUMS
scripts/bootstrap.sh
scripts/check.sh
```

`scripts/check.sh` builds the submission through `Tests.Axioms`, audits the proof
dependencies, and runs the Lean/Rust vectors. The default `lake build` alone does
not build the submission. Dependency caches may be reused when checking the
archive, but project build outputs must be generated from the extracted sources.

The local submission's proved cost is 18,612; this does not establish an official
baseline score. Site registration should preserve `baseline_score: null` pending
maintainer review. Site maintainers control registry and scoring UI integration.
The copied zkGolf utility files retain a provenance notice; no
upstream license was identified, so this bundle makes no new grant of rights
for those files. See `THIRD_PARTY_NOTICES.md`.

The projective-infinity fix is pinned even if the PR changes later. Changing the
pin requires an explicit review, source-hash update and rerun of validation.
Deployment and registration are outside this local deliverable.

For direct implementation validation, run `python3 scripts/check_cpp.py
/path/to/longfellow-zk` with the checkout at the pinned commit and `clang++`
available. This evaluates the real C++ constraints on generated witnesses.
