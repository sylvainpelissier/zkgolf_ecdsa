#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
python3 scripts/check_sources.py
python3 scripts/import_vectors.py --check
lake build
lake build Tests.Regressions Tests.Axioms
python3 scripts/check_axioms.py
lake exe vectors
cargo run --locked --release --manifest-path reference/Cargo.toml
