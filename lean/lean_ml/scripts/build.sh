#!/usr/bin/env bash
# build.sh: build the QECML library and print the axioms of its main theorems.
# Needs elan (the Lean toolchain manager); the first step downloads the prebuilt Mathlib for the pinned revision.
# The Lean version is pinned by lean-toolchain and Mathlib by lake-manifest.json.
# Usage, from any directory: bash scripts/build.sh
set -euo pipefail
cd "$(dirname "$0")/.."
lake exe cache get
lake build
lake env lean scripts/Axioms.lean
