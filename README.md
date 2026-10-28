# Certified lower bounds on the optimal-decoding threshold of the surface code

This repository holds the paper "Certified lower bounds on the optimal-decoding threshold of the surface code" by
Tejasvi S. Tomar, its source in one LaTeX file, and the two Lean 4 developments that prove its theorems. The
registrations, programs, certificate data and check outputs are in the data record that the paper cites in its
section "Code and data".

| path | content |
|---|---|
| `paper/main.pdf`, `paper/main.tex` | the paper and its source, bibliography included |
| `lean/lean_ml/` | Lean proofs of Theorem 2.1 (library QECML) |
| `lean/lean_counting/` | Lean proofs of Theorems 2.2 to 2.5 (libraries QEC and QECCountComp) |
| `lean/*.SHA256SUMS` | the SHA-256 of every file of each Lean tree; the paper gives the SHA-256 of these two files |
| `lean/*_axioms.txt` | the axioms on which each main theorem depends, as printed by Lean |

Each Lean tree has a README with build instructions. Both use Lean 4.35.0-rc3 and Mathlib commit c55e6e786f49,
pinned by `lean-toolchain` and `lake-manifest.json`. In `lean_ml/`, `bash scripts/build.sh` builds the library and
prints the axioms of the main theorems in about six minutes on one core. In `lean_counting/`, the modules of the
general argument build in a few minutes; the data and kernel check modules of the large certificates are regenerated
from the certificate files in the data record, as `lean_counting/README.md` explains.

To check a Lean tree against its checksum list:

    cd lean/lean_ml
    sha256sum -c ../lean_ml.SHA256SUMS

`CITATION.cff` gives the paper's citation. The paper (`paper/`) is licensed under the Creative Commons Attribution 4.0
International license (`LICENSE-CC-BY-4.0.txt`), and the Lean sources (`lean/`) under the Apache License 2.0
(`LICENSE-APACHE-2.0.txt`). Copyright 2026 Tejasvi S. Tomar.

The file `lean/lean_counting/QEC/KChecks/T8K/tree.json` (108 MB) is stored with Git LFS; install Git LFS before
cloning, or download the Lean archive from the record that the paper cites.
