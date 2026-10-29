# The Gohberg–Krupnik sharpness belief for aI+bH (2003) is fully resolved: the Lean proof

Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.

This folder is the Lean 4 formalization of the paper (version 0.90). Nine interval estimates of the paper are not proved in Lean: `GKSharp/ComputerChecked.lean` states each one as a named computer check, and the proofs use them only as explicit hypotheses. The programs that verify them are in `../interval/`. Three published theorems are assumed: two of Hollenbeck and Verbitsky (2000) and one of Hollenbeck, Kalton and Verbitsky (2003). `GKSharp/Cited/` states each one with its source. `AUDIT.md` lists each public Lean statement (`GKSharp/Paper/Statements.lean`) with its place in the paper and the computer checks and published theorems it uses; the other claims are tied to their exact Lean statements in `GKSharp/Paper/CoverageLinks/`.

Build, from this folder: `lake exe cache get && lake build` (Lean 4 v4.35.0, Mathlib commit 56a005855ea1). `bash scripts/check.sh` (Python 3 and ripgrep) checks the sources and regenerates `AUDIT.md`.
