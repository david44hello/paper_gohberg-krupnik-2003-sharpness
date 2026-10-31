# The Gohberg–Krupnik sharpness belief for aI+bH (2003) is fully resolved — Lean 4 proof

The paper: https://doi.org/10.5281/zenodo.23732817

This folder is a Lean 4 proof of the paper's results.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone https://github.com/david44hello/paper_gohberg-krupnik-2003-sharpness.git
cd paper_gohberg-krupnik-2003-sharpness/lean
./check.sh
```

Its last lines look like:

```
FINAL GATE PASS: placeholders only as whole bodies of the 0 listed OPEN rows; statuses match the list.
PASS (final): project builds; source policy passes; the only gaps are the listed OPEN rows.
```

The proof of the classification (Theorem 1.1) takes as given the interval computations and two theorems that the
paper cites: the norm of P_+ (Hollenbeck and Verbitsky, 2000) and Cole's theorem in the form of Hollenbeck, Kalton
and Verbitsky (2003), Theorem 2.1. A third cited theorem, Theorem 3.1 of Hollenbeck and Verbitsky (2000) on the
real line, is used only to show that the real-line operator of Lemma 1.2 exists. 29 claims use cited theorems.
22 claims are proved given interval estimates that are checked by computer, by the programs in
[../interval/](../interval/). [AUDIT.md](AUDIT.md) names them, claim by claim.

Copyright (C) Dave Goel 2026--now. All rights reserved.
