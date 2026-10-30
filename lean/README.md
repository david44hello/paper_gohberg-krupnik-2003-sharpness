# The Gohberg–Krupnik sharpness belief for aI+bH (2003) is fully resolved — Lean 4 proof

The paper: its link will be added here when it is posted.

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

The proof assumes three theorems that the paper cites, two of Hollenbeck and Verbitsky (2000) and one of Hollenbeck,
Kalton and Verbitsky (2003); 29 claims use them. 22 claims are proved given interval estimates that are checked by
computer, by the programs in [../interval/](../interval/). [AUDIT.md](AUDIT.md) names them, claim by claim.

Copyright (C) Dave Goel 2026--now. All rights reserved.
