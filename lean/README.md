# When is the Gohberg–Krupnik lower bound for aI+bH sharp? — Lean 4 proof

The paper: https://doi.org/10.5281/zenodo.23732817

This folder is a Lean 4 proof of the paper's results.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone --branch v3.90 --single-branch https://github.com/david44hello/paper_gohberg-krupnik-2003-sharpness.git
cd paper_gohberg-krupnik-2003-sharpness/lean
./check.sh
```

Its last lines look like:

```
FINAL GATE PASS: placeholders only as whole bodies of the 0 listed OPEN rows; statuses match the list.
PASS (final): project builds; source policy passes; the only gaps are the listed OPEN rows.
```

The Lean proof takes as given interval estimates, checked by the programs in [../interval/](../interval/), and theorems from papers that the paper cites; [AUDIT.md](AUDIT.md) and [AUDIT_NOTES.md](AUDIT_NOTES.md) name them.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
