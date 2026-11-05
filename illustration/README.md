# Illustration-only values
Version 1.00 — October 31, 2026 — Dave Goel.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.

`lambda_one.py` computes the two values that the paper labels as computed numerically: λ1(1.1) ≈ 0.389 in the caption of Figure 1, and the lower curve λ = λ1(p) of Figure 2. It uses floating point at 20 digits (mpmath), not interval arithmetic. These values are for illustration only; the proofs do not use them. The rigorous computations are in `../interval/`.

λ1(p) is the first sign change of the positive-axis test h(·, p) on a scan of λ in (0, 1), refined by 36 bisection steps; the program's docstring states the formulas. From this directory, with the interpreter of `../interval/REPLAY_DEPENDENCIES.json`:

```bash
/path/to/venv/bin/python lambda_one.py --test
/path/to/venv/bin/python lambda_one.py --run
```

`run.stdout.log` and `test.stdout.log` are the outputs of these two commands on October 31, 2026 (Python 3.12.3, mpmath 1.4.1).
