# Interval calculations
Version 1.00 — October 28, 2026 — Dave Goel.

Copyright (C) Dave Goel 2026--now. All rights reserved.

The programs verify the numerical inequalities used in the paper. `MANIFEST.json` and `SUPPLEMENTAL_MANIFEST.json` identify the release source bytes. `SOURCE_PROVENANCE.json` pairs their checksums with the original source checksums using neutral identifiers. `AST_EQUIVALENCE.json` records the exact source-equivalence check: mathematical expressions, numerical constants, domains and controls are unchanged outside the stated naming, path and metadata substitutions.

Use Python 3.12.3 with the versions in `REPLAY_DEPENDENCIES.json`: python-flint 0.9.0 with FLINT 3.6.0, mpmath 1.4.1, NumPy 2.5.4 and SciPy 1.18.1. The runner checks the actual versions and requires assertions enabled. From this directory, supply the full path of that environment's Python interpreter:

```bash
/path/to/venv/bin/python replay_primary.py --test --python /path/to/venv/bin/python --output-dir replays/test_run
/path/to/venv/bin/python replay_primary.py --replay --python /path/to/venv/bin/python --output-dir replays/release_primary
```

Each output directory must be new. Tests alone do not establish full coverage. A completed replay has `status=PASS` and `primary_coverage_complete=true` in its `SUMMARY.json` only after seven preliminary test jobs and eleven coverage/control jobs have passed. Every child must return zero and emit its required success/control markers; unexpected failures stop the run and retain its output. A deliberately false control succeeds when its claim is refused. The runner executes serially with one numerical thread.

Fresh run records use path aliases at their first serialization: `.` is this directory, program paths are relative to it, and output paths beneath it remain relative to it. `python` identifies the explicitly supplied interpreter; `python-environment/<package>` identifies its external installed package. For an output directory outside this tree, `run-output/<filename>` is relative to the explicitly supplied output directory. These are documented aliases, not rewritten historical logs. Raw child stdout and stderr are saved directly from the new execution.

## Primary numerical coverage

| Calculation | Program | Domain |
|---|---|---|
| Negative Omega | `programs/omega_negative.py` | `[1.001,1.2336025]` |
| Omega root and positivity | `programs/omega_positive.py`, using the preceding local helper | Positive slope on `[1.2336025,1.2336027]`; positive Omega on `[1.2336027,1.268]` |
| Local threshold pc | `programs/local_threshold.py` | Compact signs, derivative window and bracket `[1.213490304,1.213490305]` |
| Axis boundary bulk | `programs/boundary_bulk.py` | Three adjacent intervals covering `[1.000001,1.2134]` |
| Axis boundary sliver | `programs/boundary_sliver.py` | `[1.2134,1.2134904] x [0,0.03]`, plus the local-threshold gap bound |
| Strip corner | `programs/strip_corner.py` | `p in [p0,1.2341027]`, `0<delta<=0.05`, all `0<s<1`, conditional on Omega nonnegative |
| Strip bulk | `programs/strip_bulk.py --corner main` | `[1.2336025,1.268] x [0.05,1]` and `[1.2341027,1.268] x [0,0.05]`, all `0<s<1` |
| Two fixed wide-chord examples | `certify_wide_chord.py --verify`, with `--test` for controls | The two exact rational witnesses printed in the paper |

All domain decimals denote exact rational numbers. The paper supplies the open-endpoint estimates, contact and envelope reductions, involution identity, root/sign implications and tail bounds. The corner is used for p at least the exact root p0; its derivative enclosures may use a larger rational rectangle beginning below p0. Numerical replay is conditional on those analytic arguments.

Alternate source programs, including `strip_corner_independent.py` and `strip_bulk_independent.py`, are supplied under `programs/`. They are not part of the primary replay; their older execution records are not presented as fresh release logs. The comparison programs use release-relative inputs when launched from this directory. The exploratory search programs are separate from the rigorous primary route.

The final release inventory and checksums are in the parent `FILE_MANIFEST.json`. A recorded full replay has a separate evidence manifest covering its summary, status records and direct stdout/stderr files.
