# Interval calculations
Version 1.10 — October 31, 2026 — Dave Goel.

Copyright (C) Dave Goel 2026--now. All rights reserved.

The programs verify the numerical inequalities used in the paper. `MANIFEST.json` and `SUPPLEMENTAL_MANIFEST.json` identify the release source bytes. `SOURCE_PROVENANCE.json` pairs their checksums with the original source checksums using neutral identifiers. `AST_EQUIVALENCE.json` records the exact source-equivalence check: mathematical expressions, numerical constants, domains and controls are unchanged outside the stated naming, path and metadata substitutions.

Use Python 3.12.3 with the versions in `REPLAY_DEPENDENCIES.json`: python-flint 0.9.0 with FLINT 3.6.0, mpmath 1.4.1, NumPy 2.5.4 and SciPy 1.18.1. One way to install them: `python3.12 -m venv venv`, then `venv/bin/pip install python-flint==0.9.0 mpmath==1.4.1 numpy==2.5.4 scipy==1.18.1` (the python-flint wheel includes FLINT). The runner checks the actual versions and requires assertions enabled. From this directory, supply the full path of that environment's Python interpreter:

```bash
/path/to/venv/bin/python replay_primary.py --test --python /path/to/venv/bin/python --output-dir replays/test_run
/path/to/venv/bin/python replay_primary.py --replay --python /path/to/venv/bin/python --output-dir replays/my_replay
```

Each output directory must be new; `replays/release_primary` holds the recorded replay of October 28, 2026. Tests alone do not establish full coverage. A completed replay has `status=PASS` and `primary_coverage_complete=true` in its `SUMMARY.json` only after seven preliminary test jobs and eleven coverage/control jobs have passed. Every child must return zero and emit its required success/control markers; unexpected failures stop the run and retain its output. A deliberately false control succeeds when its claim is refused. Arb prints a ball as `[+/- R]` when it cannot give even one digit of it; this says only that the ball lies in [−R, R]; where a claim needs a lower bound, the log prints the certified lower end separately (for example `g >= [0.292063 +/- 3.83e-7]` in `strip_corner.stdout.log`). The runner executes serially with one numerical thread.

Run records name files relative to this folder. In them, `python` is the interpreter given with `--python`, `python-environment/<package>` is a package installed in its environment, and `run-output/<filename>` is a file in an output directory outside this folder. Each job's stdout and stderr are saved as the job printed them.

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
| Two fixed wide-chord examples | `certify_wide_chord.py --verify`, with `--test` for controls | The two exact rational witnesses printed in Proposition 6.3 of the expanded version |
| The same two examples, at the printed bounds | `prop_6_3_check/certify_wide_chord.py` (version 0.20; not run by `replay_primary.py`); see `prop_6_3_check/README.md` | S < −0.00196 and S < −0.00074, as printed in Proposition 6.3 |

All domain decimals denote exact rational numbers. The paper supplies the open-endpoint estimates, contact and envelope reductions, involution identity, root/sign implications and tail bounds. The corner is used for p at least the exact root p0; its derivative enclosures may use a larger rational rectangle beginning below p0. Numerical replay is conditional on those analytic arguments.

Alternate source programs, including `strip_corner_independent.py` and `strip_bulk_independent.py`, are supplied under `programs/`. They are not part of the primary replay; their older execution records are not presented as fresh release logs. The comparison programs use release-relative inputs when launched from this directory. The exploratory search programs are separate from the rigorous primary route.

The final release inventory and checksums are in the parent `FILE_MANIFEST.json`. A recorded full replay has a separate evidence manifest covering its summary, status records and direct stdout/stderr files. Old labels in the recorded files: the "Proposition 4.3 endpoint estimate" of `REPLAY_DEPENDENCIES.json` is Lemma A.1 of the paper; "Gamma" in the negative-Omega and boundary-sliver logs is Ω; the keys `proposition_2_1_S` and `section_4_2_S` of `certify_wide_chord.py` version 0.10 are the two sums of Proposition 6.3 of the expanded version; the boundary-sliver line "1 - lam_loc(p) <= 3/100" is checked as 2√T(p) ≤ 3/100, that is, T(p) ≤ 0.015² (Table 1 of the paper); `T1` in `boundary_sliver.py`, `strip_corner.py`, `strip_bulk.py` and `strip_bulk_independent.py` is Z_1 of the paper.
