# Proposition 6.3 of the expanded version
Version 1.00 — October 31, 2026 — Dave Goel.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.

`certify_wide_chord.py` (version 0.20) checks the two bounds of Proposition 6.3 of the expanded version at the values printed there: S < −0.00196 for p = 21/20 and S < −0.00074 for p = 8/7. It uses the same exact rational witnesses as `../certify_wide_chord.py` (version 0.10). Version 0.10 is the program of the primary replay; its output names the two sums `proposition_2_1_S` and `section_4_2_S`, and it checks the second sum only for S < 0. The enclosures printed by both versions are identical.

Use the Python interpreter and package versions of `../REPLAY_DEPENDENCIES.json`. From this directory:

```bash
/path/to/venv/bin/python certify_wide_chord.py --verify
/path/to/venv/bin/python certify_wide_chord.py --test
```

`verify.stdout.log` and `test.stdout.log` are the outputs of these two commands on October 31, 2026 (Python 3.12.3, python-flint 0.9.0, 160-bit precision); both returned 0 and wrote nothing to standard error.
