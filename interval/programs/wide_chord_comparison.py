#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# wide_chord_comparison.py - Gohberg–Krupnik: independent Arb check (my spline_certificate.py) of route A's wide-chord certificates [-route C]
## version 0.10 - route C 20261027_1548 ET - WC = 3-kink tent c = (0, 1, 0) at (-s, 0, s), s in [pi/p, pi]; parameters from
##   archived verification record (eps, y0, y1); s = rational near pi - eps (any s in [pi/p, pi] is valid)
import hashlib
import math
import sys
from fractions import Fraction

sys.path.insert(0, "programs")
from spline_certificate import check_certificate  # noqa: E402

CERT_CODE = "programs/spline_certificate.py"
# (label, p, lam, C, eps, y0, y1, expect_proved)
CASES = [
    ("CTRL above norm", "3/2", "9/10", "5041/5000", "1044573/1000000", "1813/1000", "1263/1000", False),
    ("CTRL above C_WC", "21/20", "1/2", "89/25", "26433/500000", "81/500", "3/250", False),
    ("POINT", "21/20", "1/2", "7/2", "47617/1000000", "83/500", "11/1000", True),
    ("POINT", "21/20", "1/2", "353/100", "51741/1000000", "41/250", "3/250", True),
    ("POINT", "21/20", "9/10", "73/50", "3/4000", "37/200", "1/1000", True),
    ("POINT", "8/7", "3/5", "367/250", "27361/200000", "13/25", "101/1000", True),
]


def wc_cert(p, lam, C, eps, y0, y1):
    s = Fraction(math.pi - float(Fraction(eps))).limit_denominator(10 ** 9)
    return {"p": p, "alpha": ["1", "0"], "beta": [lam, "0"], "C": C,
            "nodes": [{"t": str(-s), "c": "0", "y": y1}, {"t": "0", "c": "1", "y": y0}, {"t": str(s), "c": "0", "y": y1}]}, s


def main_wc():
    md5_start = hashlib.md5(open(CERT_CODE, "rb").read()).hexdigest()
    print(f"md5 {CERT_CODE} start {md5_start}")
    ok_all = True
    for label, p, lam, C, eps, y0, y1, expect in CASES:
        cert, s = wc_cert(p, lam, C, eps, y0, y1)
        total, ws = check_certificate(cert)
        proved = bool(total < 0)
        ok = proved == expect
        ok_all &= ok
        print(f"{label}: p={p} lam={lam} C={C} s={s} (= pi - {math.pi - float(s):.6f}): S = {total.mid().str(8)} +/- {total.rad().str(2)} "
              f"weights {[w.mid().str(5) for w in ws]} -> {'PROVED norm > C' if proved else 'not proved'} [{'ok' if ok else 'UNEXPECTED'}]")
    md5_end = hashlib.md5(open(CERT_CODE, "rb").read()).hexdigest()
    print(f"md5 end {md5_end} ({'same' if md5_end == md5_start else 'CHANGED'}); all as expected: {ok_all}")
    return 0 if ok_all and md5_end == md5_start else 1


def main():
    sys.exit(main_wc())


if __name__ == "__main__":
    main()
