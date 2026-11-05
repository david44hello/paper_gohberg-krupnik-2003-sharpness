#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
# wide_chord_independent.py - Gohberg–Krupnik: interval certificate for the WIDE-CHORD lower bound on the real line (beta = lam alpha) 
# version 0.10 - route A 20261027_1555 ET - first version; gamma_iv / to_iv / rational reused from arch_search.py v0.30
#
# Certificate (by hand, route A 15:45): nu(t) = sin(q(s - |t|)) on |t| <= s, 0 elsewhere, s in [pi/(2q), pi], q = p/2 in (1/2, 1).
# nu >= 0, and nu'' + q^2 nu = q (delta_s + delta_-s) - 2q cos(qs) delta_0, all three weights >= 0 because cos(qs) <= 0.
# For q-subtrigonometric phi: sum w phi = int nu d(phi'' + q^2 phi) >= 0. Real lam: Gamma_C(y, -t) = Gamma_C(y, t). So if phi <= m_C,
#   S := 2 Gamma_C(y1, s) - 2 cos(qs) Gamma_C(y0, 0) < 0   (y0, y1 any reals: Gamma >= m_C)
# rules phi out, and the norm of P+ + lam P- is > C (Theorem R "=>", C > max(1, |lam|)). Only "S.b < 0" is tested.
# usage: python wide_chord_independent.py --run
import sys
from fractions import Fraction
import numpy as np
import mpmath
from mpmath import iv
import arch_search as ac
import pencil_search as lp

Y_FINE = np.linspace(-8, 8, 16001)
N_S = 400


def best_y(cc, p, lam, t):
    """Float argmin over Y_FINE of Gamma_C(y, t) and the minimum."""
    vals = lp.gamma_c(cc, p, 1.0, lam, Y_FINE, t)
    k_best = int(np.argmin(vals))
    if k_best in (0, len(Y_FINE) - 1):
        raise RuntimeError("argmin at the y-grid edge")
    return Y_FINE[k_best], vals[k_best]


def search_s(cc, p, lam):
    """Float search: the s in [pi/p, pi] that minimises 2 Gamma(y1, s) - 2 cos(qs) Gamma(y0, 0)."""
    y0, g0 = best_y(cc, p, lam, 0.0)
    best = None
    for s_val in np.linspace(np.pi / p, np.pi, N_S)[1:-1]:
        y1, g1 = best_y(cc, p, lam, s_val)
        total = 2 * g1 - 2 * np.cos(p / 2 * s_val) * g0
        if best is None or total < best[0]:
            best = (total, s_val, y1)
    return y0, best[1], best[2], best[0]


def certify_wc(cc, p, lam, eps, y0, y1):
    """S in mpmath iv with s = pi - eps (eps > 0 rational); checks q s >= pi/2 rigorously."""
    q = ac.to_iv(p) / 2
    s_iv = iv.pi - ac.to_iv(eps)
    if not (eps > 0 and (q * s_iv).a > iv.pi.b / 2):
        raise RuntimeError("s outside [pi/(2q), pi): the centre weight would not be >= 0")
    alpha, beta = (Fraction(1), Fraction(0)), (lam, Fraction(0))
    g1 = ac.gamma_iv(ac.to_iv(cc), ac.to_iv(p), alpha, beta, ac.to_iv(y1), s_iv)
    g0 = ac.gamma_iv(ac.to_iv(cc), ac.to_iv(p), alpha, beta, ac.to_iv(y0), iv.mpf(0))
    return 2 * g1 - 2 * iv.cos(q * s_iv) * g0


def check_point(label, p, lam, cc, expect_proved):
    y0, s_val, y1, s_float = search_s(float(cc), float(p), float(lam))
    eps, y0r, y1r = ac.rational(np.pi - s_val), ac.rational(y0), ac.rational(y1)
    s_iv = certify_wc(cc, p, lam, eps, y0r, y1r)
    proved = bool(s_iv.b < 0)
    gk = lp.gk_bound(float(p), 1.0, float(lam))
    print(f"{label}: p={p} lam={lam} C={cc} ({float(cc) / gk - 1:+.3e} vs GK={gk:.10f}): s = pi - {eps}, y0={y0r}, y1={y1r}"
          f"  S_float={s_float:+.6f}  S_iv.b={mpmath.nstr(s_iv.b, 10)} -> {'PROVED norm > C' if proved else 'NOT PROVED'}"
          f"  [{'as expected' if proved == expect_proved else 'UNEXPECTED!'}]", flush=True)
    return proved == expect_proved


def main_wc_cert():
    cases = [
        ("CTRL above norm ", Fraction(3, 2), Fraction(9, 10), Fraction(10082, 10000), False),   # norm = GK = 1.0081735 there
        ("CTRL above C_WC ", Fraction(21, 20), Fraction(1, 2), Fraction(356, 100), False),     # C_WC = 3.5357743
        ("POINT lam=1/2   ", Fraction(21, 20), Fraction(1, 2), Fraction(7, 2), True),          # GK = 3.4977040 = arch
        ("POINT lam=1/2   ", Fraction(21, 20), Fraction(1, 2), Fraction(353, 100), True),
        ("POINT lam=9/10  ", Fraction(21, 20), Fraction(9, 10), Fraction(146, 100), True),     # arch 1.3828, GK 1.3417
        ("POINT p=8/7 3/5 ", Fraction(8, 7), Fraction(3, 5), Fraction(1468, 1000), True),      # arch 1.4579, GK 1.4570
    ]
    results = [check_point(*case) for case in cases]
    print(f"all {len(results)} outcomes as expected: {all(results)}")


def main():
    if "--run" not in sys.argv:
        raise SystemExit("usage: wide_chord_independent.py --run")
    main_wc_cert()


if __name__ == "__main__":
    main()
