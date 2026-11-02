#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
"""Compute the illustration-only values lambda_1(p): Figure 1 (p = 1.1) and the lower curve of Figure 2.

Version 1.00 — release maintainer — 20261031 13:32 ET.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.
Requires mpmath (1.4.1 was used). Floating point at 20 digits: a picture, not a certificate. The proofs do not use it.

For 1 < p < 2 and 0 < lambda < 1, with C = GK_p(lambda), q = p/2, s0 = sin(pi/p), c0 = -cos(pi/p):
  h(lambda, p) = inf_{x>0} (C^p (1+x)^p - (1+lambda x)^p) / x^q  -  K,
  K = 2 (1-lambda) C s0^(p-2) c0^(1-q) (C^2 + lambda)^(q-1),
  lambda_loc(p) = (1 - sqrt T)/(1 + sqrt T) if T = s0^2 (p p'/4 - 1 - c0^2)/c0^4 > 0, else 1.
lambda_1(p) is the first sign change of h(., p) on a scan of lambda in (0, 1), refined by 36 bisection steps.
The infimum over x is taken on a grid of u = log x in [-14, 14] (281 points), refined by ternary search.

Usage:  lambda_one.py --run    (prints lambda_1(1.1), lambda_loc(1.1) and the Figure 2 curve, one JSON line each)
        lambda_one.py --test   (spot values)
"""
import argparse
import json

import mpmath as mp

mp.mp.dps = 20
U_GRID = [mp.mpf(-14) + kk * mp.mpf(28) / 280 for kk in range(281)]
LAM_SCAN = [mp.mpf(kk) / 100 for kk in range(1, 100)] + [mp.mpf(v) for v in
            ("0.995", "0.998", "0.999", "0.9995", "0.9998", "0.9999")]


def angles(p):
    theta = mp.pi / p
    return mp.sin(theta), -mp.cos(theta)


def gk_bound(lam, p):
    """GK_p(lambda): the largest singular value of [[1, (lambda-1) cot(pi/p)], [0, lambda]]."""
    mat = mp.matrix([[1, (lam - 1) * mp.cot(mp.pi / p)], [0, lam]])
    return max(mp.svd_r(mat, compute_uv=False))


def k_const(lam, p, cc):
    s0, c0 = angles(p)
    q = p / 2
    return 2 * (1 - lam) * cc * s0**(p - 2) * c0**(1 - q) * (cc**2 + lam)**(q - 1)


def axis_quotient(lam, p, cc, uu):
    xx = mp.e**uu
    return (cc**p * (1 + xx)**p - (1 + lam * xx)**p) / xx**(p / 2)


def axis_min(lam, p, cc):
    vals = [axis_quotient(lam, p, cc, uu) for uu in U_GRID]
    kbest = min(range(len(vals)), key=lambda kk: vals[kk])
    if kbest in (0, len(vals) - 1):
        raise RuntimeError(f"axis minimum at grid edge: p={p}, lambda={lam}")
    lo, hi = U_GRID[kbest - 1], U_GRID[kbest + 1]
    for _ in range(70):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if axis_quotient(lam, p, cc, m1) < axis_quotient(lam, p, cc, m2):
            hi = m2
        else:
            lo = m1
    return axis_quotient(lam, p, cc, (lo + hi) / 2)


def h_test(lam, p):
    cc = gk_bound(lam, p)
    return axis_min(lam, p, cc) - k_const(lam, p, cc)


def lam_loc(p):
    s0, c0 = angles(p)
    pp = p / (p - 1)
    tt = s0**2 * (p * pp / 4 - 1 - c0**2) / c0**4
    return (1 - mp.sqrt(tt)) / (1 + mp.sqrt(tt)) if tt > 0 else mp.mpf(1)


def lam_one(p):
    """First sign change of h(., p) on the scan, refined by bisection."""
    prev = None
    for lam in LAM_SCAN:
        if h_test(lam, p) < 0:
            if prev is None:
                raise RuntimeError(f"h < 0 already at the first scan point, p={p}")
            return bisect_zero(prev, lam, p)
        prev = lam
    raise RuntimeError(f"no sign change of h below lambda=0.9999 at p={p}")


def bisect_zero(lo, hi, p):
    for _ in range(36):
        mid = (lo + hi) / 2
        if h_test(mid, p) >= 0:
            lo = mid
        else:
            hi = mid
    return lo


def figure2_p_grid():
    """The exponents at which the lower curve of Figure 2 is drawn."""
    near_one = [mp.mpf(v) for v in ("1.0002", "1.0005", "1.001", "1.002", "1.003", "1.004")]
    coarse = near_one + [mp.mpf("1.005") + kk * mp.mpf("0.005") for kk in range(45)]
    fine = [mp.mpf(v) for v in ("1.227", "1.229", "1.231", "1.232", "1.233", "1.2335")]
    return coarse + fine


def run_all():
    p11 = mp.mpf("1.1")
    print(json.dumps({"p": "1.1", "lambda_1": mp.nstr(lam_one(p11), 12), "lambda_loc": mp.nstr(lam_loc(p11), 12)}), flush=True)
    curve = [[mp.nstr(p, 6), mp.nstr(lam_one(p), 8)] for p in figure2_p_grid()]
    print(json.dumps({"figure_2_lower_curve_p_lambda_1": curve}), flush=True)


def run_tests():
    got = lam_one(mp.mpf("1.1"))
    assert abs(got - mp.mpf("0.388773778451")) < mp.mpf("1e-9"), got
    assert h_test(got - mp.mpf("1e-4"), mp.mpf("1.1")) > 0 > h_test(got + mp.mpf("1e-4"), mp.mpf("1.1"))
    assert abs(lam_loc(mp.mpf("1.1")) - mp.mpf("0.513321146673")) < mp.mpf("1e-11")
    assert got < lam_loc(mp.mpf("1.1"))
    print("tests passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--test", action="store_true")
    arguments = parser.parse_args()
    run_tests() if arguments.test else run_all()


if __name__ == "__main__":
    main()
