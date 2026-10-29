#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# omega_negative.py - Gohberg–Krupnik: independent Arb second code of route B's "Gamma(p) < 0 on [1.001, 1.2336025]" (Prop. F, p_0 edge) [-route C]
## version 0.10 - route C 20261027_1702 ET - centered form Gamma(c) + |Gamma'(cell)| h via arb_series; stable s*; adaptive bisection; control
# Gamma(p) = p (A + s*)/(s*(1-s*))^q - 2^q s0^{p-2} c0^{1-q},  s0 = sin(pi(p-1)/p), c0 = cos(pi(p-1)/p), A = (1-s0)/(2 s0), q = p/2,
# s* = root in (0,1) of (2q-1)s^2 + (1-q+2qA)s - qA = 0, computed as 2qA/(b + sqrt(b^2 + 4(2q-1)qA)), b = 1-q+2qA (no cancellation).
import argparse
import hashlib
import sys
from flint import arb, arb_series, ctx, fmpq

PREC_BITS = 120


def gamma_series(p_ball, order):
    """Taylor series of Gamma at p_ball (arb_series in the variable p - p_ball)."""
    pp = arb_series([p_ball, 1], prec=order)
    one, two = arb(1), arb(2)
    q = pp / two
    ang = arb.pi() * (pp - one) / pp
    s0, c0 = ang.sin(), ang.cos()
    A = (one - s0) / (two * s0)
    b = one - q + two * q * A
    s = two * q * A / (b + (b * b + 4 * (two * q - one) * q * A).sqrt())
    first = pp * (A + s) * ((s * (one - s)).log() * (-q)).exp()
    second = (q * arb(2).log()).exp() * ((pp - two) * s0.log()).exp() * ((one - q) * c0.log()).exp()
    return first - second


def cell_upper(lo, hi):
    """Rigorous upper bound of Gamma on [lo, hi] (fmpq endpoints): Gamma(c) + |Gamma'([lo,hi])| (hi-lo)/2."""
    c, h = (lo + hi) / 2, (hi - lo) / 2
    val = gamma_series(arb(c), 1).coeffs()[0]
    cell = arb(c, arb(h).upper())
    try:
        der = gamma_series(cell, 2).coeffs()[1]
    except ValueError:            # ball too wide for a series division (denominator ball meets 0): NOT certified, so split the cell
        return arb("inf")
    return (val + abs(der) * arb(h)).upper()


def certify(lo, hi, max_cells):
    """Adaptive bisection; returns (ok, cells_used)."""
    stack, used = [(lo, hi)], 0
    while stack:
        a, b = stack.pop()
        used += 1
        if used > max_cells:
            return False, used
        if cell_upper(a, b) < 0:
            continue
        m = (a + b) / 2
        stack += [(m, b), (a, m)]
    return True, used


def main_certify():
    ctx.prec = PREC_BITS
    md5 = hashlib.md5(open(__file__, "rb").read()).hexdigest()
    print(f"# omega_negative.py md5 {md5}, prec {PREC_BITS} bits")
    ok, n = certify(fmpq(1001, 1000), fmpq(12336025, 10000000), 200000)
    print(f"CLAIM Gamma < 0 on [1.001, 1.2336025]: {'PROVED' if ok else 'NOT proved'} ({n} cells)")
    hi = fmpq(12336027, 10000000)
    ok2, n2 = certify(hi - fmpq(1, 10 ** 9), hi, 2000)
    print(f"CONTROL Gamma < 0 on [1.2336027 - 1e-9, 1.2336027] (must FAIL): {'PROVED (BAD)' if ok2 else 'refused (good)'} ({n2} cells)")
    v = gamma_series(arb(hi), 1).coeffs()[0]
    print(f"Gamma(1.2336027) = {v.str(10)}")
    print(f"# md5 at end {hashlib.md5(open(__file__, 'rb').read()).hexdigest()}")
    return ok and not ok2


def main_test():
    ctx.prec = PREC_BITS
    v = gamma_series(arb(fmpq(3, 2)), 1).coeffs()[0]
    assert abs(float(v.mid()) - 0.074838) < 1e-5, v       # float value from my scipy check
    assert cell_upper(fmpq(105, 100), fmpq(1051, 1000)) < 0      # a 0.01 cell is too wide here (|Gamma'| enclosure 575)
    print("tests passed")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--test", action="store_true")
    args = ap.parse_args()
    if args.test:
        main_test()
        return
    sys.exit(0 if main_certify() else 1)


if __name__ == "__main__":
    main()
