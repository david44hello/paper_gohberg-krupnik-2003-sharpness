#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# omega_positive.py - Gohberg–Krupnik: second code for route A's 1-D facts: Omega' > 0 on [1.2336025, 1.2336027], Omega > 0 on [1.2336027, 1.268] [-route C]
## version 0.10 - route C 20261028_0136 ET - reuses gamma_series of omega_negative.py v0.10 (my Prop. F second code; Gamma = Omega);
##   derivative claim = enclosure of Omega' on each cell; positivity = centred form Omega(c) - |Omega'(cell)| h; adaptive bisection; 2 controls
import hashlib
import sys
from flint import arb, ctx, fmpq
from omega_negative import gamma_series

PREC_BITS = 120
P_A, P_B, P_HI = fmpq(12336025, 10 ** 7), fmpq(12336027, 10 ** 7), fmpq(317, 250)


def derivative_lower(lo, hi):
    """Rigorous lower bound of Omega' on [lo, hi] (enclosure from an arb_series over the cell ball); -inf if not computable."""
    try:
        return gamma_series(arb((lo + hi) / 2, arb((hi - lo) / 2).upper()), 2).coeffs()[1].lower()
    except ValueError:
        return arb("-inf")


def value_lower(lo, hi):
    """Rigorous lower bound of Omega on [lo, hi]: Omega(c) - |Omega'(cell)| (hi - lo)/2."""
    c, h = (lo + hi) / 2, (hi - lo) / 2
    try:
        der = gamma_series(arb(c, arb(h).upper()), 2).coeffs()[1]
    except ValueError:
        return arb("-inf")
    return (gamma_series(arb(c), 1).coeffs()[0] - abs(der) * arb(h)).lower()


def certify(lo, hi, lower_fn, max_cells):
    """Adaptive bisection: lower_fn(cell) > 0 on every piece of [lo, hi]."""
    stack, used = [(lo, hi)], 0
    while stack:
        a, b = stack.pop()
        used += 1
        if used > max_cells:
            return False, used
        if lower_fn(a, b) > 0:
            continue
        m = (a + b) / 2
        stack += [(m, b), (a, m)]
    return True, used


def neg_derivative_lower(lo, hi):
    """Lower bound of -Omega' (for the control 'Omega' < 0')."""
    try:
        return (-gamma_series(arb((lo + hi) / 2, arb((hi - lo) / 2).upper()), 2).coeffs()[1]).lower()
    except ValueError:
        return arb("-inf")


def md5_self():
    return hashlib.md5(open(__file__, "rb").read()).hexdigest()


def main():
    ctx.prec = PREC_BITS
    import omega_negative as gsc
    gmd5 = hashlib.md5(open(gsc.__file__, "rb").read()).hexdigest()
    print(f"# omega_positive.py md5 {md5_self()}; imports omega_negative.py md5 {gmd5}; prec {PREC_BITS}")
    ok1, n1 = certify(P_A, P_B, derivative_lower, 2000)
    print(f"CLAIM Omega' > 0 on [1.2336025, 1.2336027]: {'PROVED' if ok1 else 'NOT proved'} ({n1} cells)")
    ok2, n2 = certify(P_B, P_HI, value_lower, 200000)
    print(f"CLAIM Omega > 0 on [1.2336027, 1.268]: {'PROVED' if ok2 else 'NOT proved'} ({n2} cells)")
    c1, m1 = certify(P_A, P_B, value_lower, 3000)
    print(f"CONTROL 1  Omega > 0 on [1.2336025, 1.2336027] (contains p_0; must FAIL): {'PROVED (BAD)' if c1 else 'refused (good)'} ({m1} cells)")
    c2, m2 = certify(P_A, P_B, neg_derivative_lower, 3000)
    print(f"CONTROL 2  Omega' < 0 on [1.2336025, 1.2336027] (must FAIL): {'PROVED (BAD)' if c2 else 'refused (good)'} ({m2} cells)")
    va, vb = gamma_series(arb(P_A), 1).coeffs()[0], gamma_series(arb(P_B), 1).coeffs()[0]
    print(f"Omega(1.2336025) = {va.str(10)}, Omega(1.2336027) = {vb.str(10)}, Omega(5/4) = {gamma_series(arb(fmpq(5, 4)), 1).coeffs()[0].str(13)}")
    print(f"# md5 at end {md5_self()}")
    good = ok1 and ok2 and not c1 and not c2
    print(f"RESULT: {'both claims PROVED, controls refused' if good else 'NOT proved'}")
    return 0 if good else 1


if __name__ == "__main__":
    sys.exit(main())
