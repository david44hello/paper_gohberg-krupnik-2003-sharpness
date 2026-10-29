#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# omega_positive_alternate.py - Gohberg–Krupnik: independent 2nd code for the sign of Omega just above p_0 (Arb; centred form) 
# version 0.10 - route B 20261028 (after 01:34 ET) - first version (route A's B2: Omega near p_0 had one code only)
"""
Omega(p) = p (A + s*)/(s*(1-s*))^q - 2^q s0^{p-2} c0^{1-q},  q = p/2, s0 = sin(pi/p), c0 = -cos(pi/p), A = (1 - s0)/(2 s0),
s* = the root in (0, 1) of (2q-1) s^2 + (1 - q + 2qA) s - qA = 0, computed as s* = 2qA/(b + sqrt(b^2 + 4(2q-1)qA)), b = 1 - q + 2qA.
CLAIMS:  (i) Omega' > 0 on [P1, P2] = [1.2336025, 1.2336027];  (ii) Omega > 0 on [P2, P3] = [1.2336027, 1.2337027].
With Omega < 0 on (1, 1.2336025] (Prop. F) this gives exactly one zero p_0 in (1, P3], and Omega > 0 on (p_0, P3].
Method: Omega as an arb_series in p (length 2) over each cell: Omega' encloses the derivative on the cell; centred form
Omega(cell) in Omega(mid) + Omega'(cell) [-h, h]. Adaptive bisection. 128 bits.
CONTROLS (must FAIL): (c1) "Omega > 0 on [P1, P2]" (contains p_0); (c2) "Omega' < 0 on [P1, P2]".
"""
import argparse
import sys

import flint
from flint import arb, arb_series

flint.ctx.prec = 128
P1, P2, P3 = arb("1.2336025"), arb("1.2336027"), arb("1.2337027")


def omega_series(p_ball):
    pp = arb_series([p_ball, arb(1)], prec=2)
    q = pp / 2
    th = arb.pi() / pp
    s0, c0 = th.sin(), -th.cos()
    big_a = (1 - s0) / (2 * s0)
    bb = 1 - q + 2 * q * big_a
    s_star = 2 * q * big_a / (bb + (bb * bb + 4 * (2 * q - 1) * q * big_a).sqrt())
    first = pp * (big_a + s_star) * ((s_star * (1 - s_star)).log() * (-q)).exp()
    second = ((q * arb(2).log()) + (pp - 2) * s0.log() + (1 - q) * c0.log()).exp()
    return (first - second).coeffs()


def cell_ok(lo, hi, claim):
    mid, half = (lo + hi) / 2, (hi - lo) / 2
    cell = mid + arb(0, half)
    value_mid, deriv = omega_series(mid)[0], omega_series(cell)[1]
    if claim == "deriv_pos":
        return deriv > 0
    if claim == "deriv_neg":
        return deriv < 0
    return (value_mid - abs(deriv).upper() * half) > 0


def certify(lo, hi, claim, max_depth):
    stack, cells, refused = [(lo, hi, 0)], 0, 0
    while stack:
        c_lo, c_hi, depth = stack.pop()
        cells += 1
        if cell_ok(c_lo, c_hi, claim):
            continue
        if depth >= max_depth:
            refused += 1
            continue
        c_mid = (c_lo + c_hi) / 2
        stack += [(c_lo, c_mid, depth + 1), (c_mid, c_hi, depth + 1)]
    return cells, refused


def main_certify():
    results = {
        "(i) Omega' > 0 on [P1, P2]": certify(P1, P2, "deriv_pos", 20),
        "(ii) Omega > 0 on [P2, P3]": certify(P2, P3, "value_pos", 24),
        "control c1: Omega > 0 on [P1, P2]": certify(P1, P2, "value_pos", 16),
        "control c2: Omega' < 0 on [P1, P2]": certify(P1, P2, "deriv_neg", 12),
    }
    for name, (cells, refused) in results.items():
        print(f"{name}: cells {cells}, refused {refused}")
    claims_ok = all(results[k][1] == 0 for k in list(results)[:2])
    controls_ok = all(results[k][1] > 0 for k in list(results)[2:])
    print(f"CLAIMS {'PROVED' if claims_ok else 'NOT PROVED'}; CONTROLS {'REFUSED (good)' if controls_ok else 'ACCEPTED (BAD)'}")
    return claims_ok and controls_ok


def run_tests():
    vals = omega_series(arb("1.25"))
    ok_value = abs(vals[0] - arb("0.01565442189276")) < arb("1e-13")
    ok_deriv = abs(vals[1] - arb("0.857789439818")) < arb("1e-10")
    print(f"TEST Omega(5/4) = {vals[0].str(14)} (route A 0.01565442189276): {ok_value}; "
          f"Omega'(5/4) = {vals[1].str(12)} (route A 0.857789439818): {ok_deriv}")
    return ok_value and ok_deriv


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--mode", choices=["certify", "test"], required=True)
    args = parser.parse_args()
    if args.mode == "test":
        sys.exit(0 if run_tests() else 1)
    sys.exit(0 if main_certify() else 1)


if __name__ == "__main__":
    main()
