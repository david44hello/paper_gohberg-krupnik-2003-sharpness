#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# omega_positive_independent.py - Gohberg–Krupnik strip (S-a): rigorous 1-D facts on Omega(p) near and above p_0 (Arb, centred forms) 
## version 0.10 - route A 20261027_2125 ET - Omega' > 0 on [P_A, P_B]; Omega > 0 on [P_B, P_END]; Omega(P_A) < 0; two controls that must fail
#
# Omega(p) = p (A + s*)/(s*(1-s*))^q - 2^q s0^{p-2} c0^{1-q}, q = p/2, s0 = sin(pi/p), c0 = -cos(pi/p), A = (1-s0)/(2 s0),
# s* = 2qA/(b + sqrt(b^2 + 4(2q-1)qA)), b = 1 - q + 2qA (cancellation-free root of (2q-1)s^2 + b s - qA = 0).
# With route B/route C (Omega < 0 on (1, 1.2336025]) these give: Omega has exactly one zero p_0 in (1, P_END], p_0 in (P_A, P_B),
# and Omega > 0 on (p_0, P_END] (P_END > 3 - sqrt 3).
# Centred form on a cell [a, b]: Omega(cell) in Omega(m) + Omega'(cell) [-h, h]; Omega'(cell) from arb_series (degree 1) at the cell ball.

import sys
import hashlib
import flint
from flint import arb, arb_series, fmpq

PREC_BITS = 160
P_A = fmpq(12336025, 10000000)
P_B = fmpq(12336027, 10000000)
P_END = fmpq(1268, 1000)
MAX_CELLS = 200000


def omega_series(p):
    q = p / 2
    th = arb.pi() / p
    s0, c0 = th.sin(), -th.cos()
    big_a = (1 - s0) / (2 * s0)
    bb = 1 - q + 2 * q * big_a
    s_star = 2 * q * big_a / (bb + (bb * bb + 4 * (2 * q - 1) * q * big_a).sqrt())
    lhs = p * (big_a + s_star) * (-q * (s_star * (1 - s_star)).log()).exp()
    rhs = (q * arb(2).log() + (p - 2) * s0.log() + (1 - q) * c0.log()).exp()
    return lhs - rhs


def ball(lo, hi):
    return arb((arb(lo) + arb(hi)) / 2, (arb(hi) - arb(lo)) / 2)


def omega_and_slope(lo, hi):
    """(Omega at the midpoint, Omega' enclosure over the cell) as arb balls."""
    mid = (lo + hi) / 2
    om_mid = omega_series(arb_series([arb(mid), 1], prec=2)).coeffs()[0]
    slope = omega_series(arb_series([ball(lo, hi), 1], prec=2)).coeffs()[1]
    return om_mid, slope


def certify_positive(lo, hi, max_cells):
    stack, used = [(lo, hi)], 0
    while stack:
        a, b = stack.pop()
        used += 1
        if used > max_cells:
            return False, used
        om_mid, slope = omega_and_slope(a, b)
        if om_mid + slope * arb(0, arb((b - a) / 2)) > 0:
            continue
        m = (a + b) / 2
        stack += [(a, m), (m, b)]
    return True, used


def slope_positive(lo, hi, cells):
    h = (hi - lo) / cells
    return all(omega_and_slope(lo + k * h, lo + (k + 1) * h)[1] > 0 for k in range(cells))


def main_omega_arb():
    flint.ctx.prec = PREC_BITS
    md5 = hashlib.md5(open(__file__, "rb").read()).hexdigest()
    print(f"# omega_positive_independent.py md5 {md5}, prec {PREC_BITS}")
    om_a = omega_series(arb_series([arb(P_A), 1], prec=1)).coeffs()[0]
    print(f"Omega({P_A}) = {om_a.str(12)}  (< 0: {om_a < 0})")
    ok_slope = slope_positive(P_A, P_B, 4)
    print(f"CLAIM Omega' > 0 on [{P_A}, {P_B}] (4 cells): {'PROVED' if ok_slope else 'NOT proved'}")
    ok_pos, n_pos = certify_positive(P_B, P_END, MAX_CELLS)
    print(f"CLAIM Omega > 0 on [{P_B}, {P_END}]: {'PROVED' if ok_pos else 'NOT proved'} ({n_pos} cells)")
    c1, n1 = certify_positive(P_A, P_B, 3000)
    print(f"CONTROL Omega > 0 on [{P_A}, {P_B}] (contains p_0) must FAIL: {'PROVED (BAD)' if c1 else 'refused (good)'} ({n1} cells)")
    c2, n2 = certify_positive(fmpq(12, 10), P_END, 3000)
    print(f"CONTROL Omega > 0 on [6/5, {P_END}] must FAIL: {'PROVED (BAD)' if c2 else 'refused (good)'} ({n2} cells)")
    print(f"# md5 at end {hashlib.md5(open(__file__, 'rb').read()).hexdigest()}")
    return om_a < 0 and ok_slope and ok_pos and not c1 and not c2


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--test":
        flint.ctx.prec = PREC_BITS
        print(omega_and_slope(fmpq(5, 4), fmpq(5, 4)))
        return
    sys.exit(0 if main_omega_arb() else 1)


if __name__ == "__main__":
    main()
