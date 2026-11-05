#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
# local_threshold.py - Gohberg–Krupnik Lemma P_c: F(p) = p p' - 4(1 + cos^2(pi/p)) is > 0 on (1, p_c) and < 0 on (p_c, 2), one simple root p_c [-route C]
## version 0.10 - route C 20261027_1606 ET - Arb cells on [1 + 1e-6, 3/2] + derivative sign near p_c; ends by hand (see note)
# Hand ends: (1, 1 + 1e-6]: p p' >= 1/(p - 1) >= 1e6 > 8 >= 4(1 + cos^2).  [3/2, 2): with eta = 2 - p, F = eta^2/(p-1) - 4 sin^2(pi eta/(2p))
#   and sin x >= x - x^3/6 (x = pi eta/(2p) <= pi/6): F/eta^2 <= 1/(p-1) - (pi/p)^2 (1 - x^2/6)^2 <= 2 - (pi^2/4)(1 - (pi/6)^2/6)^2 < 0.
# Stable form used in cells: F = (p - 2)^2/(p - 1) - 4 sin^2(pi (p - 2)/(2p))   (exact: p^2/(p-1) - 4 = (p-2)^2/(p-1), cos(pi/p) = sin(pi/2 - pi/p)).
import sys
from fractions import Fraction
from flint import arb, ctx


def arb_of(fr):
    fr = Fraction(fr)
    return arb(fr.numerator) / arb(fr.denominator)


def F(p):
    return (p - 2) ** 2 / (p - 1) - 4 * (arb.pi() * (p - 2) / (2 * p)).sin() ** 2


def dF(p):
    # d/dp [(p-2)^2/(p-1)] = (p-2)(p)/(p-1)^2 ;  d/dp [4 sin^2(u)] = 8 sin u cos u u', u = pi (p-2)/(2p), u' = pi/p^2
    u = arb.pi() * (p - 2) / (2 * p)
    return (p - 2) * p / (p - 1) ** 2 - 8 * u.sin() * u.cos() * arb.pi() / p ** 2


def sign_on(pa, pb, want, depth=0):
    p = arb_of(pa).union(arb_of(pb))
    val = F(p)
    if (want > 0 and val > 0) or (want < 0 and val < 0):
        return 1
    if depth > 40:
        raise SystemExit(f"cannot certify sign {want} on [{float(pa)}, {float(pb)}]: {val}")
    mid = (pa + pb) / 2
    return sign_on(pa, mid, want, depth + 1) + sign_on(mid, pb, want, depth + 1)


def main_pc():
    ctx.prec = 192
    lo, hi = Fraction(1213490304, 10 ** 9), Fraction(1213490305, 10 ** 9)   # bracket of p_c = 1.2134903043...
    print(f"F(lo) = {F(arb_of(lo))}  F(hi) = {F(arb_of(hi))}")
    assert F(arb_of(lo)) > 0 and F(arb_of(hi)) < 0
    win_lo, win_hi = Fraction(12134, 10 ** 4), Fraction(12136, 10 ** 4)
    d = dF(arb_of(win_lo).union(arb_of(win_hi)))
    print(f"F' on [{float(win_lo)}, {float(win_hi)}] = {d}  (< 0 => at most one root there)")
    assert d < 0
    n1 = sign_on(Fraction(1000001, 10 ** 6), win_lo, +1)
    n2 = sign_on(win_hi, Fraction(3, 2), -1)
    w = arb_of(win_lo).union(arb_of(win_hi))
    print(f"F > 0 on [1.000001, {float(win_lo)}]: {n1} cells;  F < 0 on [{float(win_hi)}, 1.5]: {n2} cells")
    print(f"F(win_lo) = {F(arb_of(win_lo))} > 0, F(win_hi) = {F(arb_of(win_hi))} < 0, F' < 0 in between => unique simple root p_c in "
          f"[{lo}, {hi}] (bracket certified above)")
    # hand end [3/2, 2): the numeric constant
    const = 2 - (arb.pi() ** 2 / 4) * (1 - (arb.pi() / 6) ** 2 / 6) ** 2
    print(f"hand-end constant 2 - (pi^2/4)(1 - (pi/6)^2/6)^2 = {const} (must be < 0)")
    assert const < 0
    print("LEMMA P_c: PROVED")
    return 0


if __name__ == "__main__":
    sys.exit(main_pc())
