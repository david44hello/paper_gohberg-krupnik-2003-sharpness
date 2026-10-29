#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# omega_negative_alternate.py - Gohberg–Krupnik Prop. F: rigorous sign of Gamma(p) on [P_LO, P_STOP] (Arb ball arithmetic) + enclosure of p_0
# version 0.10 - route B 20261027 (after 16:52 ET) - first version
"""
Gamma(p) = p (A + s)/(s(1-s))^q - 2^q s0^{p-2} c0^{1-q},   q = p/2, s0 = sin(pi/p), c0 = -cos(pi/p), A = (1 - s0)/(2 s0),
s = s*(p) = the positive root of (2q-1) s^2 + (1 - q + 2qA) s - qA = 0  (s* in (0,1)).
Claim: Gamma < 0 on [P_LO, P_STOP]; Gamma(P_HI) > 0. Then p_0 := inf{Gamma >= 0} lies in (P_STOP, P_HI).
Method: adaptive bisection; on each p-ball evaluate Gamma in ball arithmetic; accept when the upper bound is < 0.
Control that CAN fail: the same evaluator on [P_HI - 1e-9, P_HI] must NOT certify "Gamma < 0".
The end p -> 1 (p < P_LO) is a separate asymptotic lemma (Gamma -> -infinity like (1/sqrt2 - 1)/s0); not covered here.
"""
import argparse
import sys

import flint
from flint import arb


def gamma_ball(p):
    q = p / 2
    th = arb.pi() / p
    s0, c0 = th.sin(), -th.cos()
    big_a = (1 - s0) / (2 * s0)
    bb = 1 - q + 2 * q * big_a
    disc = bb * bb + 4 * (2 * q - 1) * q * big_a
    s_star = (-bb + disc.sqrt()) / (2 * (2 * q - 1))
    lhs = p * (big_a + s_star) / (s_star * (1 - s_star)) ** q
    rhs = arb(2) ** q * s0 ** (p - 2) * c0 ** (1 - q)
    return lhs - rhs


def ball_from(lo, hi):
    lo_a, hi_a = arb(lo), arb(hi)
    return (lo_a + hi_a) / 2 + arb(0, (hi_a - lo_a) / 2)


def certify_negative(lo, hi, depth_max):
    stack, cells = [(lo, hi, 0)], 0
    while stack:
        cl, ch, depth = stack.pop()
        val = gamma_ball(ball_from(cl, ch))
        if val < 0:
            cells += 1
            continue
        if depth >= depth_max:
            return False, cells, (cl, ch, val)
        mid = (cl + ch) / 2
        stack += [(cl, mid, depth + 1), (mid, ch, depth + 1)]
    return True, cells, None


def main_certify(p_lo, p_stop, p_hi, prec):
    flint.ctx.prec = prec
    ok, cells, fail = certify_negative(p_lo, p_stop, 60)
    print(f"Gamma < 0 on [{p_lo}, {p_stop}]: {ok} ({cells} cells){'' if ok else ' FAILED at ' + str(fail)}")
    at_hi = gamma_ball(arb(p_hi))
    print(f"Gamma({p_hi}) = {at_hi.str(10)}  (> 0: {at_hi > 0})")
    control_ok, _, _ = certify_negative(p_hi - 1e-9, p_hi, 8)
    print(f"CONTROL: certify Gamma < 0 on [{p_hi} - 1e-9, {p_hi}] -> {control_ok} (must be False)")
    return ok and at_hi > 0 and not control_ok


def main():
    parser = argparse.ArgumentParser(description="Gohberg–Krupnik: rigorous sign of Gamma(p) and enclosure of p_0")
    parser.add_argument("--p-lo", type=float, required=True)
    parser.add_argument("--p-stop", type=float, required=True)
    parser.add_argument("--p-hi", type=float, required=True)
    parser.add_argument("--prec", type=int, required=True)
    args = parser.parse_args()
    sys.exit(0 if main_certify(args.p_lo, args.p_stop, args.p_hi, args.prec) else 1)


if __name__ == "__main__":
    main()
