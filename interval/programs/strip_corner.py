#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
# strip_corner.py - Gohberg–Krupnik strip (S-c): rigorous corner lemma g > 0 near (delta, p) = (0, p_0) (Arb; even form + Taylor remainder)
# version 0.30 - route B 20261027 (after 21:47 ET) - prints certified LOWER ends of the edge bounds (v0.20 printed "[+/- 1.49]": no digit, not a sign)
# version 0.20 - route B 20261027 (after 21:30 ET) - Lagrange remainder from a REAL ball series (Cauchy circle was 7x too lossy; v0.10 refused)
# version 0.10 - route B 20261027 (after 21:25 ET) - first version (Cauchy bound on |eps| = 0.5: complex-ball overestimation, NOT PROVED)
"""
CLAIM (corner). For p in [P_A, P_B] with Omega(p) >= 0, delta in (0, DELTA1] and s in (0, 1): g(delta, p, s) > 0.
  (P_A = 1.2336025 < p_0, P_B = 1.2341027, DELTA1 = 0.05; g as in lampos note Sec. 8; h = delta min_s g.)
Coordinates (route A 21:20): lam = e^{-eps}, rho = 1 - s delta = e^{-sigma eps}; Et := g / V, V = e^{(1-q) eps/2} C^{p/2} > 0.
Et is EVEN in eps at fixed sigma (route A's identity, read by route B 21:22), so Et'(0) = Et'''(0) = 0 and, for 0 < eps <= EPS1,
  Et(eps) = Et0 + e2 eps^2 + c4(xi) eps^4  (Lagrange; xi in (0, eps); c4 = Et''''/24),
with Et0 = Et(0), e2 = Et''(0)/2 from an arb_series at eps = 0, and |c4| bounded over xi in [0, EPS1] by arb_series centred on
N_SUB = 64 real sub-balls covering [0, EPS1] (computed once per sigma-cell of width <= TAU_WIDTH, inherited by sub-cells).
No removable 0/0 anywhere: with the entire function E(z) = (1 - e^{-z})/z,
  delta = eps E(eps),  s = sigma E(sigma eps)/E(eps),  1 - s = e^{-sigma eps}(1-sigma) E((1-sigma) eps)/E(eps),
  T1 = p E(-pL)/E(-L) (C - s0)/(s0 (C+1)) with L = log C,  s phi(s delta) = p sigma E(p sigma eps)/E(eps).
MIDDLE (s in [0.05, 0.95], covered by sigma in [SIG_LO, SIG_HI] since s E(eps) <= sigma <= s), per (sigma, p) cell, tau := |c4| EPS1^2:
  PASS (I): e2 > tau  =>  Et > Et0 >= Omega(p) >= 0.      PASS (II): Et0 > EPS1^2 (max(0, -e2) + tau)  =>  Et > 0.
EDGES: s <= 0.05: g >= T1/0.05^q - kappa; s >= 0.95: g >= (T1 + 0.95)/0.05^q - kappa (phi >= 1), over delta in [0, DELTA1].
CONTROLS (must FAIL): (c1) PASS (II) alone on sigma in [0.25, 0.27] (Et0 ~ Omega ~ 0 near sigma* = 0.2607 at p_0);
  (c2) the false claim e2 > tau + 0.2 on sigma in [0.25, 0.35] (e2 ~ 0.11).
"""
import argparse
import math
import sys

import flint
from flint import arb, arb_series

flint.ctx.prec = 128
P_A, P_B = arb("1.2336025"), arb("1.2341027")
DELTA1 = arb("0.05")
EPS1 = -(1 - DELTA1).log()
SIG_LO, SIG_HI = arb("0.045"), arb("0.95")
S_EDGE = arb("0.05")
N_TERMS = 40
N_SUB = 64
TAU_WIDTH = arb("0.01")


def ball(lo, hi):
    return (lo + hi) / 2 + arb(0, (hi - lo) / 2)


def constants(p):
    q = p / 2
    th = arb.pi() / p
    s0, c0 = th.sin(), -th.cos()
    k0 = (s0.log() * (p - 2) + c0.log() * (1 - q)).exp()
    return q, s0, k0


def cpow(x, y):
    return (x.log() * y).exp()


def exprel_tail(radius):
    """Bound for |sum_{n >= N} (-z)^n/(n+1)!| on |z| <= radius."""
    return radius ** N_TERMS / arb(math.factorial(N_TERMS + 1)) / (1 - radius / (N_TERMS + 2))


def exprel(z):
    """E(z) = (1 - e^{-z})/z = sum_n (-z)^n/(n+1)!, N terms + rigorous tail (for a series: Cauchy on |x| = 1)."""
    total, term = 0 * z + 1, 0 * z + 1
    for kk in range(1, N_TERMS):
        term = term * (-z) / (kk + 1)
        total = total + term
    if isinstance(z, arb_series):
        radius = sum((abs(cc).upper() for cc in z.coeffs()), arb(0))
        tail = exprel_tail(radius)
        coeffs = total.coeffs() + [arb(0)] * (z.prec - len(total.coeffs()))
        return arb_series([cc + arb(0, tail) for cc in coeffs], prec=z.prec)
    return total + arb(0, exprel_tail(abs(z).upper()))


def etilde(eps, sigma, p):
    q, s0, k0 = constants(p)
    e_eps = exprel(eps)
    delta = eps * e_eps
    cc = delta / (2 * s0) + (delta * delta / (4 * s0 * s0) + 1 - delta).sqrt()
    big_l = cc.log()
    t1 = p * exprel(-p * big_l) / exprel(-big_l) * (cc - s0) / (s0 * (cc + 1))
    s_val = sigma * exprel(sigma * eps) / e_eps
    one_minus_s = (-sigma * eps).exp() * (1 - sigma) * exprel((1 - sigma) * eps) / e_eps
    numer = t1 + p * sigma * exprel(p * sigma * eps) / e_eps
    big_f = numer * ((s_val * one_minus_s).log() * (-q)).exp()
    kappa = 2 * cc * k0 * cpow(cc * cc + (-eps).exp(), q - 1)
    big_v = (eps * (1 - q) / 2).exp() * cpow(cc, p / 2)
    return (big_f - kappa) / big_v


def coeffs_at(eps_centre, sigma, p, length):
    eps = arb_series([eps_centre, arb(1)], prec=length)
    return etilde(eps, sigma, p).coeffs()


def tau_bound(sigma, p):
    """tau = EPS1^2 * sup |c4(xi)| over xi in [0, EPS1]: max over N_SUB sub-balls (small radii -> little overestimation)."""
    worst = 0.0
    for jj in range(N_SUB):
        centre = ball(EPS1 * jj / N_SUB, EPS1 * (jj + 1) / N_SUB)
        c4 = coeffs_at(centre, sigma, p, 5)[4]
        if not c4.is_finite():
            return arb("inf")
        bound = abs(c4).upper()
        worst = max(worst, float(bound.mid()) + float(bound.rad()))
    return arb(worst) * (1 + arb("1e-10")) * EPS1 * EPS1


def cell_numbers(sigma, p, tau=None):
    at_zero = coeffs_at(arb(0), sigma, p, 3)
    if tau is None:
        tau = tau_bound(sigma, p)
    return at_zero[0], at_zero[2], tau


def cell_verdict(sig_lo, sig_hi, p_lo, p_hi, mode, tau):
    et0, e2, tau = cell_numbers(ball(sig_lo, sig_hi), ball(p_lo, p_hi), tau)
    shift = arb("0.2") if mode == "control_c2" else arb(0)
    pass_one = mode != "control_c1" and (e2 - tau - shift) > 0
    neg_e2 = arb(0) if e2 > 0 else (-e2).upper()
    pass_two = mode != "control_c2" and (et0 - EPS1 * EPS1 * (neg_e2 + tau)) > 0
    return pass_one, pass_two, (et0, e2, tau)


def split_cell(cell):
    a_lo, a_hi, b_lo, b_hi, depth, tau = cell
    if (a_hi - a_lo) > 400 * (b_hi - b_lo):
        a_mid = (a_lo + a_hi) / 2
        return [(a_lo, a_mid, b_lo, b_hi, depth + 1, tau), (a_mid, a_hi, b_lo, b_hi, depth + 1, tau)]
    b_mid = (b_lo + b_hi) / 2
    return [(a_lo, a_hi, b_lo, b_mid, depth + 1, tau), (a_lo, a_hi, b_mid, b_hi, depth + 1, tau)]


def with_tau(cell):
    """Cells inherit tau from the parent; tau is computed once, on the first cell of sigma-width <= TAU_WIDTH."""
    if cell[5] is not None:
        return cell, False
    if (cell[1] - cell[0]) > TAU_WIDTH:
        return cell, True
    return cell[:5] + (tau_bound(ball(cell[0], cell[1]), ball(cell[2], cell[3])),), False


def certify_middle(mode, sig_lo, sig_hi, max_depth):
    stack, counts = [(sig_lo, sig_hi, P_A, P_B, 0, None)], {"cells": 0, "pass_I": 0, "pass_II": 0, "refused": 0}
    worst_tau = 0.0
    while stack:
        cell, too_wide = with_tau(stack.pop())
        if too_wide:
            stack += split_cell(cell)
            continue
        pass_one, pass_two, info = cell_verdict(*cell[:4], mode, cell[5])
        counts["cells"] += 1
        if pass_one or pass_two:
            counts["pass_I" if pass_one else "pass_II"] += 1
            worst_tau = max(worst_tau, float(info[2].upper().mid()))
            continue
        if cell[4] >= max_depth:
            counts["refused"] += 1
            if counts["refused"] <= 3:
                print(f"  REFUSED sigma [{cell[0].mid().str(8)}, {cell[1].mid().str(8)}] p [{cell[2].mid().str(10)}, {cell[3].mid().str(10)}]: "
                      f"Et0 = {info[0].str(5)}, e2 = {info[1].str(5)}, tau = {info[2].str(4)}")
            continue
        stack += split_cell(cell)
    counts["max_tau"] = worst_tau
    return counts


def certify_edges():
    p = ball(P_A, P_B)
    q, s0, k0 = constants(p)
    eps = ball(arb(0), EPS1)
    delta = eps * exprel(eps)
    cc = delta / (2 * s0) + (delta * delta / (4 * s0 * s0) + 1 - delta).sqrt()
    big_l = cc.log()
    t1 = p * exprel(-p * big_l) / exprel(-big_l) * (cc - s0) / (s0 * (cc + 1))
    kappa = 2 * cc * k0 * cpow(cc * cc + (-eps).exp(), q - 1)
    edge_cap = cpow(S_EDGE, q)
    low_edge = t1 / edge_cap - kappa
    high_edge = (t1 + 1 - S_EDGE) / edge_cap - kappa
    print(f"EDGES (certified lower ends): s <= 0.05: g >= {low_edge.lower().str(6)};  s >= 0.95: g >= {high_edge.lower().str(6)}"
          f"  (balls {low_edge.str(6, radius=True)}, {high_edge.str(6, radius=True)})")
    return low_edge > 0 and high_edge > 0


def main_certify(mode, max_depth):
    print(f"corner box: p in [{P_A.str(10)}, {P_B.str(10)}], delta in [0, {DELTA1.str(4)}] (eps1 = {EPS1.str(8)}), mode = {mode}")
    if mode in ("control_c1", "control_c2"):
        lo, hi = (arb("0.25"), arb("0.27")) if mode == "control_c1" else (arb("0.25"), arb("0.35"))
        counts = certify_middle(mode, lo, hi, 8)
        good = counts["refused"] > 0
        print(f"CONTROL {mode}: {counts} -> {'REFUSED (good)' if good else 'ACCEPTED (BAD)'}")
        return good
    edges_ok = certify_edges()
    counts = certify_middle(mode, SIG_LO, SIG_HI, max_depth)
    print(f"MIDDLE: {counts}")
    verdict = edges_ok and counts["refused"] == 0
    print(f"CORNER CLAIM: {'PROVED' if verdict else 'NOT PROVED'}")
    return verdict


def run_tests():
    p, sigma = arb("1.2336026"), arb("0.3")
    at_zero = coeffs_at(arb(0), sigma, p, 4)
    q, s0, k0 = constants(p)
    big_a = (1 - s0) / (2 * s0)
    et0_closed = p * (big_a + sigma) / cpow(sigma * (1 - sigma), q) - 2 * k0 * cpow(arb(2), q - 1)
    ok0 = abs(at_zero[0] - et0_closed) < arb("1e-30")
    ok_odd = abs(at_zero[1]) < arb("1e-25") and abs(at_zero[3]) < arb("1e-20")
    et0, e2, tau = cell_numbers(sigma, p)
    ok_bound = True
    for eps_txt in ("0.01", "0.03", "0.05"):
        eps = arb(eps_txt)
        exact = etilde(eps, sigma, p)
        ok_bound = ok_bound and (exact - (et0 + eps * eps * (e2 - tau))) > 0 and ((et0 + eps * eps * (e2 + tau)) - exact) > 0
    print(f"TEST Et0 = closed form: {ok0}; odd coefficients at 0 vanish (c1 = {at_zero[1].str(3)}, c3 = {at_zero[3].str(3)}): {ok_odd}; "
          f"Et(eps) inside Et0 + eps^2 (e2 +- tau) at 3 points: {ok_bound} (e2 = {e2.str(8)}, tau = {tau.str(4)})")
    return ok0 and ok_odd and ok_bound


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--mode", choices=["certify", "control_c1", "control_c2", "test"], required=True)
    parser.add_argument("--max-depth", type=int, default=24)
    args = parser.parse_args()
    if args.mode == "test":
        sys.exit(0 if run_tests() else 1)
    sys.exit(0 if main_certify(args.mode, args.max_depth) else 1)


if __name__ == "__main__":
    main()
