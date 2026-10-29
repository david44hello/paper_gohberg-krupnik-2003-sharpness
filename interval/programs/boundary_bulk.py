#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# boundary_bulk.py - Gohberg–Krupnik (ii): rigorous Arb check that h(lam_loc(p), p) = m_GK(0) - K < 0 on p-cells (so lam_0(p) < lam_loc(p)) [-route C]
## version 0.20 - route C 20261027_1602 ET - cancellation-free forms (delta, lam = (1-delta)/(1+delta), s = sqrt(disc), ...) for p -> 1
## version 0.10 - route C 20261027_1557 ET - upper bound m_GK(0) <= (C^p - w^p)/(theta(1-theta))^q, w = lam + theta(1 - lam); adaptive cells
# Facts used (all proved in the 019 notes): lam_loc(p) = (1 - sqrt(1 - Kl))^2/Kl, Kl = [1 - (p p'/4) sin^2(pi/p)]/cos^4(pi/p) (Theorem L);
#   C^2 = GK^2 = larger root of X^2 - (1 + lam^2 + (1-lam)^2 cot^2) X + lam^2; contact r + lam/r = (1+lam)/c, c = |cos(pi/p)|;
#   K = -m'(pi/p)/q = 2 r^{-q} |zeta* + lam|^p (1 - lam) / (sin(pi/p) (r - lam/r))  (Theorem L Steps 2, 5; = route A/independent review closed form).
#   m_GK(0) = (1-lam)^p min_{w in (lam,1)} (C^p - w^p)/[(w-lam)(1-w)]^q; with w = lam + theta (1-lam) this is (C^p - w^p)/(theta(1-theta))^q.
import argparse
import sys
from fractions import Fraction
import numpy as np
from flint import arb, ctx
from scipy.optimize import minimize_scalar

PREC = 192


def arb_of(fr):
    fr = Fraction(fr)
    return arb(fr.numerator) / arb(fr.denominator)


def cell_quantities(p):
    """All quantities as Arb balls for a p-ball (1 < p < p_c). Returns dict; raises on uncertified preconditions."""
    # cancellation-free forms (exact identities): with a = pi (p - 1)/p = pi/p', theta0 = pi - a:
    #   c = |cos theta0| = cos a, sn = sin a, 1 - c = 2 sin^2(a/2);  1 - Kl = delta^2 = sn^2 (p p'/4 - 1 - c^2)/c^4;
    #   lam = (1 - delta)/(1 + delta), eps = 2 delta/(1 + delta);  s = r - lam/r = sqrt(disc), disc = (eps^2 + 4 lam sn^2)/c^2;
    #   sqrt(S^2 - 4 lam^2) = eps csc(a) sqrt((1 + lam)^2 + eps^2 cot^2 a);  |zeta* + lam|^2 = (r - lam)^2 + 2 lam r (1 - c),
    #   r - lam = (eps + 2 lam (1 - c))/(2c) + s/2.
    q = p / 2
    a = arb.pi() * (p - 1) / p
    c, sn = a.cos(), a.sin()
    one_minus_c = 2 * (a / 2).sin() ** 2
    if not (c > 0 and sn > 0):
        raise ValueError("cos/sin sign not certified")
    d2 = sn ** 2 * (p * p / (p - 1) / 4 - 1 - c ** 2) / c ** 4
    if not (d2 > 0 and d2 < 1):
        raise ValueError(f"delta^2 not certified in (0,1): {d2}")
    delta = d2.sqrt()
    lam = (1 - delta) / (1 + delta)
    eps = 2 * delta / (1 + delta)
    cot2 = (c / sn) ** 2
    S = 1 + lam ** 2 + eps ** 2 * cot2
    X = (S + eps / sn * ((1 + lam) ** 2 + eps ** 2 * cot2).sqrt()) / 2
    s = ((eps ** 2 + 4 * lam * sn ** 2) / c ** 2).sqrt()
    sig = (1 + lam) / c
    r = (sig + s) / 2
    r_minus_lam = (eps + 2 * lam * one_minus_c) / (2 * c) + s / 2
    P = (r_minus_lam ** 2 + 2 * lam * r * one_minus_c) ** q
    K_mine = 2 * r ** (-q) * P * eps / (sn * s)
    K_n03 = 2 * eps ** p * X ** q * (X + lam) ** (q - 1) / (sn * c ** (q - 1) * (X - lam) ** (p - 1))
    return {"q": q, "lam": lam, "eps": eps, "X": X, "K": K_mine, "K_n03": K_n03}


def upper_h(p, theta):
    qq = cell_quantities(p)
    th = arb_of(theta)
    w = qq["lam"] + th * qq["eps"]
    m0_up = (qq["X"] ** qq["q"] - w ** p) / (th * (1 - th)) ** qq["q"]
    return m0_up - qq["K"], qq


def float_theta(pm):
    """Float: lam_loc, C, and the minimising theta of (C^p - w^p)/(theta(1-theta))^q at p = pm."""
    th0 = np.pi / pm
    c, sn = -np.cos(th0), np.sin(th0)
    kl = (1 - (pm * pm / (pm - 1) / 4) * sn ** 2) / c ** 4
    lam = (1 - np.sqrt(1 - kl)) ** 2 / kl
    eps = 1 - lam
    S = 1 + lam ** 2 + eps ** 2 * (c / sn) ** 2
    X = (S + np.sqrt(S ** 2 - 4 * lam ** 2)) / 2
    q = pm / 2
    f = lambda t: (X ** q - (lam + t * eps) ** pm) / (t * (1 - t)) ** q
    res = minimize_scalar(f, bounds=(1e-9, 1 - 1e-9), method="bounded", options={"xatol": 1e-13})
    return Fraction(res.x).limit_denominator(10 ** 6)


def check_cell(pa, pb, depth, max_depth, stats):
    p = arb_of(pa).union(arb_of(pb))
    theta = float_theta(float((pa + pb) / 2))
    try:
        U, qq = upper_h(p, theta)
        ok = U < 0
        overlap = qq["K"].overlaps(qq["K_n03"])
    except ValueError as err:
        ok, overlap, U = False, True, str(err)
    if ok:
        if not overlap:
            raise SystemExit(f"K forms do not overlap on [{pa}, {pb}]")
        stats["cells"] += 1
        stats["worst"] = max(stats["worst"], float(U.upper()))
        return True
    if depth >= max_depth:
        print(f"  FAILED cell [{float(pa):.10f}, {float(pb):.10f}] at depth {depth}: U = {U}", flush=True)
        return False
    mid = (pa + pb) / 2
    return check_cell(pa, mid, depth + 1, max_depth, stats) and check_cell(mid, pb, depth + 1, max_depth, stats)


def main_ii(p_lo, p_hi, n_cells, max_depth):
    ctx.prec = PREC
    edges = [p_lo + (p_hi - p_lo) * Fraction(k, n_cells) for k in range(n_cells + 1)]
    stats = {"cells": 0, "worst": -1e300}
    ok_all = True
    for pa, pb in zip(edges[:-1], edges[1:]):
        ok_all &= check_cell(pa, pb, 0, max_depth, stats)
    print(f"(ii) on p in [{float(p_lo)}, {float(p_hi)}] = [{p_lo}, {p_hi}]: {'PROVED' if ok_all else 'NOT PROVED'} "
          f"h(lam_loc(p), p) < 0; {stats['cells']} certified cells; worst upper bound {stats['worst']:+.3e}", flush=True)
    return 0 if ok_all else 1


def main_test():
    """Positive control: a float-known point is certified. Negative control: h at lam = 0.2 (< lam_0) must NOT come out negative."""
    ctx.prec = PREC
    U, qq = upper_h(arb_of(Fraction(21, 20)), float_theta(1.05))
    print(f"control +: p = 21/20: U = {U} (float h(lam_loc) = -0.2516); lam = {qq['lam']}; K overlap {qq['K'].overlaps(qq['K_n03'])}")
    assert U < 0
    # negative control: same bound at lam = 0.2 (below lam_0 = 0.391), where m_GK(0) > K - no theta may give U < 0
    p = arb_of(Fraction(21, 20))
    q = p / 2
    lam = arb_of(Fraction(1, 5))
    th = arb.pi() / p
    c, sn = -th.cos(), th.sin()
    eps = 1 - lam
    S = 1 + lam ** 2 + eps ** 2 * (c / sn) ** 2
    X = (S + (S ** 2 - 4 * lam ** 2).sqrt()) / 2
    sig = (1 + lam) / c
    r = (sig + (sig ** 2 - 4 * lam).sqrt()) / 2
    K = 2 * r ** (-q) * (r ** 2 - 2 * lam * r * c + lam ** 2) ** q * eps / (sn * (r - lam / r))
    best = min(float(((X ** q - (lam + arb_of(t) * eps) ** p) / (arb_of(t) * (1 - arb_of(t))) ** q - K).mid())
               for t in [Fraction(k, 200) for k in range(1, 200)])
    print(f"control -: p = 21/20, lam = 1/5: min over theta grid of the upper bound minus K = {best:+.4e} (must be > 0)")
    assert best > 0
    print("tests done")
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--test", action="store_true")
    ap.add_argument("--p-lo")
    ap.add_argument("--p-hi")
    ap.add_argument("--cells", type=int)
    ap.add_argument("--max-depth", type=int)
    args = ap.parse_args()
    if args.test:
        sys.exit(main_test())
    sys.exit(main_ii(Fraction(args.p_lo), Fraction(args.p_hi), args.cells, args.max_depth))


if __name__ == "__main__":
    main()
