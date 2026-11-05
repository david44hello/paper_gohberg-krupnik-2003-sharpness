#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
# corner_comparison.py - Gohberg–Krupnik strip (S-c): READ 1 checks of route B's strip_corner.py v0.30 (md5 c61003de) 
## version 0.10 - route A 20261027_2153 ET - (a) arb(mid, rad-ball) radius; (b) max tail radius R in exprel; (c) e2, c4 by my own mpmath g
#
# (a) ball(lo, hi) = (lo+hi)/2 + arb(0, (hi-lo)/2) with arb endpoints: is the radius ball's upper end kept (no gap between cells)?
# (b) exprel_tail(R) = R^N/(N+1)!/(1 - R/(N+2)) is a valid bound only for R < N + 2 = 42: record the largest R used on sample cells.
# (c) Et(eps, sigma) = g/V from MY evaluator (closed-form kappa, my C(d), (delta, s) coordinates; mpmath 50 digits):
#     e2 = lim (Et - Et0)/eps^2 by Richardson, c4 by finite differences, compared with his arb_series enclosures.

import sys
import mpmath as mp
import flint
from flint import arb

sys.path.insert(0, "programs")
import strip_corner as nc  # noqa: E402

mp.mp.dps = 50
P0 = mp.mpf('1.2336026038408565')


def check_ball_radius():
    lo, hi = arb(1) / 3, arb(2) / 3
    rad_ball = (hi - lo) / 2 + arb(0, arb("1e-20"))
    made = arb(0, rad_ball)
    print(f"(a) arb(0, r) with r = {rad_ball.str(25, radius=True)}: radius kept = {made.rad()}  (upper end of r = {rad_ball.upper()})")
    print(f"    ball(1/3, 2/3) = {nc.ball(lo, hi).str(25, radius=True)}; contains exact 1/3 and 2/3: "
          f"{nc.ball(lo, hi).contains(lo) and nc.ball(lo, hi).contains(hi)}")


def check_tail_radius():
    seen = []
    original = nc.exprel_tail

    def recording(radius):
        seen.append(float(radius.upper().mid()))
        return original(radius)
    nc.exprel_tail = recording
    for sig in [("0.045", "0.055"), ("0.25", "0.26"), ("0.94", "0.95")]:
        nc.tau_bound(nc.ball(arb(sig[0]), arb(sig[1])), nc.ball(nc.P_A, nc.P_B))
        nc.coeffs_at(arb(0), nc.ball(arb(sig[0]), arb(sig[1])), nc.ball(nc.P_A, nc.P_B), 3)
    nc.certify_edges()
    nc.exprel_tail = original
    print(f"(b) exprel tail radius R over {len(seen)} calls (3 sigma cells x 64 sub-balls + edges): max R = {max(seen):.4f} (< 42 needed)")


def my_et(eps, sigma, p):
    q, s0, c0 = p / 2, mp.sin(mp.pi / p), -mp.cos(mp.pi / p)
    d = -mp.expm1(-eps)
    s = -mp.expm1(-sigma * eps) / d
    cc = d / (2 * s0) + mp.sqrt(d ** 2 / (4 * s0 ** 2) + 1 - d)
    g = (cc ** p - (1 - s * d) ** p) / (d * (s * (1 - s)) ** q) - 2 * cc * s0 ** (p - 2) * c0 ** (1 - q) * (cc ** 2 + 1 - d) ** (q - 1)
    return g / (mp.exp((1 - q) * eps / 2) * cc ** (p / 2))


def my_et0(sigma, p):
    q, s0, c0 = p / 2, mp.sin(mp.pi / p), -mp.cos(mp.pi / p)
    big_a = (1 - s0) / (2 * s0)
    return p * (big_a + sigma) / (sigma * (1 - sigma)) ** q - 2 ** q * s0 ** (p - 2) * c0 ** (1 - q)


def s_star0(p):
    q, s0 = p / 2, mp.sin(mp.pi / p)
    big_a = (1 - s0) / (2 * s0)
    bq = 1 - q + 2 * q * big_a
    return 2 * q * big_a / (bq + mp.sqrt(bq ** 2 + 4 * (2 * q - 1) * q * big_a))


def my_e2_c4(sigma, p):
    """Even function: Et = Et0 + e2 x + c4 x^2 + ..., x = eps^2; fit on x = h^2, (2h)^2, (3h)^2 (polynomial in x of degree 2)."""
    et0 = my_et0(sigma, p)
    hh = mp.mpf('1e-4')
    xs = [(k * hh) ** 2 for k in (1, 2, 3)]
    ys = [(my_et(k * hh, sigma, p) - et0) / x for k, x in zip((1, 2, 3), xs)]
    c4 = ((ys[2] - ys[0]) / (xs[2] - xs[0]))
    e2 = ys[0] - c4 * xs[0]
    return e2, c4


def check_e2():
    for sigma, p, label in [(mp.mpf('0.3'), mp.mpf('1.2336026'), "his test point"), (s_star0(P0), P0, "(sigma*, p_0)")]:
        e2, c4 = my_e2_c4(sigma, p)
        coeffs = nc.coeffs_at(arb(0), arb(mp.nstr(sigma, 30)), arb(mp.nstr(p, 30)), 5)
        print(f"(c) {label:<15} sigma = {mp.nstr(sigma, 10)}: my e2 = {mp.nstr(e2, 12)}, his e2 = {coeffs[2].str(12)}; "
              f"my c4(0) = {mp.nstr(c4, 6)}, his c4(0) = {coeffs[4].str(6)}")
    big = max(abs(my_e2_c4_at(mp.mpf(xi), mp.mpf('0.26'), P0)) for xi in ['0.0', '0.02', '0.04', '0.0512'])
    print(f"(c) my |c4(xi)| at sigma 0.26, p_0, xi in {{0, 0.02, 0.04, 0.0512}}: max = {mp.nstr(big, 6)};  "
          f"his tau/eps1^2 bound (max over all cells) = {0.01907082936928859 / float(nc.EPS1.mid()) ** 2:.4f}")


def my_e2_c4_at(xi, sigma, p):
    """c4(xi) = Et''''(xi)/24 by mpmath numerical differentiation."""
    return mp.diff(lambda e: my_et(e, sigma, p), xi + mp.mpf('1e-3') if xi == 0 else xi, 4) / 24


def main_corner_cert_read():
    flint.ctx.prec = 128
    check_ball_radius()
    check_tail_radius()
    check_e2()


def main():
    main_corner_cert_read()


if __name__ == "__main__":
    main()
