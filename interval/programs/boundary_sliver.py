#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
# boundary_sliver.py - Gohberg–Krupnik edge lam = lam_loc: Arb proof that h(lam_loc(p), p) < 0 for p in [1.2134, 1.2134904] (covers up to p_c) [-route C]
## version 0.10 - route C 20261027_1708 ET - h <= delta g(delta,p,s), g = [T1 + s phi(s delta)]/(s(1-s))^q - K/delta (rescaling of route B's
##   lampos Sec. 8), MY contact K, mean-value enclosures (delta = 0 allowed in a cell); plus 1 - lam_loc(p) <= DELTA_HI; two controls that must fail
# Exact facts used (accepted 019 notes): with a = pi(p-1)/p, sn = sin a, c = cos a (= |cos(pi/p)|), lam = 1 - delta:
#   GK:  C = delta/(2 sn) + sqrt((1 - delta/2)^2 + delta^2 c^2/(4 sn^2)), so (C - 1)/delta = 1/(2 sn) + (delta/(4 sn^2) - 1)/(1 + sqrt(1 + u)),
#        u = delta^2/(4 sn^2) - delta  (no division by delta).
#   m_GK(0) <= (1-lam)^p (C^p - rho^p)/((1-rho)(rho-lam))^q at rho = 1 - s delta, = delta [T1 + s phi(s delta)]/(s(1-s))^q,
#        T1 = (C^p - 1)/delta = [(C^p - 1)/(C - 1)] (C - 1)/delta,  phi(x) = (1 - (1-x)^p)/x;  both quotients = p xi^{p-1}, xi in the hull (MVT).
#   K/delta = 2 r^{-q} |zeta* + lam|^p / (sn sqrt(sig^2 - 4 lam)),  sig = (1 + lam)/c, r = (sig + sqrt(sig^2 - 4 lam))/2,
#        |zeta* + lam|^2 = lam^2 - 2 lam r c + r^2  (contact formula; = -m'(pi/p)/q).
#   lam_loc = (1 - d)/(1 + d), d^2 = sn^2 (p p'/4 - 1 - c^2)/c^4 (Theorem L); 1 - lam_loc = 2d/(1+d) <= 2d.
import argparse
import hashlib
import sys
from flint import arb, ctx, fmpq

PREC_BITS = 160
DELTA_HI = fmpq(3, 100)
S_FIX = fmpq(2742, 10000)               # near s*(p_c) = 0.27427


def ball(lo, hi):
    return arb((lo + hi) / 2, arb((hi - lo) / 2).upper())


def mvt_pow_quot(lo_pt, hi_pt, p):
    """Enclosure of p xi^{p-1} for xi in [lo_pt, hi_pt] (arb balls), i.e. of ((x)^p - 1)/(x - 1)-type quotients."""
    xi = lo_pt.union(hi_pt)
    return p * ((p - 1) * xi.log()).exp()


def g_upper(p_lo, p_hi, d_lo, d_hi, s):
    """Rigorous upper bound of g(delta, p, s) over the cell [p_lo, p_hi] x [d_lo, d_hi]."""
    p, dl, s = ball(p_lo, p_hi), ball(d_lo, d_hi), arb(s)
    q, one = p / 2, arb(1)
    a = arb.pi() * (p - 1) / p
    sn, c = a.sin(), a.cos()
    lam = one - dl
    u = dl * dl / (4 * sn * sn) - dl
    cm1_over_d = 1 / (2 * sn) + (dl / (4 * sn * sn) - 1) / (1 + (1 + u).sqrt())
    C = one + dl * cm1_over_d
    t1 = mvt_pow_quot(one, C, p) * cm1_over_d
    phi = mvt_pow_quot(one - s * dl, one, p)
    first = (t1 + s * phi) * ((-q) * (s * (one - s)).log()).exp()
    sig = (one + lam) / c
    root = (sig * sig - 4 * lam).sqrt()
    r = (sig + root) / 2
    zabs2 = lam * lam - 2 * lam * r * c + r * r
    k_over_d = 2 * ((-q) * r.log()).exp() * (q * zabs2.log()).exp() / (sn * root)
    return (first - k_over_d).upper()


def lamloc_gap_upper(p_lo, p_hi):
    """Upper bound of 2d >= 1 - lam_loc over the p-cell (d^2 clipped at 0: for p >= p_c there is no lam_loc)."""
    p = ball(p_lo, p_hi)
    a = arb.pi() * (p - 1) / p
    sn, c = a.sin(), a.cos()
    d2 = sn * sn * (p * p / (4 * (p - 1)) - 1 - c * c) / c ** 4
    d2u = max(d2.upper(), arb(0))
    return 2 * d2u.sqrt()


def certify(p_lo, p_hi, s, max_cells):
    """Adaptive bisection in (p, delta) for g < 0 on [p_lo, p_hi] x [0, DELTA_HI]; returns (ok, cells)."""
    stack, used = [(p_lo, p_hi, fmpq(0), DELTA_HI)], 0
    while stack:
        a, b, c, d = stack.pop()
        used += 1
        if used > max_cells:
            return False, used
        if g_upper(a, b, c, d, s) < 0:
            continue
        if (b - a) * 300 > (d - c):                       # split the relatively wider side
            m = (a + b) / 2
            stack += [(a, m, c, d), (m, b, c, d)]
        else:
            m = (c + d) / 2
            stack += [(a, b, c, m), (a, b, m, d)]
    return True, used


def gap_ok(p_lo, p_hi, cells):
    h = (p_hi - p_lo) / cells
    return all(lamloc_gap_upper(p_lo + k * h, p_lo + (k + 1) * h) <= arb(DELTA_HI) for k in range(cells))


def main_certify():
    ctx.prec = PREC_BITS
    md5 = hashlib.md5(open(__file__, "rb").read()).hexdigest()
    print(f"# boundary_sliver.py md5 {md5}, prec {PREC_BITS}, DELTA_HI {DELTA_HI}, s {S_FIX}")
    P_LO, P_HI = fmpq(12134, 10000), fmpq(12134904, 10000000)
    ok, n = certify(P_LO, P_HI, S_FIX, 100000)
    print(f"CLAIM g < 0 on [1.2134, 1.2134904] x [0, 3/100]: {'PROVED' if ok else 'NOT proved'} ({n} cells)")
    ok_gap = gap_ok(P_LO, P_HI, 200)
    print(f"CLAIM 1 - lam_loc(p) <= 3/100 on [1.2134, 1.2134904] (200 p-cells): {'PROVED' if ok_gap else 'NOT proved'}")
    c1, n1 = certify(P_LO, P_HI, fmpq(1, 50), 3000)
    print(f"CONTROL s = 1/50 (far from s*) must FAIL: {'PROVED (BAD)' if c1 else 'refused (good)'} ({n1} cells)")
    c2, n2 = certify(fmpq(125, 100), fmpq(12501, 10000), fmpq(3, 10), 3000)
    print(f"CONTROL p in [1.25, 1.2501] (Gamma > 0 there) must FAIL: {'PROVED (BAD)' if c2 else 'refused (good)'} ({n2} cells)")
    print(f"# md5 at end {hashlib.md5(open(__file__, 'rb').read()).hexdigest()}")
    return ok and ok_gap and not c1 and not c2


def main_test():
    ctx.prec = PREC_BITS
    # (1) delta = 0: the MVT hulls collapse, so g = p(A+s)/(s(1-s))^q - kappa_0 = Gamma(p_c) up to O((s - s*)^2) = -0.0243966 (float 17:07)
    pc = fmpq(12134903, 10000000)
    v0 = g_upper(pc, pc, fmpq(0), fmpq(0), S_FIX)
    assert abs(float(v0) + 0.0243966) < 1e-6, v0
    # (2) delta = 0.01: the exact float value -0.024489 must lie BELOW the rigorous upper bound, which stays < 0 (MVT hull costs ~1e-3)
    v = g_upper(pc, pc, fmpq(1, 100), fmpq(1, 100), S_FIX)
    assert -0.024489 <= float(v) < 0 and float(v) + 0.024489 < 2e-3, v
    print("tests passed")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--test", action="store_true")
    if ap.parse_args().test:
        main_test()
        return
    sys.exit(0 if main_certify() else 1)


if __name__ == "__main__":
    main()
