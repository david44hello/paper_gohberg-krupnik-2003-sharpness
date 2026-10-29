#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# strip_corner_independent.py - Gohberg–Krupnik strip corner (S-c), SECOND code: g(delta, p, s) > 0 for p in [p_0, 1.2337027], 0 < delta <= 1/100 [-route C]
## version 0.10 - route C 20261027_2145 ET - second-order Taylor at (delta, s) = (0, s*(p)) + Hessian positive definite on window boxes
##   (mixed derivative from the two diagonal directions), mean value boxes outside the window, s-tails; independent of route B's even-form code
# Notation and formulas as in strip_bulk.py (lampos note Sec. 8): lam = 1 - delta, rho = 1 - s delta, q = p/2, sn = sin(pi/p),
#   c = -cos(pi/p), A = (1 - sn)/(2 sn), f_p(s) = p (A + s)/(s(1-s))^q, kappa0 = 2^q sn^{p-2} c^{1-q}, Omega(p) = min_s f_p - kappa0.
# PROOF of the claim, for p in [p_0, P_C] (p_0 = the unique zero of Omega in (1, 1.268]; Omega >= 0 on [p_0, 1.268], route A 21:21):
#   (a) delta = 0: g(0, p, s) = f_p(s) - kappa0, so g(0, p, s*) = Omega(p) and d_s g(0, p, s*) = 0, where s* = s*(p) is the critical point.
#   (b) d_delta g(0, p, s*) = k Omega(p), k = (pA + 1 - q)/2 > 0 (corner identity: route A 21:20, route B 21:23, two proofs).
#   (c) Taylor with integral remainder along the segment from (0, s*) to (delta, s), (u, delta) = (s - s*, delta):
#       g(delta, p, s) = Omega(p)(1 + k delta) + int_0^1 (1-t) (u, delta) H(t) (u, delta)^T dt,  H = Hessian of g in (s, delta).
#       If s*(p) and s lie in the window W, the segment lies in W x [0, delta]. This code proves H positive definite at EVERY point of
#       [P_A, P_C] x [0, D_C] x W (boxes with H_ss > 0, H_dd > 0, H_sd^2 < H_ss H_dd). Hence g >= Omega(p)(1 + k delta) >= 0, with
#       strict inequality unless (u, delta) = (0, 0); so g > 0 for delta > 0.
#   (d) s in [1/20, 19/20] outside W: mean value boxes prove g > 0 directly (for all p in [P_A, P_C], also p < p_0).
#   (e) s < 1/20 or s > 19/20: the s-tail bound (phi >= 1).
# Series tail of E(v) = ((1+v)^p - 1)/v (|v| <= 1/8, 24 terms, 1.2 < p < 1.3): |T| < 1e-20, |T_v| < 1e-18, |T_p| < 1e-18, |T_vv| < 1e-16
#   (the sums are evaluated in --test). Coefficient 2 is only used with p constant (Hessian directions): (1/2)T_vv v1^2 + T_v v2.
import argparse
import hashlib
import sys
from fractions import Fraction
from flint import arb, arb_series, ctx, fmpq

PREC_BITS = 120
P_A = fmpq(12336025, 10 ** 7)             # below p_0; the boxes start here
P_C = fmpq(12337027, 10 ** 7)             # the 'reach' bulk run covers p >= P_C and delta >= D_C
D_C = fmpq(1, 100)
W_LO, W_HI = fmpq(1, 4), fmpq(27, 100)    # window around s*(p) ~ 0.2607
S_TAIL = fmpq(1, 20)
SERIES_TERMS = 24
SERIES_RADIUS = fmpq(1, 8)
TAIL0, TAIL1, TAIL2 = arb("1e-20"), arb("1e-18"), arb("1e-16")


def ball(lo, hi):
    return arb((lo + hi) / 2, arb((hi - lo) / 2).upper())


def coeffs_padded(ser, n):
    cs = list(ser.coeffs())
    return cs + [arb(0)] * (n - len(cs))


def e_series(v, pp, n):
    """E(v) near v = 0: binomial series plus rigorous tail balls on coefficients 0, 1 and (p constant only) 2."""
    b_list = [pp]
    for k in range(1, SERIES_TERMS):
        b_list.append(b_list[-1] * (pp - k) / (k + 1))
    acc = b_list[-1]
    for b_k in reversed(b_list[:-1]):
        acc = b_k + v * acc
    cs = coeffs_padded(acc, n)
    vc, pc = coeffs_padded(v, n), coeffs_padded(pp, n)
    cs[0] += arb(0, TAIL0.upper())
    if n > 1:
        cs[1] += arb(0, (TAIL1 * (abs(vc[1]) + abs(pc[1]))).upper())
    if n > 2:
        if not all(x == 0 for x in pc[1:]):
            raise ValueError("coefficient-2 tail bound needs p constant")
        cs[2] += arb(0, (TAIL2 * (vc[1] * vc[1] + abs(vc[2]))).upper())
    if n > 3:
        raise ValueError("series length > 3 not supported")
    return arb_series(cs, prec=n)


def e_quot(v, pp, n):
    if abs(coeffs_padded(v, 1)[0]) <= arb(SERIES_RADIUS):
        return e_series(v, pp, n)
    return ((pp * (1 + v).log()).exp() - 1) / v


def angle_sin_cos(pp):
    ang = arb.pi() * (1 - 1 / pp)
    return ang.sin(), ang.cos()


def kappa_series(pp, dd):
    """K/delta, cancellation-free contact formula (accepted)."""
    q = pp / 2
    sn, c = angle_sin_cos(pp)
    lam = 1 - dd
    root_c = (dd * dd + 4 * lam * sn * sn).sqrt()
    r = (1 + lam + root_c) / (2 * c)
    zabs2 = (r - lam * c) * (r - lam * c) + lam * lam * sn * sn
    return 2 * ((-q) * r.log()).exp() * (q * zabs2.log()).exp() * c / (sn * root_c)


def t1_series(pp, dd, n):
    sn = angle_sin_cos(pp)[0]
    u = dd * dd / (4 * sn * sn) - dd
    x_ratio = 1 / (2 * sn) + (dd / (4 * sn * sn) - 1) / (1 + (1 + u).sqrt())
    return e_quot(dd * x_ratio, pp, n) * x_ratio


def g_series(pp, dd, ss, n):
    num = t1_series(pp, dd, n) + ss * e_quot(-(ss * dd), pp, n)
    half = arb(1) / 2
    first = num * ((-(pp / 2)) * (arb(1) / 4 - (ss - half) * (ss - half)).log()).exp()
    return first - kappa_series(pp, dd)


def lift(balls, direction, n):
    """direction: None (constants), an index (that coordinate + t), or a tuple of per-coordinate t-coefficients."""
    if direction is None:
        steps = (0, 0, 0)
    elif isinstance(direction, tuple):
        steps = direction
    else:
        steps = tuple(1 if k == direction else 0 for k in range(3))
    return [arb_series([b, st] if st else [b], prec=n) for b, st in zip(balls, steps)]


def s_star(pp):
    """Critical point of f_p (cancellation-free root of (2q-1)s^2 + (1-q+2qA)s - qA = 0)."""
    sn = angle_sin_cos(pp)[0]
    q = pp / 2
    A = (1 - sn) / (2 * sn)
    b = 1 - q + 2 * q * A
    return 2 * q * A / (b + (b * b + 4 * (2 * q - 1) * q * A).sqrt())


# ---- (c) Hessian positive definite on window boxes ----

def hessian_entries(box):
    """Enclosures of H_ss, H_dd, H_sd over box = ((p), (delta), (s)) via coefficient 2 of series along s, delta, s+delta, s-delta."""
    balls = [ball(lo, hi) for lo, hi in box]
    coef2 = {}
    for name, steps in [("ss", (0, 0, 1)), ("dd", (0, 1, 0)), ("plus", (0, 1, 1)), ("minus", (0, -1, 1))]:
        coef2[name] = coeffs_padded(g_series(*lift(balls, steps, 3), 3), 3)[2]
    return 2 * coef2["ss"], 2 * coef2["dd"], (coef2["plus"] - coef2["minus"]) / 2


def hessian_box_ok(box, ratio):
    """H positive definite on the box, with H_sd^2 < ratio * H_ss H_dd (ratio = 1 for the claim; < 1 for the control)."""
    try:
        h_ss, h_dd, h_sd = hessian_entries(box)
    except ValueError:
        return False
    return bool(h_ss > 0 and h_dd > 0 and (h_sd * h_sd - ratio * h_ss * h_dd) < 0)


def bisect_all(box0, test, max_boxes):
    """Adaptive bisection (relative widths) until test(box) holds on every piece; returns (ok, boxes used)."""
    scales = [P_C - P_A, D_C, W_HI - W_LO]
    stack, used = [box0], 0
    while stack:
        box = stack.pop()
        used += 1
        if used > max_boxes:
            return False, used
        if test(box):
            continue
        k = max(range(3), key=lambda j: (box[j][1] - box[j][0]) / scales[j])
        lo, hi = box[k]
        m = (lo + hi) / 2
        stack += [tuple((m, hi) if j == k else iv for j, iv in enumerate(box)),
                  tuple((lo, m) if j == k else iv for j, iv in enumerate(box))]
    return True, used


# ---- (d) mean value boxes outside the window, (e) s-tails ----

def box_lower(box):
    mids = [arb((lo + hi) / 2) for lo, hi in box]
    halfs = [arb((hi - lo) / 2) for lo, hi in box]
    balls = [ball(lo, hi) for lo, hi in box]
    try:
        total = coeffs_padded(g_series(*lift(mids, None, 1), 1), 1)[0]
        errs = []
        for k in range(3):
            der = coeffs_padded(g_series(*lift(balls, k, 2), 2), 2)[1]
            if not der.is_finite():
                return None
            errs.append(abs(der) * halfs[k])
            total -= errs[-1]
    except ValueError:
        return None
    return total, errs


def certify_mvf(box0, max_boxes):
    scales = [P_C - P_A, D_C, fmpq(1)]
    stack, used = [box0], 0
    while stack:
        box = stack.pop()
        used += 1
        if used > max_boxes:
            return False, used
        res = box_lower(box)
        if res is not None and res[0] > 0:
            continue
        if res is None:
            k = max(range(3), key=lambda j: (box[j][1] - box[j][0]) / scales[j])
        else:
            k = max(range(3), key=lambda j: res[1][j].upper())
        lo, hi = box[k]
        m = (lo + hi) / 2
        stack += [tuple((m, hi) if j == k else iv for j, iv in enumerate(box)),
                  tuple((lo, m) if j == k else iv for j, iv in enumerate(box))]
    return True, used


def tails_ok(rect):
    pp, dd = [arb_series([ball(lo, hi)], prec=1) for lo, hi in rect]
    try:
        t1 = coeffs_padded(t1_series(pp, dd, 1), 1)[0]
        kap = coeffs_padded(kappa_series(pp, dd), 1)[0]
    except ValueError:
        return False
    s_pow = ((coeffs_padded(pp, 1)[0] / 2) * arb(S_TAIL).log()).exp()
    return bool((t1 / s_pow - kap > 0) and ((t1 + 1 - arb(S_TAIL)) / s_pow - kap > 0))


# ---- driver ----

def md5_self():
    return hashlib.md5(open(__file__, "rb").read()).hexdigest()


def window_contains_s_star():
    sst = s_star(ball(P_A, P_C))
    return bool(sst > arb(W_LO) and sst < arb(W_HI)), sst


def main_certify(max_boxes):
    ctx.prec = PREC_BITS
    print(f"# strip_corner_independent.py md5 {md5_self()}, prec {PREC_BITS} bits; p in [{float(P_A)}, {float(P_C)}], "
          f"delta in [0, {float(D_C)}], window s in [{float(W_LO)}, {float(W_HI)}]", flush=True)
    ok_w, sst = window_contains_s_star()
    print(f"(c0) s*(p) in the window for all p: {'PROVED' if ok_w else 'NOT proved'} (s* in {sst.str(8)})", flush=True)
    win = ((P_A, P_C), (fmpq(0), D_C), (W_LO, W_HI))
    ok_h, n_h = bisect_all(win, lambda b: hessian_box_ok(b, arb(1)), max_boxes)
    print(f"(c)  Hessian positive definite on the window: {'PROVED' if ok_h else 'NOT proved'} ({n_h} boxes)", flush=True)
    ok_l, n_l = certify_mvf(((P_A, P_C), (fmpq(0), D_C), (S_TAIL, W_LO)), max_boxes)
    ok_r, n_r = certify_mvf(((P_A, P_C), (fmpq(0), D_C), (W_HI, 1 - S_TAIL)), max_boxes)
    print(f"(d)  g > 0 for s in [0.05, 0.25] and [0.27, 0.95]: {'PROVED' if ok_l and ok_r else 'NOT proved'} ({n_l} + {n_r} boxes)", flush=True)
    ok_t = tails_ok(((P_A, P_C), (fmpq(0), D_C)))
    print(f"(e)  s-tails s < 0.05, s > 0.95: {'PROVED' if ok_t else 'NOT proved'}", flush=True)
    c1 = certify_mvf(win, 20000)
    print(f"CONTROL 1  mean value boxes alone on the window (contains the touching zero; must FAIL): "
          f"{'PROVED (BAD)' if c1[0] else 'refused (good)'} ({c1[1]} boxes)", flush=True)
    c2 = bisect_all(win, lambda b: hessian_box_ok(b, arb("0.3")), 20000)
    print(f"CONTROL 2  H_sd^2 < 0.3 H_ss H_dd on the window (false: the ratio is 0.43 at the corner point; must FAIL): "
          f"{'PROVED (BAD)' if c2[0] else 'refused (good)'} ({c2[1]} boxes)", flush=True)
    all_ok = ok_w and ok_h and ok_l and ok_r and ok_t
    controls = not c1[0] and not c2[0]
    print(f"CLAIM g > 0 for p in [p_0, 1.2337027], 0 < delta <= 0.01, all s in (0,1) (given Omega >= 0 on [p_0, P_C] and the corner "
          f"identity): {'PROVED' if all_ok else 'NOT proved'}; controls {'good' if controls else 'BAD'}")
    print(f"# md5 at end {md5_self()}")
    return all_ok and controls


def main_test():
    ctx.prec = PREC_BITS
    import mpmath as mp
    mp.mp.dps = 50

    def dec(text):
        frac = Fraction(text)
        return fmpq(frac.numerator, frac.denominator)

    def direct_g(p, dl, s):
        s0, c0 = mp.sin(mp.pi / p), -mp.cos(mp.pi / p)
        C = (dl + mp.sqrt(dl ** 2 + 4 * s0 ** 2 * (1 - dl))) / (2 * s0)
        kap = 2 * C * s0 ** (p - 2) * c0 ** (1 - p / 2) * (C ** 2 + 1 - dl) ** (p / 2 - 1)
        return (C ** p - (1 - s * dl) ** p) / (dl * (s * (1 - s)) ** (p / 2)) - kap

    def mine(p, dl, s, n=1, direction=None):
        return coeffs_padded(g_series(*lift([arb(p), arb(dl), arb(s)], direction, n), n), n)

    for p, dl, s in [("1.2336026", "0.005", "0.26"), ("1.2337", "0.01", "0.3"), ("1.25", "0.3", "0.28")]:
        got = float(mine(dec(p), dec(dl), dec(s))[0].mid())
        assert abs(got - float(direct_g(mp.mpf(p), mp.mpf(dl), mp.mpf(s)))) < 1e-12, (p, dl, s)
    # tail constants (|v| <= 1/8, terms k > 24): value, v-derivative, p-derivative, second v-derivative
    sums = [mp.nsum(lambda k: 8 ** (-(k - 1)), [25, mp.inf]), mp.nsum(lambda k: (k - 1) * 8 ** (-(k - 2)), [25, mp.inf]),
            mp.nsum(lambda k: (9 + k) * 8 ** (-(k - 1)), [25, mp.inf]), mp.nsum(lambda k: (k - 1) * (k - 2) * 8 ** (-(k - 3)), [25, mp.inf])]
    assert sums[0] < 1e-20 and sums[1] < 1e-18 and sums[2] < 1e-18 and sums[3] < 1e-16, sums
    # corner identity (b): d_delta g(0, p, s*) = k Omega(p) - checked in Arb (the difference ball contains 0 and is tiny)
    for p in [fmpq(121, 100), fmpq(5, 4), fmpq(129, 100)]:
        sst = s_star(arb(p))
        omega = coeffs_padded(g_series(*lift([arb(p), arb(0), sst], None, 1), 1), 1)[0]
        g_d = coeffs_padded(g_series(*lift([arb(p), arb(0), sst], 1, 2), 2), 2)[1]
        sn = angle_sin_cos(arb(p))[0]
        k_fac = (p * (1 - sn) / (2 * sn) + 1 - arb(p) / 2) / 2
        diff = g_d - k_fac * omega
        assert diff.contains(0) and diff.rad() < 1e-15, (p, diff)
    # Hessian at the corner point against mpmath (H_ss 17.4728, H_dd 0.380706, H_sd -1.68377 at p = 1.2336026038)
    p0 = dec("1.2336026038")
    sst = s_star(arb(p0))
    pt = [arb(p0), arb(0), sst]
    h_ss = 2 * coeffs_padded(g_series(*lift(pt, (0, 0, 1), 3), 3), 3)[2]
    h_dd = 2 * coeffs_padded(g_series(*lift(pt, (0, 1, 0), 3), 3), 3)[2]
    c_p = coeffs_padded(g_series(*lift(pt, (0, 1, 1), 3), 3), 3)[2]
    c_m = coeffs_padded(g_series(*lift(pt, (0, -1, 1), 3), 3), 3)[2]
    h_sd = (c_p - c_m) / 2
    for got, want in [(h_ss, 17.472756972), (h_dd, 0.380705533), (h_sd, -1.683770317)]:
        assert abs(float(got.mid()) - want) < 1e-8, (got, want)
    # the two E branches agree on coefficients 0..2 (p constant)
    for v in [fmpq(1, 10), fmpq(-1, 10)]:
        vs, ps = arb_series([arb(v), 1], prec=3), arb_series([arb(fmpq(5, 4))], prec=3)
        ser = coeffs_padded(e_series(vs, ps, 3), 3)
        dirc = coeffs_padded(((ps * (1 + vs).log()).exp() - 1) / vs, 3)
        assert all(abs(float((x - y).mid())) < 1e-15 for x, y in zip(ser, dirc)), (v, ser, dirc)
    print("tests passed")


def main():
    ap = argparse.ArgumentParser(description="Gohberg–Krupnik strip corner (S-c), second code [-route C]")
    ap.add_argument("--test", action="store_true")
    ap.add_argument("--max-boxes", type=int, default=2_000_000)
    args = ap.parse_args()
    if args.test:
        main_test()
        return 0
    return 0 if main_certify(args.max_boxes) else 1


if __name__ == "__main__":
    sys.exit(main())
