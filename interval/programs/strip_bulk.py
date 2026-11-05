#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
# strip_bulk.py - Gohberg–Krupnik strip (S-b): Arb proof that g(delta, p, s) > 0 on the strip p in [p_0, 1.268] AWAY from the corner [-route C]
## version 0.20 - route C 20261027_2131 ET - fix: the reported smallest lower bound tracks exact lower endpoints (ball '<' between
##   overlapping balls is False, so v0.10 reported a too-LARGE value; the certification test itself is unchanged); 'corner' choice main|reach
## version 0.10 - route C 20261027_2125 ET - 3-D mean value form (arb_series derivative in each direction), s-tails by the numerator bound,
##   removable delta = 0 quotient via the binomial series with a rigorous tail; MY contact K; two controls that must FAIL
# Claim (lampos note Sec. 8 rescaling; lam = 1 - delta, rho = 1 - s delta):  h(lam, p) = m_GK(0) - K = delta * inf_{0<s<1} g(delta, p, s),
#   g = [T1 + s phi(s delta)]/(s(1-s))^q - K/delta.  Certified: g > 0 for ALL s in (0, 1) and (p, delta) in
#   REGION A = [1.2336025, 1.268] x [DELTA1, 1]   and   REGION B = [1.2336027 + ETA, 1.268] x [0, DELTA1]   (DELTA1 = 1/20, ETA = 1/2000).
#   The complement in the strip, [p_0, 1.2341027] x [0, 0.05], is route B's corner lemma (S-c).  delta = 1 (lam = 0) is inside REGION A.
# Exact facts used, with a = pi(p-1)/p, sn = sin a = sin(pi/p), c = cos a = -cos(pi/p) > 0, q = p/2:
#   GK: C = 1 + delta X, X = (C-1)/delta = 1/(2 sn) + (delta/(4 sn^2) - 1)/(1 + sqrt(1 + u)), u = delta^2/(4 sn^2) - delta (no division by delta).
#   T1 = (C^p - 1)/delta = E(C - 1) X,  s phi(s delta) = (1 - (1 - s delta)^p)/delta = s E(-s delta),  E(v) := ((1+v)^p - 1)/v.
#   K/delta = 2 r^{-q} zabs2^q/(sn root), sig = (1+lam)/c, root = sqrt(sig^2 - 4 lam), r = (sig + root)/2, zabs2 = lam^2 - 2 lam r c + r^2.
#   E near v = 0: E(v) = sum_{k>=1} b_k v^{k-1}, b_1 = p, b_{k+1} = b_k (p-k)/(k+1); for 1.2 < p < 1.3 and k >= 2: |b_k| <= 1 and
#   |d b_k/dp| <= (9 + k)|b_k|.  With |v| <= 1/8 and SERIES_TERMS = 24 terms the tail is < 1e-20, its v- and p-derivatives < 1e-18.
#   s-tails: phi >= 1 ((1-x)^p <= 1-x), so N := T1 + s phi >= T1 (s <= S_TAIL) and N >= T1 + 1 - S_TAIL (s >= 1 - S_TAIL), and
#   (s(1-s))^q <= S_TAIL^q there; hence g >= N_low/S_TAIL^q - K/delta.
import argparse
import hashlib
import sys
from fractions import Fraction
from flint import arb, arb_series, ctx, fmpq

PREC_BITS = 120
P_LO = fmpq(12336025, 10 ** 7)            # below p_0 (Omega(P_LO) < 0, two codes); REGION A starts here
P0_UP = fmpq(12336027, 10 ** 7)           # p_0 < P0_UP (route B + route C + route A Arb)
P_HI = fmpq(317, 250)                     # 1.268 > 3 - sqrt3
DELTA1 = fmpq(1, 20)                      # route B's corner (S-c) is [p_0, P0_UP + ETA] x [0, DELTA1]
ETA = fmpq(1, 2000)
CORNERS = {"main": (DELTA1, ETA), "reach": (fmpq(1, 100), fmpq(1, 10000))}   # reach = a smaller corner, for slack
S_TAIL = fmpq(1, 20)
SERIES_TERMS = 24
SERIES_RADIUS = fmpq(1, 8)
TAIL0, TAIL1 = arb("1e-20"), arb("1e-18")


def ball(lo, hi):
    return arb((lo + hi) / 2, arb((hi - lo) / 2).upper())


def coeffs_padded(ser, n):
    cs = list(ser.coeffs())
    return cs + [arb(0)] * (n - len(cs))


def e_series(v, pp, n):
    """E(v) = ((1+v)^p - 1)/v near v = 0: truncated binomial series plus the rigorous tail ball (see header)."""
    b_list = [pp]
    for k in range(1, SERIES_TERMS):
        b_list.append(b_list[-1] * (pp - k) / (k + 1))
    acc = b_list[-1]
    for b_k in reversed(b_list[:-1]):
        acc = b_k + v * acc
    cs = coeffs_padded(acc, n)
    cs[0] += arb(0, TAIL0.upper())
    if n > 1:
        vd, pd = coeffs_padded(v, n)[1], coeffs_padded(pp, n)[1]
        cs[1] += arb(0, (TAIL1 * (abs(vd) + abs(pd))).upper())
    return arb_series(cs, prec=n)


def e_quot(v, pp, n):
    """E(v) = ((1+v)^p - 1)/v for arb_series v (v > -1); the series branch whenever |v| <= 1/8 on the whole ball."""
    if abs(coeffs_padded(v, 1)[0]) <= arb(SERIES_RADIUS):
        return e_series(v, pp, n)
    return ((pp * (1 + v).log()).exp() - 1) / v


def angle_sin_cos(pp):
    """sn = sin(pi/p), c = -cos(pi/p), via a = pi - pi/p (p occurs once: less ball overestimation)."""
    ang = arb.pi() * (1 - 1 / pp)
    return ang.sin(), ang.cos()


def kappa_series(pp, dd):
    """K/delta by MY contact formula (edge certificate, ACCEPTED); analytic at delta = 0."""
    q = pp / 2
    sn, c = angle_sin_cos(pp)
    lam = 1 - dd
    # cancellation-free forms: sig^2 - 4 lam = (delta^2 + 4 lam sn^2)/c^2,  zabs2 = (r - lam c)^2 + lam^2 sn^2
    root_c = (dd * dd + 4 * lam * sn * sn).sqrt()
    root = root_c / c
    r = (1 + lam + root_c) / (2 * c)
    zabs2 = (r - lam * c) * (r - lam * c) + lam * lam * sn * sn
    return 2 * ((-q) * r.log()).exp() * (q * zabs2.log()).exp() / (sn * root)


def t1_series(pp, dd, n):
    """T1 = (C^p - 1)/delta = E(C - 1) (C - 1)/delta, no division by delta."""
    sn = angle_sin_cos(pp)[0]
    u = dd * dd / (4 * sn * sn) - dd
    x_ratio = 1 / (2 * sn) + (dd / (4 * sn * sn) - 1) / (1 + (1 + u).sqrt())
    return e_quot(dd * x_ratio, pp, n) * x_ratio


def g_series(pp, dd, ss, n):
    """g(delta, p, s) as an arb_series of length n (inputs are arb_series)."""
    num = t1_series(pp, dd, n) + ss * e_quot(-(ss * dd), pp, n)
    first = num * ((-(pp / 2)) * (arb(1) / 4 - (ss - arb(1) / 2) * (ss - arb(1) / 2)).log()).exp()
    return first - kappa_series(pp, dd)


def lift(balls, direction, n):
    """arb_series inputs: the coordinate `direction` gets the series variable, the others are constants."""
    return [arb_series([b, 1] if k == direction else [b], prec=n) for k, b in enumerate(balls)]


def box_lower(box, shift):
    """Rigorous lower bound of g - shift on box = ((p_lo,p_hi), (d_lo,d_hi), (s_lo,s_hi)); returns (lower arb, per-direction errors) or None."""
    mids = [arb((lo + hi) / 2) for lo, hi in box]
    halfs = [arb((hi - lo) / 2) for lo, hi in box]
    balls = [ball(lo, hi) for lo, hi in box]
    try:
        total = coeffs_padded(g_series(*lift(mids, -1, 1), 1), 1)[0] - shift
        errs = []
        for k in range(3):
            der = coeffs_padded(g_series(*lift(balls, k, 2), 2), 2)[1]
            if not der.is_finite():
                return None
            errs.append(abs(der) * halfs[k])
            total -= errs[-1]
    except ValueError:            # a series division by a ball containing 0: NOT certified, the box is split
        return None
    return total, errs


def split(box, k):
    lo, hi = box[k]
    m = (lo + hi) / 2
    return [tuple((m, hi) if j == k else iv for j, iv in enumerate(box)),
            tuple((lo, m) if j == k else iv for j, iv in enumerate(box))]


def widest_relative(box, scales):
    return max(range(len(box)), key=lambda k: (box[k][1] - box[k][0]) / scales[k])


def certify_middle(box0, shift, max_boxes):
    """Adaptive bisection of g - shift > 0 over box0 (all three directions). Returns (ok, boxes used, smallest certified lower bound)."""
    scales = [P_HI - P_LO, fmpq(1), fmpq(1)]
    stack, used, worst = [box0], 0, None
    while stack:
        box = stack.pop()
        used += 1
        if used > max_boxes:
            return False, used, worst
        res = box_lower(box, shift)
        if res is not None and res[0] > 0:
            low = res[0].lower()                  # an exact point: comparisons below are exact
            worst = low if worst is None or low < worst else worst
            continue
        k = widest_relative(box, scales) if res is None else max(range(3), key=lambda j: res[1][j].upper())
        stack += split(box, k)
    return True, used, worst


def tails_ok(rect):
    """Both s-tails over the (p, delta) rectangle, with balls (no series variable)."""
    pp, dd = [arb_series([ball(lo, hi)], prec=1) for lo, hi in rect]
    try:
        t1 = coeffs_padded(t1_series(pp, dd, 1), 1)[0]
        kap = coeffs_padded(kappa_series(pp, dd), 1)[0]
    except ValueError:
        return False
    s_pow = ((coeffs_padded(pp, 1)[0] / 2) * arb(S_TAIL).log()).exp()
    return (t1 / s_pow - kap > 0) and ((t1 + 1 - arb(S_TAIL)) / s_pow - kap > 0)


def certify_tails(rect0, max_rects):
    scales = [P_HI - P_LO, fmpq(1)]
    stack, used = [rect0], 0
    while stack:
        rect = stack.pop()
        used += 1
        if used > max_rects:
            return False, used
        if tails_ok(rect):
            continue
        stack += split(rect, widest_relative(rect, scales))
    return True, used


def regions(delta1, eta):
    s_mid = (S_TAIL, 1 - S_TAIL)
    rect_a = ((P_LO, P_HI), (delta1, fmpq(1)))
    rect_b = ((P0_UP + eta, P_HI), (fmpq(0), delta1))
    return [("A", rect_a, rect_a + (s_mid,)), ("B", rect_b, rect_b + (s_mid,))]


def run_controls(max_boxes):
    """Two FALSE claims; the certifier must refuse both."""
    s_mid = (S_TAIL, 1 - S_TAIL)
    c1 = certify_middle(((fmpq(1233, 1000), fmpq(12336, 10000)), (fmpq(0), fmpq(1, 100)), s_mid), arb(0), max_boxes)
    print(f"CONTROL 1  g > 0 on [1.2330, 1.2336] x [0, 0.01] (Omega < 0 there; must FAIL): "
          f"{'PROVED (BAD)' if c1[0] else 'refused (good)'} ({c1[1]} boxes)", flush=True)
    c2 = certify_middle(((P_LO, fmpq(12337, 10000)), (DELTA1, fmpq(6, 100)), s_mid), arb("3e-4"), max_boxes)
    print(f"CONTROL 2  g > 3e-4 on [1.2336025, 1.2337] x [0.05, 0.06] (float min 2.93e-4; must FAIL): "
          f"{'PROVED (BAD)' if c2[0] else 'refused (good)'} ({c2[1]} boxes)", flush=True)
    return not c1[0] and not c2[0]


def md5_self():
    return hashlib.md5(open(__file__, "rb").read()).hexdigest()


def main_certify(max_boxes, controls_only, corner):
    ctx.prec = PREC_BITS
    delta1, eta = CORNERS[corner]
    print(f"# strip_bulk.py md5 {md5_self()}, prec {PREC_BITS} bits, corner '{corner}': "
          f"delta1 = {delta1}, eta = {eta}", flush=True)
    all_ok = True
    if not controls_only:
        for name, rect, box in regions(delta1, eta):
            ok_t, n_t = certify_tails(rect, 100000)
            ok_m, n_m, worst = certify_middle(box, arb(0), max_boxes)
            worst_s = f"{float(worst.lower()):.3e}" if worst is not None else "-"
            print(f"REGION {name} {[[float(a), float(b)] for a, b in rect]}: s-tails {'PROVED' if ok_t else 'NOT proved'} ({n_t} rects); "
                  f"middle s in [0.05, 0.95] {'PROVED' if ok_m else 'NOT proved'} ({n_m} boxes, smallest lower bound {worst_s})", flush=True)
            all_ok = all_ok and ok_t and ok_m
    controls_good = run_controls(20000)
    print(f"CLAIM g > 0 on REGION A u REGION B (corner '{corner}'), all s in (0,1): {'PROVED' if all_ok and not controls_only else 'NOT proved'}; "
          f"controls {'good' if controls_good else 'BAD'}")
    print(f"# md5 at end {md5_self()}")
    return all_ok and controls_good


def main_test():
    ctx.prec = PREC_BITS
    import mpmath as mp
    mp.mp.dps = 40

    def contact_kappa(p, dl):                          # route B's closed form, an independent formula
        s0, c0 = mp.sin(mp.pi / p), -mp.cos(mp.pi / p)
        C = (dl + mp.sqrt(dl ** 2 + 4 * s0 ** 2 * (1 - dl))) / (2 * s0)
        return 2 * C * s0 ** (p - 2) * c0 ** (1 - p / 2) * (C ** 2 + 1 - dl) ** (p / 2 - 1), C

    def direct_g(p, dl, s):                           # g from its definition, with route B's kappa
        kap, C = contact_kappa(p, dl)
        return (C ** p - (1 - s * dl) ** p) / (dl * (s * (1 - s)) ** (p / 2)) - kap

    def mine(p, dl, s, n=1, direction=-1):
        return g_series(*lift([arb(p), arb(dl), arb(s)], direction, n), n)

    def dec(text):
        frac = Fraction(text)
        return fmpq(frac.numerator, frac.denominator)

    for p, dl, s in [("1.25", "0.3", "0.28"), ("1.2341027", "0.01", "0.26"), ("1.26", "1", "0.5"), ("1.24", "0.11", "0.9")]:
        got = float(mine(dec(p), dec(dl), dec(s)).coeffs()[0].mid())
        want = float(direct_g(mp.mpf(p), mp.mpf(dl), mp.mpf(s)))
        assert abs(got - want) < 1e-12, (p, dl, s, got, want)
    # delta = 0: min_s g = Omega(p); Omega(5/4) = 0.01565442189276 (route A Arb + mpmath)
    p = mp.mpf(5) / 4
    s0 = mp.sin(mp.pi / p)
    A, q = (1 - s0) / (2 * s0), p / 2
    b = 1 - q + 2 * q * A
    s_star = 2 * q * A / (b + mp.sqrt(b * b + 4 * (2 * q - 1) * q * A))
    got = mine(fmpq(5, 4), fmpq(0), fmpq(int(s_star * 10 ** 15), 10 ** 15)).coeffs()[0]
    assert abs(float(got.mid()) - 0.01565442189276) < 1e-12, got
    # derivatives against central differences (series branch at delta = 0.01, direct branch at delta = 0.6)
    for pt in [(fmpq(1243, 1000), fmpq(1, 100), fmpq(3, 10)), (fmpq(1255, 1000), fmpq(6, 10), fmpq(7, 10))]:
        for k in range(3):
            der = float(coeffs_padded(mine(*pt, n=2, direction=k), 2)[1].mid())
            hh = fmpq(1, 10 ** 8)
            up = [pt[j] + (hh if j == k else 0) for j in range(3)]
            dn = [pt[j] - (hh if j == k else 0) for j in range(3)]
            fd = float(((mine(*up).coeffs()[0] - mine(*dn).coeffs()[0]) / (2 * arb(hh))).mid())
            assert abs(der - fd) < 1e-6 * (1 + abs(fd)), (pt, k, der, fd)
    # the two branches of E agree where both apply
    for v in [fmpq(1, 10), fmpq(-1, 10)]:
        vs, ps = arb_series([arb(v), 1], prec=2), arb_series([arb(fmpq(5, 4)), 1], prec=2)
        ser = coeffs_padded(e_series(vs, ps, 2), 2)
        dirc = coeffs_padded(((ps * (1 + vs).log()).exp() - 1) / vs, 2)
        assert all(abs(float((x - y).mid())) < 1e-18 for x, y in zip(ser, dirc)), (v, ser, dirc)
    # a box that must certify and a box that must not
    assert certify_middle(((fmpq(126, 100), fmpq(1261, 1000)), (fmpq(5, 10), fmpq(51, 100)), (fmpq(3, 10), fmpq(31, 100))), arb(0), 2000)[0]
    assert not certify_middle(((fmpq(1233, 1000), fmpq(12331, 10000)), (fmpq(0), fmpq(1, 1000)), (fmpq(25, 100), fmpq(27, 100))), arb(0), 300)[0]
    assert certify_tails(((P_LO, P_HI), (fmpq(0), fmpq(1, 10))), 5000)[0]
    print("tests passed")


def main():
    ap = argparse.ArgumentParser(description="Gohberg–Krupnik strip (S-b) bulk certificate [-route C]")
    ap.add_argument("--test", action="store_true")
    ap.add_argument("--controls-only", action="store_true")
    ap.add_argument("--max-boxes", type=int, default=3_000_000)
    ap.add_argument("--corner", choices=sorted(CORNERS), help="REQUIRED unless --test")
    args = ap.parse_args()
    if args.test:
        main_test()
        return 0
    if args.corner is None:
        ap.error("--corner main|reach is required")
    return 0 if main_certify(args.max_boxes, args.controls_only, args.corner) else 1


if __name__ == "__main__":
    sys.exit(main())
