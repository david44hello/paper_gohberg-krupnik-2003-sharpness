#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
# strip_bulk_independent.py - Gohberg–Krupnik strip (S-b), SECOND independent code: g > 0 off the corner, rigorous (Arb) 
## version 0.20 - route A 20261028_0207 ET - a ValueError of a ball evaluation (series division by a ball meeting 0 on a wide box) = "not certified", split
## version 0.10 - route A 20261028_0130 ET - F-form F = g (s(1-s))^q; closed-form kappa; rationalized (C-1)/delta; own series tails
"""
CLAIM ('reach' split; with either corner code this closes the strip p_0 <= p <= 1.268, 0 < delta <= 1):
  F(delta, p, s) := T1 + S - kappa P > 0 for every s in (0, 1) on
    REGION A' = [1.2336025, 1.268] x [1/100, 1]  and  REGION B' = [1.2337027, 1.268] x [0, 1/100]   (p x delta), where
  T1 = (C^p - 1)/delta, S = s phi(s delta) = (1 - (1 - s delta)^p)/delta, P = (s(1-s))^q, q = p/2,
  kappa = K/delta = 2 C s0^{p-2} c0^{1-q} (C^2 + 1 - delta)^{q-1}, C = delta/(2 s0) + sqrt(delta^2/(4 s0^2) + 1 - delta),
  s0 = sin(pi/p), c0 = -cos(pi/p).  F = g (s(1-s))^q with g of the lampos note Sec. 8, so F > 0 <=> g > 0.
NO 0/0: (C - 1)/delta = w := 1/(2 s0) + (delta/(4 s0^2) - 1)/(1 + sqrt(delta^2/(4 s0^2) + 1 - delta))  (rationalized root), and
  T1 = w E(delta w), S = s E(-s delta), with E(u) := ((1+u)^p - 1)/u = sum_{k>=1} b_k u^{k-1}, b_k = binom(p, k).
  E on a ball: |u| <= 1/8: N_TERMS terms plus a tail ball (see tail_constant); |u| >= 1/20 on the whole ball: (exp(p log(1+u)) - 1)/u;
  otherwise the box is split.
ENDS in s: s <= 1/20: F >= T1 - kappa (19/400)^q (S >= 0; s(1-s) increases on [0, 1/2]);
  s >= 19/20: F >= T1 + 19/20 - kappa (19/400)^q (S = s phi(s delta) >= s, as phi >= 1 by (1-x)^p <= 1-x).
MIDDLE s in [1/20, 19/20]: mean value form on 3-D boxes, F >= F(mid) - sum_k sup_box |d_k F| h_k, where d_k F is coefficient 1 of a
  length-2 arb_series in coordinate k with the other coordinates as full balls. The coordinate with the largest term is bisected.
CONTROLS (false claims, must be refused): (c1) the claim on [1.2336020, 1.2336025] x [0, 1/1000] (p < p_0, so Omega < 0 there);
  (c2) kappa inflated by 1 + 10^-4 on [1.2336025, 1.2337] x [1/100, 2/100] (true margin there ~ 4e-6 < 8e-5).
"""
import argparse
import hashlib
import random
import sys

import flint
import mpmath as mp
from flint import arb, arb_series, fmpq

PREC_BITS = 128
P_LO_A, P_LO_B, P_HI = fmpq(12336025, 10 ** 7), fmpq(12337027, 10 ** 7), fmpq(1268, 1000)
D_SPLIT = fmpq(1, 100)
S_EDGE = fmpq(1, 20)
N_TERMS = 40
R_SERIES, R_CLOSED = fmpq(1, 8), fmpq(1, 20)
P_TAIL_RANGE = (fmpq(6, 5), fmpq(13, 10))
MIN_HALF = fmpq(1, 10 ** 10)
MAX_BOXES = 2000000
CONTROL_BOXES = 20000
KAPPA_INFLATE = 1 + fmpq(1, 10 ** 4)


def tail_constant():
    """sum_{k > N} k(k+6) r^{k-2}, r = 1/8: bounds the value tail (|b_k| <= 1), the u-derivative tail ((k-1)|b_k|) and the
    p-derivative tail (|d b_k/dp| <= k + 6) of E for 6/5 <= p <= 13/10 and |u| <= r.  Successive terms have ratio <= ratio below."""
    nn, rr = N_TERMS, arb(R_SERIES)
    first = arb((nn + 1) * (nn + 7)) * rr ** (nn - 1)
    ratio = arb((nn + 2) * (nn + 8)) / arb((nn + 1) * (nn + 7)) * rr
    return first / (1 - ratio)


def hull(lo, hi):
    return arb(lo).union(arb(hi))


def const(ball):
    return arb_series([ball], prec=2)


def coeffs2(series):
    cc = series.coeffs()
    return cc + [arb(0)] * (2 - len(cc))


def binomials(p):
    b_k, out = p, [p]
    for kk in range(1, N_TERMS):
        b_k = b_k * (p - kk) / (kk + 1)
        out.append(b_k)
    return out


def e_series(u, p, binoms, tail):
    total = binoms[-1]
    for b_k in reversed(binoms[:-1]):
        total = total * u + b_k
    c_tot, c_u, c_p = coeffs2(total), coeffs2(u), coeffs2(p)
    return arb_series([c_tot[0] + arb(0, tail), c_tot[1] + arb(0, tail * (abs(c_u[1]) + abs(c_p[1])).upper())], prec=2)


def e_quot(u, p, binoms, tail):
    """E(u) = ((1+u)^p - 1)/u as a length-2 series, or None when the u-ball is neither small nor away from 0."""
    u0 = coeffs2(u)[0]
    if abs(u0).upper() <= arb(R_SERIES):
        return e_series(u, p, binoms, tail)
    if u0 >= arb(R_CLOSED) or u0 <= -arb(R_CLOSED):
        return ((p * (1 + u).log()).exp() - 1) / u
    return None


def angle_parts(p):
    inv = 1 / p
    s0, c0 = inv.sin_pi(), -inv.cos_pi()
    k0 = ((p - 2) * s0.log() + (1 - p / 2) * c0.log()).exp()
    return s0, k0


def t1_kappa(delta, p, binoms, tail):
    s0, k0 = angle_parts(p)
    root = (delta * delta / (4 * s0 * s0) + 1 - delta).sqrt()
    cc = delta / (2 * s0) + root
    ww = 1 / (2 * s0) + (delta / (4 * s0 * s0) - 1) / (1 + root)
    e_u = e_quot(delta * ww, p, binoms, tail)
    kappa = 2 * cc * k0 * ((p / 2 - 1) * (cc * cc + 1 - delta).log()).exp()
    return (None if e_u is None else ww * e_u), kappa


def f_value(delta, p, s, kappa_mult, tail):
    """F = T1 + S - kappa_mult kappa (s(1-s))^q for length-2 series arguments; None if the box needs a split
    (a quotient branch is undecided, or a series division meets a ball containing 0: never an acceptance)."""
    try:
        binoms = binomials(p)
        t1, kappa = t1_kappa(delta, p, binoms, tail)
        e_s = e_quot(-s * delta, p, binoms, tail)
        if t1 is None or e_s is None:
            return None
        return t1 + s * e_s - arb(kappa_mult) * kappa * ((p / 2) * (s * (1 - s)).log()).exp()
    except ValueError:
        return None


def box_lower(box, kappa_mult, tail):
    """(lower bound of F on the box or None, per-coordinate losses, F(mid) upper end)."""
    balls = [hull(lo, hi) for lo, hi in box]
    mids = [const(arb((lo + hi) / 2)) for lo, hi in box]
    f_mid = f_value(*mids, kappa_mult, tail)
    if f_mid is None:
        return None, None, None
    lower, losses = coeffs2(f_mid)[0], []
    for kk in range(3):
        args = [const(bb) for bb in balls]
        args[kk] = arb_series([balls[kk], 1], prec=2)
        val = f_value(*args, kappa_mult, tail)
        if val is None:
            return None, None, coeffs2(f_mid)[0].upper()
        loss = abs(coeffs2(val)[1]).upper() * arb((box[kk][1] - box[kk][0]) / 2)
        losses.append(loss)
        lower = lower - loss
    return lower, losses, coeffs2(f_mid)[0].upper()


def split_box(box, kk):
    lo, hi = box[kk]
    mid = (lo + hi) / 2
    left, right = list(box), list(box)
    left[kk], right[kk] = (lo, mid), (mid, hi)
    return [tuple(left), tuple(right)]


def choose_split(box, losses):
    if losses is not None and all(loss.is_finite() for loss in losses):
        return max(range(3), key=lambda kk: float(losses[kk].mid()))
    return 0 if (box[0][1] - box[0][0]) >= (box[2][1] - box[2][0]) else 2


def certify_middle(region, kappa_mult, tail, max_boxes):
    """Region = ((d_lo, d_hi), (p_lo, p_hi)); boxes (delta, p, s). Returns (verdict, stats)."""
    stack = [(region[0], region[1], (S_EDGE, 1 - S_EDGE))]
    stats = {"boxes": 0, "accepted": 0, "min_lower": None}
    while stack:
        box = stack.pop()
        stats["boxes"] += 1
        if stats["boxes"] > max_boxes:
            return "REFUSED (box budget)", stats
        lower, losses, f_mid_up = box_lower(box, kappa_mult, tail)
        if f_mid_up is not None and f_mid_up < 0:
            stats["witness"] = [str(lo) + ".." + str(hi) for lo, hi in box]
            return "FALSE (F(mid) < 0 at an exact point)", stats
        if lower is not None and lower > 0:
            stats["accepted"] += 1
            low = float(lower.lower().mid())
            stats["min_lower"] = low if stats["min_lower"] is None else min(stats["min_lower"], low)
            continue
        kk = choose_split(box, losses)
        if (box[kk][1] - box[kk][0]) / 2 < MIN_HALF:
            stats["witness"] = [str(lo) + ".." + str(hi) for lo, hi in box]
            return "REFUSED (box too small)", stats
        stack += split_box(box, kk)
    return "PROVED", stats


def ends_lower(d_box, p_box, kappa_mult, tail):
    delta, p = const(hull(*d_box)), const(hull(*p_box))
    try:
        t1, kappa = t1_kappa(delta, p, binomials(p), tail)
    except ValueError:
        return None
    if t1 is None:
        return None
    edge_cap = ((p / 2) * arb(S_EDGE * (1 - S_EDGE)).log()).exp()
    low = coeffs2(t1 - arb(kappa_mult) * kappa * edge_cap)[0]
    high = coeffs2(t1 + arb(1 - S_EDGE) - arb(kappa_mult) * kappa * edge_cap)[0]
    return low, high


def certify_ends(region, kappa_mult, tail, max_boxes):
    stack, stats = [region], {"rects": 0, "min_low": None, "min_high": None}
    while stack:
        d_box, p_box = stack.pop()
        stats["rects"] += 1
        if stats["rects"] > max_boxes:
            return "REFUSED (rect budget)", stats
        ends = ends_lower(d_box, p_box, kappa_mult, tail)
        if ends is not None and ends[0] > 0 and ends[1] > 0:
            for key, val in (("min_low", ends[0]), ("min_high", ends[1])):
                low = float(val.lower().mid())
                stats[key] = low if stats[key] is None else min(stats[key], low)
            continue
        d_half, p_half = (d_box[1] - d_box[0]) / 2, (p_box[1] - p_box[0]) / 2
        if max(d_half, p_half) < MIN_HALF:
            return "REFUSED (rect too small)", stats
        if d_half >= 100 * p_half:
            mid = (d_box[0] + d_box[1]) / 2
            stack += [((d_box[0], mid), p_box), ((mid, d_box[1]), p_box)]
        else:
            mid = (p_box[0] + p_box[1]) / 2
            stack += [(d_box, (p_box[0], mid)), (d_box, (mid, p_box[1]))]
    return "PROVED", stats


def regions():
    return {"A'": ((D_SPLIT, fmpq(1)), (P_LO_A, P_HI)), "B'": ((fmpq(0), D_SPLIT), (P_LO_B, P_HI))}


def check_p_range(region):
    if not (P_TAIL_RANGE[0] <= region[1][0] and region[1][1] <= P_TAIL_RANGE[1]):
        raise SystemExit(f"p range {region[1]} outside the tail-bound range {P_TAIL_RANGE}")


def run_region(name, region, kappa_mult, tail, max_boxes):
    check_p_range(region)
    ends_verdict, ends_stats = certify_ends(region, kappa_mult, tail, max_boxes)
    print(f"REGION {name} p [{region[1][0]}, {region[1][1]}] x delta [{region[0][0]}, {region[0][1]}]: ends {ends_verdict} {ends_stats}",
          flush=True)
    mid_verdict, mid_stats = certify_middle(region, kappa_mult, tail, max_boxes)
    print(f"REGION {name} middle s in [1/20, 19/20]: {mid_verdict} {mid_stats}", flush=True)
    return ends_verdict == "PROVED" and mid_verdict == "PROVED"


def main_certify(tail):
    results = [run_region(name, region, 1, tail, MAX_BOXES) for name, region in regions().items()]
    verdict = all(results)
    print(f"CLAIM F > 0 (so g > 0) on A' u B', all s in (0, 1): {'PROVED' if verdict else 'NOT PROVED'}")
    return verdict


def main_control(mode, tail):
    if mode == "control_c1":
        region, mult = ((fmpq(0), fmpq(1, 1000)), (fmpq(12336020, 10 ** 7), P_LO_A)), 1
    else:
        region, mult = ((D_SPLIT, fmpq(2, 100)), (P_LO_A, fmpq(12337, 10 ** 4))), KAPPA_INFLATE
    good = not run_region(mode, region, mult, tail, CONTROL_BOXES)
    print(f"CONTROL {mode}: {'REFUSED (good)' if good else 'PROVED (BAD)'}")
    return good


def mp_f(delta, p, s):
    q, s0, c0 = p / 2, mp.sin(mp.pi / p), -mp.cos(mp.pi / p)
    if delta == 0:
        aa = (1 - s0) / (2 * s0)
        return p * (aa + s) - 2 ** q * s0 ** (p - 2) * c0 ** (1 - q) * (s * (1 - s)) ** q
    cc = delta / (2 * s0) + mp.sqrt(delta ** 2 / (4 * s0 ** 2) + 1 - delta)
    kappa = 2 * cc * s0 ** (p - 2) * c0 ** (1 - q) * (cc ** 2 + 1 - delta) ** (q - 1)
    return (cc ** p - (1 - s * delta) ** p) / delta - kappa * (s * (1 - s)) ** q


def to_arb(value):
    return arb(mp.nstr(value, 45))


def run_tests(tail):
    mp.mp.dps = 50
    rng, ok = random.Random(2028), True
    worst = 0.0
    for _ in range(40):
        pt = [mp.mpf(rng.choice([0, 0.003, 0.2, 0.7, 1.0]) * rng.random()), mp.mpf(1.2336 + 0.0344 * rng.random()),
              mp.mpf(0.05 + 0.9 * rng.random())]
        val = coeffs2(f_value(*[const(to_arb(xx)) for xx in pt], 1, tail))[0]
        ref = mp_f(*pt)
        ok = ok and val.contains(to_arb(ref)) if abs(ref) > mp.mpf('1e-40') else ok
        worst = max(worst, float(val.rad()))
    print(f"TEST (1) F ball contains the mpmath value at 40 random points (delta in [0, 1] incl. 0): {ok}; max radius {worst:.2e}")
    ok_d = True
    for pt in [(mp.mpf('0.004'), mp.mpf('1.24'), mp.mpf('0.26')), (mp.mpf('0.5'), mp.mpf('1.26'), mp.mpf('0.7'))]:
        for kk in range(3):
            args = [const(to_arb(xx)) for xx in pt]
            args[kk] = arb_series([to_arb(pt[kk]), 1], prec=2)
            der = coeffs2(f_value(*args, 1, tail))[1]
            num = mp.diff(lambda xx: mp_f(*[xx if jj == kk else pt[jj] for jj in range(3)]), pt[kk])
            ok_d = ok_d and abs(der - to_arb(num)) < arb("1e-20")
    print(f"TEST (2) coefficient-1 derivatives = mpmath numerical derivatives (2 points x 3 coordinates, 1e-20): {ok_d}")
    p = const(arb("1.25"))
    binoms = binomials(p)
    ok_e = True
    for uu in ["0.1", "-0.1", "0.06", "-0.06"]:
        u = const(arb(uu))
        diff = coeffs2(e_series(u, p, binoms, tail))[0] - coeffs2(((p * (1 + u).log()).exp() - 1) / u)[0]
        ok_e = ok_e and abs(diff) < arb("1e-25")
    print(f"TEST (3) E: series branch = closed branch at u = +-0.1, +-0.06 (1e-25): {ok_e}; tail constant {tail.str(3)}")
    return ok and ok_d and ok_e


def md5_self():
    return hashlib.md5(open(__file__, "rb").read()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--mode", choices=["test", "control_c1", "control_c2", "certify"], required=True)
    args = parser.parse_args()
    flint.ctx.prec = PREC_BITS
    print(f"# strip_bulk_independent.py md5 {md5_self()} prec {PREC_BITS} mode {args.mode}", flush=True)
    tail = tail_constant()
    if args.mode == "test":
        good = run_tests(tail)
    elif args.mode == "certify":
        good = main_certify(tail)
    else:
        good = main_control(args.mode, tail)
    print(f"# md5 at end {md5_self()}")
    sys.exit(0 if good else 1)


if __name__ == "__main__":
    main()
