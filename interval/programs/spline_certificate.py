#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# spline_certificate.py - Gohberg–Krupnik (A) T2: rigorous Arb check of a "norm > C" certificate for ||alpha P+ + beta P-||_p 
## version 0.10 - route C 20261027_1135 ET - q-trig spline certificate (kinks t_k, values c_k >= 0, points y_k); exact rational input
# THEOREM USED (route A 11:22: norm <= C <=> some q-subtrigonometric phi <= m_C, q = p/2, m_C(t) = inf_y Gamma_C(y, t)).
# Let c >= 0 be the 2pi-periodic spline that is q-trigonometric (c'' + q^2 c = 0) between consecutive kinks t_k, with c(t_k) = c_k;
# then nu = c'' + q^2 c = sum_k w_k delta_{t_k}, w_k = derivative jump of c at t_k. If every w_k >= 0, then for every q-subtrig phi,
# sum_k w_k phi(t_k) = <phi'' + q^2 phi, c> >= 0 (c >= 0). With phi <= m_C <= Gamma_C(y_k, t_k), the check
#   S := sum_k w_k Gamma_C(y_k, t_k) < 0
# shows that no such phi exists, hence ||alpha P+ + beta P-||_p > C.
# Gamma_C(y, t) = C^p (2 cosh y + 2 cos t)^q - (|alpha|^2 e^y + |beta|^2 e^-y + 2 Re(alpha conj(beta) e^{it}))^q.
# c >= 0 on an arc with a positive end needs 0 < q*gap < pi (then the arc is a positive combination of two positive sines);
# an arc with both ends 0 is c = 0 and contributes nothing.
import argparse
import json
import sys
from fractions import Fraction
from flint import arb, acb, ctx

PREC_BITS = 256


def arb_of(text):
    fr = Fraction(text)
    return arb(fr.numerator) / arb(fr.denominator)


def require(cond, msg):
    if not cond:
        raise SystemExit(f"CERTIFICATE REJECTED: {msg}")


def gamma_c(C, p, alpha, beta, y, t):
    q = p / 2
    base1 = 2 * y.cosh() + 2 * t.cos()
    cross = (alpha * beta.conjugate() * acb(t.cos(), t.sin())).real
    base2 = abs(alpha) ** 2 * y.exp() + abs(beta) ** 2 * (-y).exp() + 2 * cross
    require(base1 > 0 and base2 > 0, f"a base is not certified positive at y = {y}, t = {t}")
    return C ** p * base1 ** q - base2 ** q


def gaps(ts):
    two_pi = 2 * arb.pi()
    out = [ts[k + 1] - ts[k] for k in range(len(ts) - 1)]
    out.append(ts[0] + two_pi - ts[-1])
    return out


def arc_terms(q, c_left, c_right, gap):
    """Contribution of one arc to the jumps at its left and right kinks: (right-derivative at left end, left-derivative at right end)."""
    if c_left == 0 and c_right == 0:
        return arb(0), arb(0)
    s = (q * gap).sin()
    require(q * gap > 0 and q * gap < arb.pi(), f"arc with a positive end has q*gap not in (0, pi): {q * gap}")
    cs = (q * gap).cos()
    d_left = q * (c_right - c_left * cs) / s      # c'(t_k+)
    d_right = -q * (c_left - c_right * cs) / s    # c'(t_{k+1}-)
    return d_left, d_right


def jump_weights(q, ts, cs):
    K = len(ts)
    gs = gaps(ts)
    right_of = [None] * K   # c'(t_k+)
    left_of = [None] * K    # c'(t_k-)
    for k in range(K):
        d_left, d_right = arc_terms(q, cs[k], cs[(k + 1) % K], gs[k])
        right_of[k] = d_left
        left_of[(k + 1) % K] = d_right
    return [right_of[k] - left_of[k] for k in range(K)]


def check_certificate(cert):
    ctx.prec = PREC_BITS
    p = arb_of(cert["p"])
    q = p / 2
    alpha = acb(arb_of(cert["alpha"][0]), arb_of(cert["alpha"][1]))
    beta = acb(arb_of(cert["beta"][0]), arb_of(cert["beta"][1]))
    C = arb_of(cert["C"])
    nodes = cert["nodes"]
    ts = [arb_of(nd["t"]) for nd in nodes]
    cs = [Fraction(nd["c"]) for nd in nodes]
    require(all(cc >= 0 for cc in cs), "some c_k < 0")
    require(all(Fraction(nodes[k]["t"]) < Fraction(nodes[k + 1]["t"]) for k in range(len(nodes) - 1)), "kinks not increasing")
    require(ts[-1] - ts[0] < 2 * arb.pi(), "kinks span more than one period")
    ws = jump_weights(q, ts, [arb_of(nd["c"]) for nd in nodes])
    total = arb(0)
    for k, nd in enumerate(nodes):
        require(ws[k] >= 0, f"jump weight w_{k} = {ws[k]} not certified >= 0 (t = {nd['t']})")
        if cs[k] == 0 and ws[k] == 0:
            continue
        total += ws[k] * gamma_c(C, p, alpha, beta, arb_of(nd["y"]), ts[k])
    return total, ws


def main_check(path):
    cert = json.loads(open(path).read())
    total, ws = check_certificate(cert)
    print(f"certificate {path}: p = {cert['p']}, alpha = {cert['alpha']}, beta = {cert['beta']}, C = {cert['C']}, {len(ws)} kinks")
    print(f"  S = sum w_k Gamma_C(y_k, t_k) = {total}")
    if total < 0:
        print(f"  PROVED: ||alpha P+ + beta P-||_p > C = {float(Fraction(cert['C'])):.10f}")
        return 0
    print("  NOT PROVED (S not certified < 0)")
    return 1


def main_test():
    """Single arch, slightly longer than pi/q, around route C's 11:20 gap case, plus negative controls."""
    import math
    print("--test: build certificates by hand and check sign behaviour")
    results = []
    # control 1: beta = 0 (P+), p = 3: norm = csc(pi/3) = 1.1547005; C below must be PROVABLE by some arch, C above NOT.
    for C, expect in [("1.15", True), ("1.16", False)]:
        cert = arch_cert("3", ("1", "0"), ("0", "0"), C)
        total, _ = check_certificate(cert)
        ok = (total < 0) == expect
        results.append(ok)
        print(f"  P+ p=3 C={C}: S = {total.mid()}  expected {'PROVED' if expect else 'not proved'} -> {'ok' if ok else 'FAIL'}")
    if not all(results):
        raise SystemExit("TEST FAILED")
    print("tests done")
    return 0


def arch_cert(p_text, alpha, beta, C_text):
    """Three-kink arch (0, 1, 0) of total length slightly more than pi/q, best placement found by a float scan."""
    import math
    import numpy as np
    p = float(Fraction(p_text))
    q = p / 2
    al = complex(float(Fraction(alpha[0])), float(Fraction(alpha[1])))
    be = complex(float(Fraction(beta[0])), float(Fraction(beta[1])))
    C = float(Fraction(C_text))
    d = (math.pi / q) / 2 * (1 + 1e-3)
    ys = np.linspace(-30, 30, 6001)

    def gam(y, t):
        b1 = np.maximum(2 * np.cosh(y) + 2 * np.cos(t), 0)
        b2 = np.maximum(abs(al) ** 2 * np.exp(y) + abs(be) ** 2 * np.exp(-y) + 2 * (al * np.conj(be) * np.exp(1j * t)).real, 0)
        return C ** p * b1 ** q - b2 ** q

    def best_y(t):
        vals = gam(ys, t)
        return ys[int(np.argmin(vals))], vals.min()

    w_end = q / math.sin(q * d)
    w_mid = -2 * q * math.cos(q * d) / math.sin(q * d)
    best = None
    for t0 in np.linspace(-math.pi, math.pi, 2001):
        pts = [t0, t0 + d, t0 + 2 * d]
        mins = [best_y(t) for t in pts]
        val = w_end * mins[0][1] + w_mid * mins[1][1] + w_end * mins[2][1]
        if best is None or val < best[0]:
            best = (val, pts, [mm[0] for mm in mins])
    _, pts, yb = best
    fr = lambda x: str(Fraction(x).limit_denominator(10 ** 9))
    return {"p": p_text, "alpha": list(alpha), "beta": list(beta), "C": C_text,
            "nodes": [{"t": fr(pts[0]), "c": "0", "y": fr(yb[0])}, {"t": fr(pts[1]), "c": "1", "y": fr(yb[1])},
                      {"t": fr(pts[2]), "c": "0", "y": fr(yb[2])}]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cert", help="JSON certificate to check")
    ap.add_argument("--test", action="store_true")
    args = ap.parse_args()
    if args.test:
        sys.exit(main_test())
    if not args.cert:
        raise SystemExit("give --cert FILE or --test")
    sys.exit(main_check(args.cert))


if __name__ == "__main__":
    main()
