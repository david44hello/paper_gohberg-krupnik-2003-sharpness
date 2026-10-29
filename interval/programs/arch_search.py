#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# arch_search.py - Gohberg–Krupnik: second-code check of route C's single-arch lower bound for ||alpha P+ + beta P-||_p 
# version 0.30 - route A 20261027_1155 ET - coarse-then-fine search (~20x cheaper, < 1 min total); m_and_argmin unused -> removed
# version 0.20 - route A 20261027_1138 ET - float search in t-chunks (memory 16 MB per array, was ~640 MB); runs go through the gate
# version 0.10 - route A 20261027_1135 ET - own float search for (t0, y_k), then S = sum w_k Gamma_C(y_k, t_k) in mpmath iv
#
# Arch argument (checked by hand, route A 11:36): c = q-sinusoidal tent with values 0, 1, 0 at t0, t0 + d, t0 + 2d (d < pi/q), zero
# elsewhere; c >= 0, and c'' + q^2 c = sum_k w_k delta_{t_k}, w = (q/sin qd, -2q cot qd, q/sin qd). For q-subtrigonometric phi,
# sum_k w_k phi(t_k) = int c d(phi'' + q^2 phi) >= 0. If all w_k >= 0 (qd >= pi/2) and phi <= m_C <= Gamma_C(y_k, t_k), then
# S := sum_k w_k Gamma_C(y_k, t_k) < 0 rules phi out, so the norm is > C (Theorem R, C > max(|alpha|, |beta|)).
# Inputs: exact rationals (t0, y_k, alpha, beta, C); pi and the weights are enclosed by iv; only "S.b < 0" is tested.
# usage: python arch_search.py --test | --run
import sys
from fractions import Fraction
import numpy as np
import mpmath
from mpmath import iv

iv.dps = 40
ARCH_STRETCH = Fraction(1001, 1000)  # 2d = (pi/q) * 1.001, as route C: then qd > pi/2 and all three weights are > 0
Y_GRID = np.linspace(-8, 8, 801)      # coarse search grid
Y_FINE = np.linspace(-8, 8, 16001)    # fine grid, used only near the coarse best t0
T_GRID = 2000
FINE_T = 200
T_CHUNK = 200        # 200 x 16001 doubles = 26 MB per array (the 11:36 test without chunks took ~640 MB: never again)


def gamma_float(cc, p, alpha, beta, y, t):
    q = p / 2
    base_f = 2 * np.cosh(y) + 2 * np.cos(t)
    base_g = abs(alpha) ** 2 * np.exp(y) + abs(beta) ** 2 * np.exp(-y) + 2 * np.real(alpha * np.conj(beta) * np.exp(1j * t))
    return cc ** p * np.maximum(base_f, 0) ** q - np.maximum(base_g, 0) ** q


def best_on_grid(cc, p, alpha, beta, t0s, y_grid, w, d):
    """min over the given t0s of sum_k w_k min_y Gamma(y, t0 + k d) (y on y_grid, t0s in chunks of T_CHUNK)."""
    best = (np.inf, None, None)
    for start in range(0, len(t0s), T_CHUNK):
        chunk = t0s[start:start + T_CHUNK]
        total = np.zeros(len(chunk))
        ys = []
        for k in range(3):
            vals = gamma_float(cc, p, alpha, beta, y_grid[None, :], (chunk + k * d)[:, None])
            k_best = np.argmin(vals, axis=1)
            total += w[k] * vals[np.arange(len(chunk)), k_best]
            ys.append(y_grid[k_best])
        i_best = int(np.argmin(total))
        if total[i_best] < best[0]:
            best = (total[i_best], chunk[i_best], [ys[k][i_best] for k in range(3)])
    return best


def search_arch(cc, p, alpha, beta):
    """Own search: t0 minimising sum_k w_k m_C(t_k); coarse t/y grid, then a fine grid near the coarse best. Returns t0, the
    three y minimisers and the float value of the sum (a search only: the certificate does not depend on its accuracy)."""
    q = p / 2
    d = float(ARCH_STRETCH) * np.pi / q / 2
    w = np.array([q / np.sin(q * d), -2 * q / np.tan(q * d), q / np.sin(q * d)])
    coarse_t = np.linspace(-np.pi, np.pi, T_GRID, endpoint=False)
    _, t_c, _ = best_on_grid(cc, p, alpha, beta, coarse_t, Y_GRID, w, d)
    step = 2 * np.pi / T_GRID
    fine_t = np.linspace(t_c - 2 * step, t_c + 2 * step, FINE_T)
    value, t_f, ys = best_on_grid(cc, p, alpha, beta, fine_t, Y_FINE, w, d)
    return t_f, ys, value


def to_iv(x):
    return iv.mpf(x) if not isinstance(x, Fraction) else iv.mpf(x.numerator) / x.denominator


def gamma_iv(cc, p, alpha, beta, y, t):
    """Gamma_C(y, t) in interval arithmetic; alpha, beta = (re, im) pairs of Fractions; y, t intervals."""
    q = to_iv(p) / 2
    ey, emy = iv.exp(y), iv.exp(-y)
    base_f = ey + emy + 2 * iv.cos(t)
    a_re, a_im = (to_iv(v) for v in alpha)
    b_re, b_im = (to_iv(v) for v in beta)
    ab_re, ab_im = a_re * b_re + a_im * b_im, a_im * b_re - a_re * b_im          # alpha * conj(beta)
    base_g = (a_re ** 2 + a_im ** 2) * ey + (b_re ** 2 + b_im ** 2) * emy + 2 * (ab_re * iv.cos(t) - ab_im * iv.sin(t))
    if base_f.a <= 0 or base_g.a <= 0:
        raise RuntimeError("a base of a power is not provably positive; choose other y_k")
    return to_iv(cc) ** to_iv(p) * base_f ** q - base_g ** q


def certify(cc, p, alpha, beta, t0, ys):
    """Returns the interval S = sum_k w_k Gamma_C(y_k, t_k); t0, ys exact rationals; d = (pi/q) * 1.001 / 2 enclosed."""
    q = to_iv(p) / 2
    d = to_iv(ARCH_STRETCH) * iv.pi / q / 2
    if not (q * d).a > iv.pi.b / 2:
        raise RuntimeError("q d not provably > pi/2: a weight may be negative")
    w = [q / iv.sin(q * d), -2 * q * iv.cos(q * d) / iv.sin(q * d), q / iv.sin(q * d)]
    if not all(wk.a > 0 for wk in w):
        raise RuntimeError("a weight is not provably positive")
    total = iv.mpf(0)
    for k in range(3):
        total += w[k] * gamma_iv(cc, p, alpha, beta, to_iv(ys[k]), to_iv(t0) + k * d)
    return total


def rational(x, den=10 ** 6):
    return Fraction(round(x * den), den)


def check_point(label, cc, p, alpha_pair, beta_pair):
    """Own float search, rationalised inputs, iv evaluation of S; prints PROVED (S.b < 0) or NOT PROVED."""
    alpha = complex(float(alpha_pair[0]), float(alpha_pair[1]))
    beta = complex(float(beta_pair[0]), float(beta_pair[1]))
    if not cc > max(abs(alpha), abs(beta)):
        raise RuntimeError("Theorem R needs C > max(|alpha|, |beta|)")
    t0, ys, s_float = search_arch(float(cc), float(p), alpha, beta)
    t0_r, ys_r = rational(t0), [rational(y) for y in ys]
    s_iv = certify(cc, p, alpha_pair, beta_pair, t0_r, ys_r)
    verdict = "PROVED norm > C" if s_iv.b < 0 else "NOT PROVED"
    print(f"{label}: p={p} alpha={alpha} beta={beta} C={cc}: t0={t0_r} y={[str(y) for y in ys_r]} S_float={s_float:.6f}"
          f" S_iv=[{mpmath.nstr(s_iv.a, 8)}, {mpmath.nstr(s_iv.b, 8)}] -> {verdict}", flush=True)
    return s_iv.b < 0


def run_tests():
    """Controls: P+ at p = 3 (norm csc(pi/3) = 1.1547): C = 1.15 must be PROVED, C = 1.16 must NOT be (true norm is below)."""
    zero, one = (Fraction(0), Fraction(0)), (Fraction(1), Fraction(0))
    assert check_point("CTRL P+ ", Fraction(115, 100), 3, one, zero), "P+ at C = 1.15 should be proved"
    assert not check_point("CTRL P+ ", Fraction(116, 100), 3, one, zero), "P+ at C = 1.16 must NOT be proved (norm 1.1547)"
    print("tests: P+ control proved below its norm and not above - PASS")


def main_arch_check():
    one = (Fraction(1), Fraction(0))
    beta = (Fraction(2, 5), Fraction(3, 10))
    for cc in (Fraction(128, 100), Fraction(1284, 1000), Fraction(1285, 1000), Fraction(129, 100)):
        check_point("reference point", cc, 4, one, beta)


def main():
    if "--test" in sys.argv:
        run_tests()
    elif "--run" in sys.argv:
        main_arch_check()
    else:
        raise SystemExit("usage: arch_search.py --test | --run")


if __name__ == "__main__":
    main()
