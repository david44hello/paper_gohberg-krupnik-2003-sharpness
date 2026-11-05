#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
# pencil_search.py - Gohberg–Krupnik: independent LP for ||alpha P+ + beta P-||_p (= aI + bH, complex a, b) 
# version 0.20 - route A 20261027_1552 ET - sweep bracket: lower end kept above max(|alpha|, |beta|) (v0.10 crashed at p = 3, lam = 0.9)
# version 0.10 - route A 20261027_1135 ET - from my 018 earlier_projection_search.py v0.20: t over the FULL circle, y over all of R (no symmetry)
#
# Method (NOTE_reduction_pencil_route A.md, Theorem R): for C > max(|alpha|, |beta|), ||alpha P+ + beta P-||_p <= C iff a 2pi-periodic
# q-subtrigonometric phi <= m_C exists, q = p/2, m_C(t) = min_y Gamma_C(y, t),
#   Gamma_C(y, t) = C^p (2 cosh y + 2 cos t)^q - (|alpha|^2 e^y + |beta|^2 e^-y + 2 Re(alpha conj(beta) e^{it}))^q.
# Discretisation on t_i = -pi + i h, h = 2 pi/N: node jumps J_i = q (phi_{i+1} + phi_{i-1} - 2 cos(qh) phi_i)/sin(qh) >= 0. The node
# problem is a RELAXATION (phi <= m only at nodes), so C*_N <= the norm, nondecreasing along nested grids (built-in bug test).
# Phase I: sigma*(C) = min sigma s.t. J_i/h >= -sigma (density units), phi_i <= m_C(t_i); feasible iff sigma* <= SIGMA_TOL.
# FLOAT ONLY (numpy + HiGHS): a pointer to the truth, not a certificate.
# usage: python pencil_search.py --test | --run   (--run: put behind a resource scheduler)
import sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix, hstack, csr_matrix

Y_MAX = 12.0         # Gamma -> +oo as |y| -> oo (Lemma 0); the argmin is checked to stay inside (-Y_MAX, Y_MAX)
Y_COARSE = 2401      # coarse y grid on [-Y_MAX, Y_MAX] before the golden-section refinement
GOLDEN_STEPS = 60    # interval shrinks by 0.618^60 ~ 3e-13
SIGMA_TOL = 1e-9     # feasible <=> sigma* <= SIGMA_TOL (density units)
C_REL_WIDTH = 1e-9   # bisection stops at this relative bracket width
T_CHUNK = 1000       # t-points per vectorised chunk (memory: 1000 x 2401 doubles = 19 MB)
BRACKET_MARGIN = 1e-3  # sweep lower end >= (1 + this) max(|alpha|, |beta|): below that m_C = -oo (argmin leaves the y-grid)
DS_RETRIES = []      # N of every LP re-solved by dual simplex after an IPM error (printed at the end)


def gamma_c(cc, p, alpha, beta, y, t):
    """Gamma_C(y, t) for the pencil alpha P+ + beta P-; y, t broadcast."""
    q = p / 2
    base_f = np.maximum(2 * np.cosh(y) + 2 * np.cos(t), 0.0)
    cross = 2 * np.real(alpha * np.conj(beta) * np.exp(1j * t))
    base_g = np.maximum(abs(alpha) ** 2 * np.exp(y) + abs(beta) ** 2 * np.exp(-y) + cross, 0.0)
    return cc ** p * base_f ** q - base_g ** q


def golden_refine(func, lo, hi):
    """Vectorised golden-section minimisation of func on [lo, hi] (arrays); returns the minimum values."""
    ratio = (np.sqrt(5) - 1) / 2
    for _ in range(GOLDEN_STEPS):
        left, right = hi - ratio * (hi - lo), lo + ratio * (hi - lo)
        go_left = func(left) < func(right)
        hi = np.where(go_left, right, hi)
        lo = np.where(go_left, lo, left)
    return func((lo + hi) / 2)


def m_c_chunk(cc, p, alpha, beta, t_chunk):
    """min over y in R of Gamma_C for each t in t_chunk: coarse grid on [-Y_MAX, Y_MAX], then golden refinement."""
    y_grid = np.linspace(-Y_MAX, Y_MAX, Y_COARSE)
    step = y_grid[1] - y_grid[0]
    values = gamma_c(cc, p, alpha, beta, y_grid[None, :], t_chunk[:, None])
    k_best = np.argmin(values, axis=1)
    if np.any(k_best <= 1) or np.any(k_best >= Y_COARSE - 2):
        raise RuntimeError("argmin at the y-grid edge: raise Y_MAX (or C is too close to max(|alpha|, |beta|))")
    lo, hi = y_grid[k_best] - step, y_grid[k_best] + step
    return golden_refine(lambda yy: gamma_c(cc, p, alpha, beta, yy, t_chunk), lo, hi)


def m_c(cc, p, alpha, beta, t_nodes):
    """m_C on all nodes, in chunks."""
    parts = [m_c_chunk(cc, p, alpha, beta, t_nodes[k:k + T_CHUNK]) for k in range(0, len(t_nodes), T_CHUNK)]
    return np.concatenate(parts)


def jump_matrix(n_nodes, q, h):
    """Sparse rows J_i/h = q (phi_{i+1} + phi_{i-1} - 2 cos(qh) phi_i)/(h sin(qh)), periodic indices."""
    idx = np.arange(n_nodes)
    scale = q / (h * np.sin(q * h))
    rows = np.concatenate([idx, idx, idx])
    cols = np.concatenate([(idx + 1) % n_nodes, (idx - 1) % n_nodes, idx])
    vals = np.concatenate([np.full(n_nodes, scale), np.full(n_nodes, scale), np.full(n_nodes, -2 * np.cos(q * h) * scale)])
    return coo_matrix((vals, (rows, cols)), shape=(n_nodes, n_nodes))


def phase_one_sigma(m_nodes, q, h, method="highs-ipm"):
    """sigma* = min sigma s.t. J/h + sigma >= 0, phi <= m, sigma >= 0. Returns (sigma*, phi)."""
    n_nodes = len(m_nodes)
    a_ub = csr_matrix(hstack([-jump_matrix(n_nodes, q, h), -np.ones((n_nodes, 1))]))
    cost = np.zeros(n_nodes + 1)
    cost[-1] = 1.0
    bounds = [(None, mm) for mm in m_nodes] + [(0, None)]
    opts = {"primal_feasibility_tolerance": 1e-10, "dual_feasibility_tolerance": 1e-10}
    res = linprog(cost, A_ub=a_ub, b_ub=np.zeros(n_nodes), bounds=bounds, method=method, options=opts)
    if res.status == 4 and method == "highs-ipm":
        DS_RETRIES.append(n_nodes)
        print(f"  [IPM status 4 at N = {n_nodes}: re-solved with dual simplex (retry #{len(DS_RETRIES)})]", flush=True)
        return phase_one_sigma(m_nodes, q, h, method="highs-ds")
    if res.status != 0:
        raise RuntimeError(f"LP status {res.status} ({method}): {res.message}")
    return res.x[-1], res.x[:-1]


def nodes(n_nodes):
    """t_i = -pi + i h, h = 2 pi/N."""
    h = 2 * np.pi / n_nodes
    return -np.pi + h * np.arange(n_nodes), h


def sigma_at(cc, p, alpha, beta, n_nodes):
    t_nodes, h = nodes(n_nodes)
    return phase_one_sigma(m_c(cc, p, alpha, beta, t_nodes), p / 2, h)


def c_star(p, alpha, beta, n_nodes, c_lo, c_hi):
    """Bisection for the least C with sigma* <= SIGMA_TOL; checks the bracket ends first."""
    if sigma_at(c_hi, p, alpha, beta, n_nodes)[0] > SIGMA_TOL or sigma_at(c_lo, p, alpha, beta, n_nodes)[0] <= SIGMA_TOL:
        raise RuntimeError(f"bad bracket [{c_lo}, {c_hi}] at p={p}, alpha={alpha}, beta={beta}, N={n_nodes}")
    while c_hi - c_lo > C_REL_WIDTH * c_hi:
        mid = (c_lo + c_hi) / 2
        if sigma_at(mid, p, alpha, beta, n_nodes)[0] <= SIGMA_TOL:
            c_hi = mid
        else:
            c_lo = mid
    return c_hi


def gk_bound(p, alpha, beta):
    """Gohberg-Krupnik lower bound (HKV 2003 (1.8)) with a - ib = alpha, a + ib = beta, so |b| = |beta - alpha|/2."""
    bb2_cot2 = (abs(beta - alpha) / 2) ** 2 / np.tan(np.pi / p) ** 2
    return (np.sqrt(bb2_cot2 + ((abs(alpha) - abs(beta)) / 2) ** 2)
            + np.sqrt(bb2_cot2 + ((abs(alpha) + abs(beta)) / 2) ** 2))


def hkv_real(p, a_re, b_re):
    """HKV 2003 exact norm of aI + bH for REAL a, b: sqrt(a^2+b^2) max_theta ratio^(1/p) (dense theta grid, float)."""
    theta = np.linspace(0, 2 * np.pi, 200001)
    th0 = np.arctan2(b_re, a_re)
    num = np.abs(np.cos(theta + th0)) ** p + np.abs(np.cos(theta + th0 + np.pi / p)) ** p
    den = np.abs(np.cos(theta)) ** p + np.abs(np.cos(theta + np.pi / p)) ** p
    return np.hypot(a_re, b_re) * (num / den).max() ** (1 / p)


def pencil_from_ab(a_cx, b_cx):
    """alpha = a - ib, beta = a + ib."""
    return a_cx - 1j * b_cx, a_cx + 1j * b_cx


def sweep(label, p, alpha, beta, grid_sizes, reference):
    """C*_N on nested grids, against a reference value; prints the monotonicity check."""
    previous = None
    c_lo = max(0.97 * reference, (1 + BRACKET_MARGIN) * max(abs(alpha), abs(beta)))   # Theorem R needs C > max(|alpha|, |beta|)
    c_hi = 1.06 * reference
    for n_nodes in grid_sizes:
        cc = c_star(p, alpha, beta, n_nodes, c_lo, c_hi)
        mono = "" if previous is None else f"  step {cc - previous:+.2e} ({'OK' if cc >= previous - 2 * C_REL_WIDTH * cc else 'DROP!'})"
        print(f"{label} p={p} alpha={alpha:.6g} beta={beta:.6g} N={n_nodes:5d}: C*_N = {cc:.9f}  ref = {reference:.9f}"
              f"  C*_N/ref-1 = {cc / reference - 1:+.3e}{mono}", flush=True)
        previous = cc


def run_tests():
    """Kernel of the jump matrix; GK formula = csc, cot at P+ and H; HKV formula at H; the LP at small N brackets P+'s norm."""
    t_nodes, h = nodes(600)
    test_phi = np.cos(0.75 * (t_nodes + 0.3))           # not 2 pi-periodic: test interior rows only
    assert np.abs((jump_matrix(600, 0.75, h).tocsr() @ test_phi)[1:-1]).max() < 1e-6, "q-sinusoid not in the kernel"
    for p in (1.5, 3.0, 4.0):
        p_star = max(p, p / (p - 1))
        assert abs(gk_bound(p, 1.0, 0.0) - 1 / np.sin(np.pi / p)) < 1e-12, "GK at P+"
        assert abs(gk_bound(p, -1j, 1j) - 1 / np.tan(np.pi / (2 * p_star))) < 1e-12, "GK at H"
        assert abs(hkv_real(p, 0.0, 1.0) - 1 / np.tan(np.pi / (2 * p_star))) < 1e-8, "HKV at H"
    ref = 1 / np.sin(np.pi / 3)
    assert sigma_at(1.001 * ref, 3.0, 1.0, 0.0, 300)[0] <= SIGMA_TOL, "P+ at p = 3: C = 1.001 csc should be feasible"
    assert sigma_at(0.99 * ref, 3.0, 1.0, 0.0, 300)[0] > SIGMA_TOL, "P+ at p = 3: C = 0.99 csc should be infeasible"
    print("tests: kernel, GK(P+) = csc, GK(H) = HKV(H) = cot(pi/2p*), LP brackets ||P+||_3 at N = 300 - PASS")


def main_pencil_lp():
    grids = [300, 600, 1200]
    # controls with known norms: P+ (HV 2000), H (Pichorides), real a, b (HKV 2003)
    sweep("CTRL P+  ", 3.0, 1.0 + 0j, 0j, grids, 1 / np.sin(np.pi / 3))
    sweep("CTRL H   ", 3.0, -1j, 1j, grids, 1 / np.tan(np.pi / 6))
    for a_re, b_re in ((1.0, 0.5), (1.0, 2.0)):
        alpha, beta = pencil_from_ab(a_re, b_re)
        sweep(f"CTRL HKV a={a_re} b={b_re}", 3.0, alpha, beta, grids, hkv_real(3.0, a_re, b_re))
    # route C 11:20 line beta/alpha real (GK claimed sharp)
    for lam in (0.9, 0.5, 0.25, -0.5):
        sweep(f"LINE lam={lam}", 3.0, 1.0 + 0j, lam + 0j, grids, gk_bound(3.0, 1.0, lam))
    # route C 11:20 genuinely complex points (LP claimed above GK and above the 2-point model)
    for p, beta in ((4.0, 0.5 * np.exp(0.6j)), (4.0, 0.3 * np.exp(2.0j)), (3.0, 0.5 * np.exp(1.5j))):
        sweep("CPLX     ", p, 1.0 + 0j, beta, grids, gk_bound(p, 1.0, beta))
    print(f"dual-simplex re-solves after IPM errors: {len(DS_RETRIES)} (N = {sorted(set(DS_RETRIES))})")


def main():
    if "--test" in sys.argv:
        run_tests()
    elif "--run" in sys.argv:
        main_pencil_lp()
    else:
        raise SystemExit("usage: pencil_search.py --test | --run")


if __name__ == "__main__":
    main()
