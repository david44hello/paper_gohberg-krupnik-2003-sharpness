/- actual GK root and positive-axis test in the endpoint appendix.
Frozen source: short_v0.70/endpoint_estimate.tex:27–32.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.EndpointScale
import GKSharp.Proofs.GKProps
import GKSharp.Proofs.ObstacleMinimum
import GKSharp.Proofs.Sec4bAxis

namespace GKSharp
open Real Set

theorem endpoint_gk_bounds {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let lam := endpointLambda p
    let Q := (1 - lam) / sin (endpointA p)
    let C := gk p (lam : ℂ)
    C = (Q + sqrt (Q ^ 2 + 4 * lam)) / 2 ∧ C ^ 2 ≤ Q ^ 2 + 2 ∧
      C ≤ Q + Q⁻¹ ∧ Q + Q⁻¹ ≤ 2 * Q := by
  dsimp only
  let a := endpointA p
  let lam := endpointLambda p
  let Q := (1 - lam) / sin a
  let C := gk p (lam : ℂ)
  have ha0 : 0 < a := (endpoint_a_range hp hp1).1
  have ha1 : a < 1 := by
    have hh := (endpoint_a_range hp hp1).2.1
    norm_num at hh
    dsimp only [a]
    linarith
  have hl : lam ∈ Ioo (0 : ℝ) 1 := (endpoint_d_basic hp hp1).2.2.2.2
  have hs : 0 < sin a := sin_pos_of_pos_of_lt_pi ha0 (by linarith [pi_gt_three])
  have hQ0 : 0 < Q := div_pos (by linarith [hl.2]) hs
  have hQ1 : 1 ≤ Q := by
    have hh := (endpoint_scale_bounds hp hp1).2.2.1
    have hpow : a ^ (-(1 / 2 : ℝ)) = 1 / sqrt a := by
      rw [rpow_neg ha0.le, ← sqrt_eq_rpow, one_div]
    have hsqrt : sqrt a ≤ 1 := by nlinarith [sq_sqrt ha0.le, sqrt_nonneg a]
    have hrec : 1 ≤ 1 / sqrt a := (le_div_iff₀ (sqrt_pos.mpr ha0)).mpr (by linarith)
    change a ^ (-(1 / 2 : ℝ)) ≤ Q at hh
    rw [hpow] at hh
    exact hrec.trans hh
  have hC1 : 1 ≤ C := one_le_gk _ _
  have hasin : sin a = sin (Real.pi / p) := by
    have ha : a = Real.pi - Real.pi / p := by
      dsimp only [a]
      unfold endpointA
      field_simp <;> ring
    rw [ha, sin_pi_sub]
  have hquad : C ^ 2 = Q * C + lam := by
    have hh := (gk_real_eq hp hl.2).1
    rw [← hasin] at hh
    have hqc : sin a * Q = 1 - lam := by
      dsimp only [Q]
      field_simp
    apply (mul_left_cancel₀ hs.ne')
    linear_combination -hh - C * hqc
  have hCge : Q ≤ C := by
    have hh : C * (C - Q) = lam := by nlinarith
    nlinarith [hl.1]
  have hroot : C = (Q + sqrt (Q ^ 2 + 4 * lam)) / 2 := by
    have hdis : 0 ≤ Q ^ 2 + 4 * lam := by nlinarith [hl.1]
    have hh := sq_sqrt hdis
    have hpos := sqrt_nonneg (Q ^ 2 + 4 * lam)
    nlinarith
  have hCu : C ≤ Q + Q⁻¹ := by
    have hrec : 0 < Q⁻¹ := inv_pos.mpr hQ0
    have hcancel : Q * Q⁻¹ = 1 := mul_inv_cancel₀ hQ0.ne'
    have hh : C * (C - Q) ≤ 1 := by nlinarith [hl.2]
    have hgoal : Q * (C - Q) ≤ 1 := by nlinarith [sq_nonneg (C - Q)]
    have hgoal' := mul_le_mul_of_nonneg_left hgoal hrec.le
    rw [← mul_assoc, inv_mul_cancel₀ hQ0.ne', one_mul, mul_one] at hgoal'
    nlinarith
  have hC2 : C ^ 2 ≤ Q ^ 2 + 2 := by
    have hh := mul_le_mul_of_nonneg_left hCu hQ0.le
    have hcancel : Q * Q⁻¹ = 1 := mul_inv_cancel₀ hQ0.ne'
    nlinarith [hl.2]
  have hrecQ : Q⁻¹ ≤ Q := by
    rw [← one_div, div_le_iff₀ hQ0]
    nlinarith
  exact ⟨hroot, hC2, hCu, by linarith⟩

/-- The actual infimum is bounded by the value at y=0, the midpoint test of (edgeaxis). -/
theorem endpoint_midpoint_bound {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let lam := endpointLambda p
    let C := gk p (lam : ℂ)
    let w := (1 + lam) / 2
    axisGap p lam ≤ (2 * C) ^ p - (2 * w) ^ p - kConst p lam := by
  dsimp only
  let lam := endpointLambda p
  let C := gk p (lam : ℂ)
  have hhi : p ≤ (1000001 : ℝ) / 1000000 := by norm_num at hp1; linarith
  have hp2 : p < 2 := by linarith
  have hl := (endpoint_d_basic hp hp1).2.2.2.2
  have hC : max 1 ‖(lam : ℂ)‖ < C := gk_gt_max hp (ne_of_lt hp2) (by
    intro hh
    have : lam = 1 := by exact_mod_cast hh
    linarith [hl.2])
  have hm := csInf_le (obstacle_bddBelow (by linarith : 0 < p) (lam : ℂ) hC 0)
    (mem_range_self (0 : ℝ))
  have hsq (u : ℝ) (hu : 0 ≤ u) : (u ^ 2) ^ (p / 2) = u ^ p := by
    rw [← rpow_natCast u 2, ← rpow_mul hu]
    congr 1
    ring
  have hval : GKSharp.gamma p C (lam : ℂ) 0 0 = (2 * C) ^ p - (1 + lam) ^ p := by
    rw [sec4b_gamma_axis]
    simp only [cosh_zero, exp_zero, neg_zero, mul_one]
    rw [show ((2 : ℝ) + 2) = (2 : ℝ) ^ 2 by norm_num,
      show (1 : ℝ) + lam ^ 2 + 2 * lam = (1 + lam) ^ 2 by ring,
      hsq 2 (by norm_num), hsq (1 + lam) (by linarith [hl.1]),
      mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (gk_nonneg _ _)]
    ring
  change axisGap p lam ≤ _
  unfold axisGap
  change GKSharp.obstacle p C (lam : ℂ) 0 - kConst p lam ≤ _
  have hh : 2 * ((1 + lam) / 2) = 1 + lam := by ring
  rw [hh]
  rw [hval] at hm
  change GKSharp.obstacle p C (lam : ℂ) 0 ≤ (2 * C) ^ p - (1 + lam) ^ p at hm
  exact sub_le_sub_right hm (kConst p lam)

end GKSharp

#print axioms GKSharp.endpoint_gk_bounds
#print axioms GKSharp.endpoint_midpoint_bound
