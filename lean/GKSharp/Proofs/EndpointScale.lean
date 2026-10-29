/- quantitative endpoint epsilon and Q scales.
Frozen source: short_v0.70/endpoint_estimate.tex:23–25.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.EndpointEnclosure

namespace GKSharp
open Real

theorem endpoint_scale_bounds {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let eps := 1 - endpointLambda p
    let Q := eps / sin a
    sqrt a ≤ eps ∧ eps ≤ 1.8 * sqrt a ∧
      a ^ (-(1 / 2 : ℝ)) ≤ Q ∧ Q ≤ 2 * a ^ (-(1 / 2 : ℝ)) ∧
      2 * endpointD p ≤ 1.8 * sqrt a := by
  dsimp only
  let a := endpointA p
  let d := endpointD p
  let eps := 1 - endpointLambda p
  have ha0 : 0 < a := (endpoint_a_range hp hp1).1
  have ha1 : a ≤ (1 : ℝ) / 100000 := by
    have hh := (endpoint_a_range hp hp1).2.1
    norm_num at hh
    dsimp only [a]
    linarith
  have hd0 : 0 < d := (endpoint_d_basic hp hp1).1
  have heq : eps = 2 * d / (1 + d) := (endpoint_d_basic hp hp1).2.2.2.1
  have hs0 : 0 < sqrt a := sqrt_pos.mpr ha0
  have hs2 : sqrt a ^ 2 = a := sq_sqrt ha0.le
  have hb := endpoint_d_squared_bounds hp hp1
  change Real.pi * a / 4 * (1 - 3 * a) ≤ d ^ 2 ∧
    d ^ 2 ≤ Real.pi * a / 4 * (1 + a) at hb
  have hdlo : (7 / 10 : ℝ) * a ≤ d ^ 2 := by
    have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    have hcoef := mul_le_mul_of_nonneg_right hpi
      (show 0 ≤ a / 4 * (1 - 3 * a) by apply mul_nonneg (by positivity); linarith)
    have haa := mul_nonneg ha0.le (show 0 ≤ (1 : ℝ) / 100000 - a by linarith)
    nlinarith [hb.1]
  have hdhi : d ^ 2 ≤ (81 / 100 : ℝ) * a := by
    have hpi : Real.pi ≤ (63 / 20 : ℝ) := by linarith [Real.pi_lt_d2]
    have hcoef := mul_le_mul_of_nonneg_right hpi (show 0 ≤ a / 4 * (1 + a) by positivity)
    have haa := mul_nonneg ha0.le (show 0 ≤ (1 : ℝ) / 100000 - a by linarith)
    nlinarith [hb.2]
  have hdsmall : d < 1 / 100 := by nlinarith
  have hdup : 2 * d ≤ (1.8 : ℝ) * sqrt a := by nlinarith
  have hlo : sqrt a ≤ eps := by
    rw [heq, le_div_iff₀ (by linarith)]
    have hden : (1 + d) ^ 2 ≤ (10201 / 10000 : ℝ) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hden ha0.le
    have hsq : (sqrt a * (1 + d)) ^ 2 ≤ (2 * d) ^ 2 := by
      rw [mul_pow, hs2]
      nlinarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  have heup : eps ≤ (1.8 : ℝ) * sqrt a := by
    rw [heq]
    have hh : 2 * d / (1 + d) ≤ 2 * d := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg d]
    exact hh.trans hdup
  have hsin0 : 0 < sin a := sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_gt_three])
  have hsinupper : sin a ≤ a := sin_le ha0.le
  have hsinlower : (9 / 10 : ℝ) * a ≤ sin a := by
    have hs := sin_ge_sub_cube ha0.le
    have ha2 : a ^ 2 ≤ (1 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ ha0.le ha1 2
    have hh := mul_nonneg ha0.le (show 0 ≤ (1 / 100000 : ℝ) ^ 2 - a ^ 2 by linarith)
    nlinarith
  have hpow : a ^ (-(1 / 2 : ℝ)) = 1 / sqrt a := by
    rw [rpow_neg ha0.le, ← sqrt_eq_rpow, one_div]
  refine ⟨hlo, heup, ?_, ?_, hdup⟩
  · rw [hpow, div_le_div_iff₀ hs0 hsin0]
    have hh := mul_le_mul_of_nonneg_right hlo hs0.le
    nlinarith
  · rw [hpow, ← mul_div_assoc, div_le_div_iff₀ hsin0 hs0]
    have hh := mul_le_mul_of_nonneg_right heup hs0.le
    nlinarith

end GKSharp

#print axioms GKSharp.endpoint_scale_bounds
