/- open endpoint: rational angular control and Taylor ingredients.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential

namespace GKSharp
open Real

theorem endpoint_a_inverse {p : ℝ} (hp : 1 < p) : p = Real.pi / (Real.pi - endpointA p) := by
  have hp0 : p ≠ 0 := by linarith
  have h : Real.pi - endpointA p = Real.pi / p := by
    unfold endpointA
    field_simp
    <;> ring
  rw [h]
  field_simp

/-- endpoint_estimate.tex:8,14. Exact bounds on the complete open interval; no numeric assumption. -/
theorem endpoint_a_range {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    0 < endpointA p ∧ endpointA p < 3.2 * 10 ^ (-6 : ℤ) ∧
      p = Real.pi / (Real.pi - endpointA p) := by
  have hp0 : 0 < p := by linarith
  have hdelta : p - 1 ≤ (1 : ℝ) / 1000000 := by
    norm_num at hp1
    linarith
  have hnum : Real.pi * (p - 1) ≤ (3.15 : ℝ) * (1 / 1000000) :=
    mul_le_mul Real.pi_lt_d2.le hdelta (by linarith) (by norm_num)
  refine ⟨by unfold endpointA; positivity, ?_, endpoint_a_inverse hp⟩
  unfold endpointA
  rw [div_lt_iff₀ hp0]
  norm_num
  nlinarith

/-- endpoint_estimate.tex:16. The p−1 comparison uses π>3.14, with the full uniform p bound. -/
theorem endpoint_p_sub_one {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    p - 1 ≤ endpointA p / 3 := by
  have hp0 : 0 < p := by linarith
  have h3 : 3 * p ≤ Real.pi := by
    norm_num at hp1
    nlinarith [Real.pi_gt_d2]
  have hmul := mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr hp.le)
  unfold endpointA
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3), le_div_iff₀ hp0]
  nlinarith

/-- endpoint_estimate.tex:16. The sine/cosine Taylor controls need no machine evaluation. -/
theorem endpoint_trig_bounds {p : ℝ} (hp : 1 < p) :
    endpointA p - endpointA p ^ 3 / 6 ≤ sin (endpointA p) ∧
    sin (endpointA p) ≤ endpointA p ∧
    1 - endpointA p ^ 2 / 2 ≤ cos (endpointA p) ∧ cos (endpointA p) ≤ 1 := by
  have ha : 0 ≤ endpointA p := by unfold endpointA; positivity
  exact ⟨Real.sin_ge_sub_cube ha, Real.sin_le ha, Real.one_sub_sq_div_two_le_cos,
    Real.cos_le_one _⟩

theorem small_angle_sin_square {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 10) :
    a ^ 2 * (1 - a ^ 2 / 3) ≤ sin a ^ 2 := by
  have ha2 : a ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := pow_le_pow_left₀ ha0 ha1 2
  have hcub := mul_le_mul_of_nonneg_left ha2 ha0
  have hl : 0 ≤ a - a ^ 3 / 6 := by nlinarith
  have hs := Real.sin_ge_sub_cube ha0
  have hsq := (sq_le_sq₀ hl (hl.trans hs)).2 hs
  nlinarith [sq_nonneg (a ^ 3)]

theorem small_angle_inv_cos_four {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 10) :
    1 / cos a ^ 4 ≤ 1 + 3 * a ^ 2 := by
  have ha2 : a ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := pow_le_pow_left₀ ha0 ha1 2
  have hc : 0 < cos a := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := a)]
  have hc4 : 1 - 2 * a ^ 2 ≤ cos a ^ 4 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := a), sq_nonneg (cos a - 1), sq_nonneg (cos a ^ 2 - 1)]
  rw [div_le_iff₀ (pow_pos hc 4)]
  have hh : 0 ≤ 1 - 6 * a ^ 2 := by nlinarith
  calc
    1 ≤ (1 + 3 * a ^ 2) * (1 - 2 * a ^ 2) := by nlinarith [mul_nonneg (sq_nonneg a) hh]
    _ ≤ (1 + 3 * a ^ 2) * cos a ^ 4 := mul_le_mul_of_nonneg_left hc4 (by positivity)

theorem small_angle_product {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 10) :
    (1 + a / 3) * (1 + 3 * a ^ 2) ≤ 1 + a := by
  have h1 := mul_nonneg ha0 (show 0 ≤ 1 / 10 - a by linarith)
  have h2 := mul_nonneg (sq_nonneg a) (show 0 ≤ 1 / 10 - a by linarith)
  nlinarith

/-- endpoint_estimate.tex:19–22. Every printed ingredient of the d² enclosure is internally proved. -/
theorem endpoint_enclosure_ingredients {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    a ^ 2 * (1 - a ^ 2 / 3) ≤ sin a ^ 2 ∧
    Real.pi / (4 * a) - 2 ≤ p * Real.pi / (4 * a) - 1 - cos a ^ 2 ∧
    cos a ^ (-4 : ℤ) ≤ 1 + 3 * a ^ 2 ∧
    (1 + a / 3) * (1 + 3 * a ^ 2) ≤ 1 + a := by
  obtain ⟨ha0, ha1, _⟩ := endpoint_a_range hp hp1
  have ha10 : endpointA p ≤ 1 / 10 := by norm_num at ha1; linarith
  refine ⟨small_angle_sin_square ha0.le ha10, ?_, ?_, small_angle_product ha0.le ha10⟩
  · have hn : Real.pi ≤ p * Real.pi := by nlinarith [Real.pi_pos]
    have hd := div_le_div_of_nonneg_right hn (by positivity : 0 ≤ 4 * endpointA p)
    nlinarith [Real.cos_sq_le_one (endpointA p)]
  · have h := small_angle_inv_cos_four ha0.le ha10
    simpa only [zpow_neg, zpow_ofNat, one_div] using h

end GKSharp
