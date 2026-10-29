/- multiplicative contact-error controls in the endpoint estimate.
Frozen source: short_v0.70/endpoint_estimate.tex:52–58.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.EndpointScale

namespace GKSharp
open Real

theorem endpoint_k_error_bounds {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let eps := 1 - endpointLambda p
    let E := (p - 1) * log (1 / eps) + a ^ 2 + sin a ^ 2 / eps + 2 * sin a ^ 2 / eps ^ 2
    E ≤ a / 6 * log (1 / a) + a ^ 2 + a ^ (3 / 2 : ℝ) + 2 * a ∧
      1 - (p - 1) * log (1 / eps) ≤ eps ^ (p - 1) ∧
      1 - a ^ 2 ≤ cos a ^ 2 ∧ E < 1 ∧
      (∀ u : ℝ, 0 ≤ u → 1 - u ≤ (1 + u)⁻¹) := by
  dsimp only
  let a := endpointA p
  let eps := 1 - endpointLambda p
  let E := (p - 1) * log (1 / eps) + a ^ 2 + sin a ^ 2 / eps + 2 * sin a ^ 2 / eps ^ 2
  have ha0 : 0 < a := (endpoint_a_range hp hp1).1
  have ha1 : a ≤ (1 : ℝ) / 100000 := by
    have hh := (endpoint_a_range hp hp1).2.1
    norm_num at hh
    dsimp only [a]
    linarith
  have hl := (endpoint_d_basic hp hp1).2.2.2.2
  have he0 : 0 < eps := by dsimp only [eps]; linarith [hl.2]
  have hs0 : 0 < sqrt a := sqrt_pos.mpr ha0
  have hs2 : sqrt a ^ 2 = a := sq_sqrt ha0.le
  have hs1 : sqrt a ≤ 1 := by nlinarith [sqrt_nonneg a]
  have helo : sqrt a ≤ eps := (endpoint_scale_bounds hp hp1).1
  have hlog0 : 0 ≤ log (1 / eps) := log_nonneg ((le_div_iff₀ he0).mpr (by dsimp only [eps]; linarith [hl.1]))
  have hloga0 : 0 ≤ log (1 / a) := log_nonneg ((le_div_iff₀ ha0).mpr (by linarith))
  have hlog : log (1 / eps) ≤ 1 / 2 * log (1 / a) := by
    have hh := log_le_log (show 0 < 1 / eps by positivity) (one_div_le_one_div_of_le hs0 helo)
    simp only [one_div, log_inv, log_sqrt ha0.le] at hh ⊢
    linarith
  have hprod := mul_le_mul (endpoint_p_sub_one hp hp1) hlog hlog0 (show 0 ≤ a / 3 by positivity)
  change (p - 1) * log (1 / eps) ≤ a / 3 * (1 / 2 * log (1 / a)) at hprod
  have hsinupper : sin a ^ 2 ≤ a ^ 2 :=
    (sq_le_sq₀ (sin_nonneg_of_nonneg_of_le_pi ha0.le (by linarith [pi_gt_three])) ha0.le).mpr (sin_le ha0.le)
  have he2 : a ≤ eps ^ 2 := by nlinarith
  have hsdiv : sin a ^ 2 / eps ≤ a * sqrt a := by
    rw [div_le_iff₀ he0]
    have hh := mul_le_mul_of_nonneg_left helo (show 0 ≤ a * sqrt a by positivity)
    nlinarith
  have hsdiv2 : sin a ^ 2 / eps ^ 2 ≤ a := by
    rw [div_le_iff₀ (pow_pos he0 2)]
    have hh := mul_le_mul_of_nonneg_left he2 ha0.le
    nlinarith
  have hpow : a ^ (3 / 2 : ℝ) = a * sqrt a := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add ha0, rpow_one, ← sqrt_eq_rpow]
  have hE : E ≤ a / 6 * log (1 / a) + a ^ 2 + a ^ (3 / 2 : ℝ) + 2 * a := by
    dsimp only [E]
    rw [hpow]
    have hp' : (p - 1) * log (1 / eps) ≤ a / 6 * log (1 / a) := by
      convert hprod using 1 <;> ring
    have hh := add_le_add (add_le_add (add_le_add_right hp' (a ^ 2)) hsdiv)
      (mul_le_mul_of_nonneg_left hsdiv2 (show (0 : ℝ) ≤ 2 by norm_num))
    convert hh using 1 <;> ring
  refine ⟨hE, ?_, ?_, ?_, ?_⟩
  · rw [rpow_def_of_pos he0]
    have hh := add_one_le_exp (log eps * (p - 1))
    rw [one_div, log_inv]
    nlinarith
  · nlinarith [one_sub_sq_div_two_le_cos (x := a), sq_nonneg (cos a - 1)]
  · have hh := log_le_sub_one_of_pos (show 0 < 1 / a by positivity)
    have hm := mul_le_mul_of_nonneg_left hh ha0.le
    have hcancel : a * (1 / a - 1) = 1 - a := by field_simp <;> ring
    rw [hcancel] at hm
    rw [hpow] at hE
    have hsmall := mul_le_mul_of_nonneg_left hs1 ha0.le
    have ha2 : a ^ 2 ≤ (1 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ ha0.le ha1 2
    linarith
  · intro u hu
    rw [← one_div, le_div_iff₀ (by linarith : 0 < 1 + u)]
    nlinarith [sq_nonneg u]

end GKSharp

#print axioms GKSharp.endpoint_k_error_bounds
