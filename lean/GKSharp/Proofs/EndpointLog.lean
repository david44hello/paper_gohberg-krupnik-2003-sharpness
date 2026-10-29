/- logarithmic endpoint error and exponential control.
Frozen source: short_v0.70/endpoint_estimate.tex:33–38.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.EndpointGK

namespace GKSharp
open Real

theorem endpoint_log_bound {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let C := gk p (endpointLambda p : ℂ)
    let x := (p - 1) * log (2 * C)
    0 ≤ x ∧ x ≤ a / 3 * log (8 / sqrt a) ∧ a / 3 * log (8 / sqrt a) < 1 ∧
      exp x ≤ 1 + 2 * x := by
  dsimp only
  let a := endpointA p
  let C := gk p (endpointLambda p : ℂ)
  let x := (p - 1) * log (2 * C)
  have ha0 : 0 < a := (endpoint_a_range hp hp1).1
  have ha1 : a ≤ (1 : ℝ) / 100000 := by
    have hh := (endpoint_a_range hp hp1).2.1
    norm_num at hh
    dsimp only [a]
    linarith
  have hs0 : 0 < sqrt a := sqrt_pos.mpr ha0
  have hs2 : sqrt a ^ 2 = a := sq_sqrt ha0.le
  have hC1 : 1 ≤ C := one_le_gk _ _
  have hC0 : 0 < C := by linarith
  have hQ := endpoint_scale_bounds hp hp1
  have hGK := endpoint_gk_bounds hp hp1
  dsimp only at hQ hGK
  have hpow : a ^ (-(1 / 2 : ℝ)) = 1 / sqrt a := by
    rw [rpow_neg ha0.le, ← sqrt_eq_rpow, one_div]
  have hCu : 2 * C ≤ 8 / sqrt a := by
    have hh := hGK.2.2.1.trans hGK.2.2.2
    have hq := hQ.2.2.2.1
    change (1 - endpointLambda p) / sin a ≤ 2 * a ^ (-(1 / 2 : ℝ)) at hq
    rw [hpow] at hq
    change C ≤ 2 * ((1 - endpointLambda p) / sin a) at hh
    have hcombined := hh.trans (mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 2 by norm_num))
    calc
      2 * C ≤ 2 * (2 * (2 * (1 / sqrt a))) := mul_le_mul_of_nonneg_left hcombined (by norm_num)
      _ = 8 / sqrt a := by ring
  have hlog0 : 0 ≤ log (2 * C) := log_nonneg (by linarith)
  have hlogup := log_le_log (by positivity : 0 < 2 * C) hCu
  have hlogupper0 : 0 ≤ log (8 / sqrt a) := hlog0.trans hlogup
  have hx0 : 0 ≤ x := mul_nonneg (by linarith) hlog0
  have hxup : x ≤ a / 3 * log (8 / sqrt a) :=
    mul_le_mul (endpoint_p_sub_one hp hp1) hlogup hlog0 (by positivity)
  have hrough : a / 3 * log (8 / sqrt a) ≤ (8 / 3 : ℝ) * sqrt a := by
    have hh := log_le_sub_one_of_pos (show 0 < 8 / sqrt a by positivity)
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ a / 3 by positivity)
    have hcancel : a / 3 * (8 / sqrt a - 1) = (8 / 3 : ℝ) * sqrt a - a / 3 := by
      apply (mul_right_cancel₀ hs0.ne')
      field_simp
      nlinarith [hs2]
    rw [hcancel] at hm
    linarith
  have hsmall : a / 3 * log (8 / sqrt a) < 1 / 2 := by
    have hs : sqrt a < 1 / 100 := by nlinarith
    linarith
  have hexp := exp_bound_div_one_sub_of_interval hx0 (show x < 1 by linarith)
  have hrec : 1 / (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - x)]
    have hh := mul_nonneg hx0 (show 0 ≤ 1 - 2 * x by linarith)
    nlinarith
  exact ⟨hx0, hxup, by linarith, hexp.trans hrec⟩

end GKSharp

#print axioms GKSharp.endpoint_log_bound
