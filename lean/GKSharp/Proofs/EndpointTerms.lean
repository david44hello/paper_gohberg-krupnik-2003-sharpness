/- T1 and T2 controls in the analytic endpoint estimate.
Frozen source: short_v0.70/endpoint_estimate.tex:35–38.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.EndpointLog

namespace GKSharp
open Real

theorem endpoint_term_bounds {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let d := endpointD p
    let lam := endpointLambda p
    let Q := (1 - lam) / sin a
    let C := gk p (lam : ℂ)
    let w := (1 + lam) / 2
    (2 * C) ^ p ≤ 2 * Q + 2 / Q + 8 / 3 * Q * a * log (8 / sqrt a) ∧
      2 * w ≤ (2 * w) ^ p ∧ 2 * w = 2 / (1 + d) ∧ 2 - 2 * d ≤ 2 / (1 + d) := by
  dsimp only
  let a := endpointA p
  let d := endpointD p
  let lam := endpointLambda p
  let Q := (1 - lam) / sin a
  let C := gk p (lam : ℂ)
  let x := (p - 1) * log (2 * C)
  have hC1 : 1 ≤ C := one_le_gk _ _
  have hC0 : 0 < C := by linarith
  have hl := (endpoint_d_basic hp hp1).2.2.2.2
  have hd0 : 0 < d := (endpoint_d_basic hp hp1).1
  have hgk := endpoint_gk_bounds hp hp1
  have hx := endpoint_log_bound hp hp1
  dsimp only at hgk hx
  have hQ0 : 0 < Q := by
    have hh := (endpoint_scale_bounds hp hp1).2.2.1
    have ha0 := (endpoint_a_range hp hp1).1
    have hr := rpow_pos_of_pos ha0 (-(1 / 2 : ℝ))
    exact hr.trans_le hh
  have hlog0 : 0 ≤ log (8 / sqrt a) := by
    have hh := log_nonneg (show 1 ≤ 2 * C by linarith)
    have hx0 : 0 ≤ x := hx.1
    have hxu : x ≤ a / 3 * log (8 / sqrt a) := hx.2.1
    have ha0 : 0 < a := (endpoint_a_range hp hp1).1
    nlinarith
  have hidentity : (2 * C) ^ p = (2 * C) * exp x := by
    rw [rpow_def_of_pos (by positivity : 0 < 2 * C)]
    have hh : log (2 * C) * p = log (2 * C) + x := by dsimp only [x]; ring
    rw [hh, exp_add, exp_log (by positivity : 0 < 2 * C)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hstart : (2 * C) ^ p ≤ 2 * C + 4 * C * x := by
      rw [hidentity]
      have hh := mul_le_mul_of_nonneg_left hx.2.2.2 (show 0 ≤ 2 * C by positivity)
      nlinarith
    have hCu : C ≤ Q + Q⁻¹ := hgk.2.2.1
    have hC2 : C ≤ 2 * Q := hCu.trans hgk.2.2.2
    have hxu : x ≤ a / 3 * log (8 / sqrt a) := hx.2.1
    have hcross := mul_le_mul hC2 hxu hx.1 (show 0 ≤ 2 * Q by positivity)
    change (2 * C) ^ p ≤ 2 * Q + 2 / Q + 8 / 3 * Q * a * log (8 / sqrt a)
    rw [div_eq_mul_inv (2 : ℝ) Q]
    nlinarith
  · have hh : 1 ≤ 2 * ((1 + lam) / 2) := by linarith [hl.1]
    exact self_le_rpow_of_one_le hh hp.le
  · change 2 * ((1 + lam) / 2) = 2 / (1 + d)
    dsimp only [lam, endpointLambda, d]
    field_simp [show 1 + endpointD p ≠ 0 by linarith [(endpoint_d_basic hp hp1).1]]
    <;> ring
  · rw [le_div_iff₀ (by linarith : 0 < 1 + d)]
    nlinarith [sq_nonneg d]

end GKSharp

#print axioms GKSharp.endpoint_term_bounds
