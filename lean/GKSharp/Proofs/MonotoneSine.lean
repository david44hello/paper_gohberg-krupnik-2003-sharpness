/- sine comparison and Psi positivity, frozen sec5d_monotone.tex:67-68.
Copyright (C) Dave Goel 2026--now. -/
import Mathlib

namespace GKSharp

/-- Strict sine comparison on the paper's domain, with a stronger upper-angle hypothesis. -/
theorem sec5d_sine_comparison_proved (m α : ℝ) (hm : 1 < m) (hα : 0 < α)
    (hmα : m * α < Real.pi) :
    0 < Real.sin (m * α) ∧ Real.sin (m * α) < m * Real.sin α := by
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have hmα0 : 0 < m * α := mul_pos hm0 hα
  have hi : 0 < 1 / m := one_div_pos.mpr hm0
  have hi1 : 1 / m < 1 := (div_lt_one hm0).mpr hm
  have hj : 0 < 1 - 1 / m := sub_pos.mpr hi1
  have hc := strictConcaveOn_sin_Icc.2
    (show m * α ∈ Set.Icc (0 : ℝ) Real.pi from ⟨hmα0.le, hmα.le⟩)
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (ne_of_gt hmα0) hi hj (by ring : (1 / m : ℝ) + (1 - 1 / m) = 1)
  have hmid : (1 / m) * (m * α) = α := by field_simp
  have hmul : m * (1 / m) = 1 := by field_simp
  simp only [smul_eq_mul, mul_zero, add_zero, Real.sin_zero, hmid] at hc
  refine ⟨Real.sin_pos_of_pos_of_lt_pi hmα0 hmα, ?_⟩
  have h := mul_lt_mul_of_pos_left hc hm0
  simpa only [← mul_assoc, hmul, one_mul] using h

/-- The exact Psi expression is positive. The private leaf needs no proposed definition import. -/
theorem sec5d_Psi_pos_expr_proved (m α : ℝ) (hm : 1 < m)
    (hα : 0 < α ∧ α < Real.pi / (m + 1)) :
    0 < (m ^ 2 * Real.sin α ^ 2 - Real.sin (m * α) ^ 2) / Real.sin α ^ 4 := by
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have hm1 : 0 < m + 1 := by linarith
  have hsum : (m + 1) * α < Real.pi := by
    have h := (lt_div_iff₀ hm1).mp hα.2
    simpa only [mul_comm] using h
  have hmα : m * α < Real.pi := by nlinarith [hα.1]
  have hαpi : α < Real.pi := by nlinarith [mul_pos (sub_pos.mpr hm) hα.1]
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hαpi
  obtain ⟨hsinm, hlt⟩ := sec5d_sine_comparison_proved m α hm hα.1 hmα
  have hsquares : Real.sin (m * α) ^ 2 < (m * Real.sin α) ^ 2 := by
    nlinarith [mul_pos hm0 hsin]
  apply div_pos _ (pow_pos hsin 4)
  nlinarith [hsquares]

end GKSharp
