/- coordinate and elementary trigonometric rows, frozen sec5d:11-59.
Copyright (C) Dave Goel 2026--now. -/
import Mathlib

namespace GKSharp

theorem sec5d_coordinate_dictionary_proved (p θ : ℝ) (hp : 1 < p ∧ p < 2)
    (hθ : 0 < θ ∧ θ < Real.pi) :
    1 < p / (2 - p) ∧
    0 < (1 - p / 2) * θ ∧
    (1 - p / 2) * θ < Real.pi / (p / (2 - p) + 1) ∧
    (p / (2 - p) + 1) * ((1 - p / 2) * θ) = θ ∧
    (p / (2 - p) - 1) * ((1 - p / 2) * θ) = (p - 1) * θ ∧
    (p - 1) = (p / (2 - p) - 1) / (p / (2 - p) + 1) := by
  have hd : 0 < 2 - p := by linarith [hp.2]
  have hm : 1 < p / (2 - p) := (lt_div_iff₀ hd).mpr (by linarith [hp.1])
  have hm1 : 0 < p / (2 - p) + 1 := by linarith
  have hcoord : (p / (2 - p) + 1) * ((1 - p / 2) * θ) = θ := by
    field_simp
    <;> ring
  refine ⟨hm, mul_pos (by linarith [hp.2]) hθ.1, ?_, hcoord, ?_, ?_⟩
  · apply (lt_div_iff₀ hm1).mpr
    exact lt_of_eq_of_lt (by simpa only [mul_comm] using hcoord) hθ.2
  · field_simp
    <;> ring
  · apply (eq_div_iff (ne_of_gt hm1)).mpr
    field_simp
    <;> ring

theorem sec5d_gamma_denominators_proved (a b γ : ℝ)
    (hab : 0 < b ∧ b < a ∧ a < Real.pi / 2)
    (hγ : b < γ ∧ γ < Real.pi / 2) :
    0 < Real.sin (γ + b) ∧ 0 < Real.sin (γ + a) ∧ 0 < Real.sin (γ - b) ∧
    0 < Real.sin (γ - b) / Real.sin (γ + b) ∧
    Real.sin (γ - b) / Real.sin (γ + b) < 1 := by
  have hplusb : 0 < Real.sin (γ + b) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hab.1, hγ.1]) (by linarith [hab.2.1, hab.2.2, hγ.2])
  have hplusa : 0 < Real.sin (γ + a) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hab.1, hab.2.1, hγ.1]) (by linarith [hab.2.2, hγ.2])
  have hminus : 0 < Real.sin (γ - b) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hγ.1]) (by linarith [hγ.2, hab.1, Real.pi_pos])
  have hcos : 0 < Real.cos γ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hab.1, hγ.1, Real.pi_pos], hγ.2⟩
  have hsinb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hab.1
    (by linarith [hab.2.1, hab.2.2, Real.pi_pos])
  refine ⟨hplusb, hplusa, hminus, div_pos hminus hplusb, (div_lt_one hplusb).mpr ?_⟩
  rw [Real.sin_sub, Real.sin_add]
  nlinarith [mul_pos hcos hsinb]

theorem sec5d_sine_product_proved (m α : ℝ) :
    Real.sin ((m + 1) * α) * Real.sin ((m - 1) * α) =
      Real.sin (m * α) ^ 2 - Real.sin α ^ 2 := by
  rw [show (m + 1) * α = m * α + α by ring,
      show (m - 1) * α = m * α - α by ring, Real.sin_add, Real.sin_sub]
  linear_combination (Real.sin (m * α)) ^ 2 * Real.sin_sq_add_cos_sq α -
    Real.sin α ^ 2 * Real.sin_sq_add_cos_sq (m * α)

end GKSharp
