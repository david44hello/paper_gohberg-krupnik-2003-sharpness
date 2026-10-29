/- curve-chain algebra and denominator signs, frozen short v0.70 sec5d.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.MonotonicityCurve
import GKSharp.Proofs.MonotoneIdentities

namespace GKSharp

theorem sec5d_cot_difference_proved (x y : ℝ) (hx : Real.sin x ≠ 0) (hy : Real.sin y ≠ 0) :
    Real.cot x - Real.cot y = Real.sin (y - x) / (Real.sin x * Real.sin y) := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.sin_sub]
  field_simp

theorem sec5d_cos_sum_difference_proved (a b : ℝ)
    (hab : 0 < b ∧ b < a ∧ a < Real.pi / 2) :
    Real.cos (a - b) + Real.cos (a + b) = 2 * Real.cos a * Real.cos b ∧
    Real.cos (a - b) - Real.cos (a + b) = 2 * Real.sin a * Real.sin b ∧
    0 < Real.cos (a - b) + Real.cos (a + b) ∧
    0 < Real.cos (a - b) - Real.cos (a + b) := by
  have ha : 0 < a := lt_trans hab.1 hab.2.1
  have hbpi : b < Real.pi / 2 := lt_trans hab.2.1 hab.2.2
  have hca := Real.cos_pos_of_mem_Ioo (x := a) ⟨by linarith [Real.pi_pos], hab.2.2⟩
  have hcb := Real.cos_pos_of_mem_Ioo (x := b) ⟨by linarith [Real.pi_pos], hbpi⟩
  have hsa := Real.sin_pos_of_pos_of_lt_pi ha (by linarith [hab.2.2, Real.pi_pos])
  have hsb := Real.sin_pos_of_pos_of_lt_pi hab.1 (by linarith [hbpi, Real.pi_pos])
  simp only [Real.cos_sub, Real.cos_add]
  constructor
  · ring
  constructor
  · ring
  constructor <;> nlinarith [mul_pos hca hcb, mul_pos hsa hsb]

theorem sec5d_denominator_positive_proved {p θ X : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) (hX : |X| ≤ 1) :
    0 < Real.cos ((1 - p / 2) * θ) - X * Real.cos (p / 2 * θ) ∧
    0 < monoSignDenominator p θ X := by
  obtain ⟨hd, hprod, -⟩ := sec5d_trig_dictionary_proved p θ ⟨hp1,hp2⟩ ⟨hθ0,hθ⟩
  have hsθ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
  have he0 : 0 < (p - 1) * θ := mul_pos (by linarith) hθ0
  have hepi : (p - 1) * θ < Real.pi := by nlinarith
  have hse := Real.sin_pos_of_pos_of_lt_pi he0 hepi
  have hsα := Real.sin_pos_of_pos_of_lt_pi (x := (1 - p / 2) * θ)
    (mul_pos (by linarith) hθ0) (by nlinarith [Real.pi_pos])
  have hgap : 0 < Real.cos ((1 - p / 2) * θ) - X * Real.cos (p / 2 * θ) := by
    have hp := mul_pos hsθ hse
    have habs := abs_le.mp hX
    rcases le_total 0 (Real.cos (p / 2 * θ)) with hc | hc
    · have hbound := mul_le_mul_of_nonneg_right habs.2 hc
      have hstrict : Real.cos (p / 2 * θ) < Real.cos ((1 - p / 2) * θ) := by nlinarith
      nlinarith
    · have hbound := mul_le_mul_of_nonpos_right habs.1 hc
      have hstrict : -Real.cos (p / 2 * θ) < Real.cos ((1 - p / 2) * θ) := by nlinarith
      nlinarith
  refine ⟨hgap, ?_⟩
  unfold monoSignDenominator
  exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hsθ) hse) hsα) hgap

theorem sec5d_gamma_ratio_derivative_proved {p θ g : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2) :
    HasDerivAt (fun x => Real.sin (x - (p - 1) * (θ / 2)) / Real.sin (x + (p - 1) * (θ / 2)))
      (Real.sin ((p - 1) * θ) / Real.sin (g + (p - 1) * (θ / 2)) ^ 2) g ∧
    0 < Real.sin ((p - 1) * θ) / Real.sin (g + (p - 1) * (θ / 2)) ^ 2 := by
  let b := (p - 1) * (θ / 2)
  change b < g ∧ g < Real.pi / 2 at hg
  have hb : 0 < b := mul_pos (by linarith) (half_pos hθ0)
  have hbpi : b < Real.pi / 2 := by dsimp [b]; nlinarith
  have hplus : 0 < Real.sin (g + b) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hg.1]) (by linarith [hg.2])
  have hdouble : Real.sin ((p - 1) * θ) =
      Real.cos (g - b) * Real.sin (g + b) - Real.sin (g - b) * Real.cos (g + b) := by
    rw [show (p - 1) * θ = (g + b) - (g - b) by dsimp [b]; ring, Real.sin_sub]
    ring
  have hnum : HasDerivAt (fun x : ℝ => Real.sin (x - b)) (Real.cos (g - b)) g := by
    simpa using ((hasDerivAt_id g).sub_const b).sin
  have hden : HasDerivAt (fun x : ℝ => Real.sin (x + b)) (Real.cos (g + b)) g := by
    simpa using ((hasDerivAt_id g).add_const b).sin
  have hderiv := hnum.div hden hplus.ne'
  refine ⟨?_, ?_⟩
  · convert hderiv using 1 <;> simp only [Pi.div_apply, hdouble, b]
  · exact div_pos (Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)) (sq_pos_of_pos hplus)

theorem sec5d_sigma_cosine_proved {p θ g : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2) :
    Real.cos (2 * g - (1 - p / 2) * θ) =
      Real.cos (2 * g) * Real.cos ((1 - p / 2) * θ) + monoSigma p θ g ∧
    Real.cos (2 * g + (1 - p / 2) * θ) =
      Real.cos (2 * g) * Real.cos ((1 - p / 2) * θ) - monoSigma p θ g := by
  have hg0 : 0 < g := lt_trans (mul_pos (by linarith) (half_pos hθ0)) hg.1
  have hs : 0 ≤ Real.sin (2 * g) :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hg.2])).le
  have hsqrt : Real.sqrt (1 - Real.cos (2 * g) ^ 2) = Real.sin (2 * g) := by
    rw [show 1 - Real.cos (2 * g) ^ 2 = Real.sin (2 * g) ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq (2 * g)], Real.sqrt_sq hs]
  simp [Real.cos_sub, Real.cos_add, monoSigma, hsqrt]

theorem sec5d_B_angle_threshold_proved {m α lam : ℝ} (hm : 1 < m)
    (hα : 0 < α ∧ α < Real.pi / (m + 1)) (hl : -1 < lam) (hl0 : lam ≤ 0) :
    α < m * α ∧ m * α < Real.pi - α ∧
    4 * (m ^ 2 - 1) * lam / (1 + lam) ^ 2 ≤ 0 := by
  have hprod := (lt_div_iff₀ (show 0 < m + 1 by linarith)).mp hα.2
  refine ⟨by nlinarith [hα.1], by nlinarith, ?_⟩
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by nlinarith) hl0) (sq_nonneg _)

end GKSharp

