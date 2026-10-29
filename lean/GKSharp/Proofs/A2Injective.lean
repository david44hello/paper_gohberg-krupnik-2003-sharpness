/- GKSharp/Proofs/A2Injective.lean - (A2) of Section 5, the text's own step: `ρ(θ) = |w(z_θ)|` is injective on
`(0, π)` "by (A1)" (sec5_sharp_inequality.tex l.84-85).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.A1
import GKSharp.Proofs.MobiusDict

namespace GKSharp.A2Injective

open ComplexConjugate

section Curve

variable {p lam θ : ℝ}

/-- `R(θ) > 0` on `(0, π)`: `0 < s₁ < s₂` (sec5_sharp_inequality.tex l.45-48). -/
theorem curveR_pos (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) (hθ0 : 0 < θ)
    (hθ : θ < Real.pi) : 0 < curveR p lam θ := by
  obtain ⟨h1, h2, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  exact curveRoot_pos hl hl1 h1 h2.le

/-- `z_θ ≠ -1` (its imaginary part is `-R(θ) sin θ < 0`). -/
theorem curveZ_ne (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) (hθ0 : 0 < θ)
    (hθ : θ < Real.pi) : curveZ p lam θ ≠ -1 := by
  intro h
  have h0 : (1 : ℂ) + curveZ p lam θ = 0 := by rw [h]; ring
  exact polar_one_add_ne_zero (curveR_pos hp1 hp2 hl hl1 hθ0 hθ) hθ0 hθ h0

/-- `w(θ)` lies in the upper half plane: `Im w = (1 - λ) R(θ) sin θ / |1 + z_θ|² > 0` (sec5 l.19, l.52). -/
theorem mobW_curveZ_im_pos (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) (hθ0 : 0 < θ)
    (hθ : θ < Real.pi) : 0 < (mobW lam (curveZ p lam θ)).im := by
  have hR := curveR_pos hp1 hp2 hl hl1 hθ0 hθ
  have him : (curveZ p lam θ).im = -(curveR p lam θ * Real.sin θ) := (polar_re_im (curveR p lam θ) θ).2
  have hn : 0 < ‖1 + curveZ p lam θ‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (polar_one_add_ne_zero hR hθ0 hθ)) 2
  have hnum : 0 < (1 - lam) * (curveR p lam θ * Real.sin θ) :=
    mul_pos (by linarith) (mul_pos hR (Real.sin_pos_of_pos_of_lt_pi hθ0 hθ))
  rw [mobW_im_norm, him, show -(1 - lam) * -(curveR p lam θ * Real.sin θ) =
    (1 - lam) * (curveR p lam θ * Real.sin θ) by ring]
  exact div_pos hnum hn

/-- `z_θ` determines `θ` on `(0, π)`: equal points have equal moduli `R`, then equal `cos θ`. -/
theorem curveZ_injOn (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    Set.InjOn (curveZ p lam) (Set.Ioo 0 Real.pi) := by
  intro θ1 h1 θ2 h2 hz
  have hR1 := curveR_pos hp1 hp2 hl hl1 h1.1 h1.2
  have hR2 := curveR_pos hp1 hp2 hl hl1 h2.1 h2.2
  have hn := congrArg Complex.normSq hz
  unfold curveZ at hn
  rw [polar_normSq, polar_normSq] at hn
  have hR : curveR p lam θ1 = curveR p lam θ2 := (pow_left_inj₀ hR1.le hR2.le two_ne_zero).1 hn
  have hre := congrArg Complex.re hz
  unfold curveZ at hre
  rw [(polar_re_im (curveR p lam θ1) θ1).1, (polar_re_im (curveR p lam θ2) θ2).1, hR] at hre
  exact Real.injOn_cos ⟨h1.1.le, h1.2.le⟩ ⟨h2.1.le, h2.2.le⟩ (mul_left_cancel₀ hR2.ne' hre)

end Curve

/-- A point of the upper half plane has its argument in `(0, π)`. -/
theorem arg_mem_Ioo_of_im_pos {w : ℂ} (hw : 0 < w.im) : Complex.arg w ∈ Set.Ioo 0 Real.pi := by
  refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.2 hw.le) fun h => ?_, Complex.arg_lt_pi_iff.2 (Or.inr hw.ne')⟩
  have := (Complex.arg_eq_zero_iff.1 h.symm).2
  linarith

/-- (A2), the text's own step, sec5_sharp_inequality.tex l.84-85: "ρ(θ) is continuous, injective by (A1)". If
`ρ(θ₁) = ρ(θ₂) = ρ`, then `w(θ₁)` and `w(θ₂)` lie on `|w| = ρ` in the upper half plane, so both are critical points
of `f_ρ` in `(0, π)` (the "if" half of `sec5_critical_points`, the leading hypothesis = that row's exact type). By
(A1) (`sec5_A1_proved`) their angles agree, so `w(θ₁) = w(θ₂)`; the Möbius map is injective (`mobW_bijOn`), so
`z_{θ₁} = z_{θ₂}`, and `z_θ = R(θ)e^{-iθ}` with `R > 0` gives `θ₁ = θ₂`. -/
theorem sec5_A2_injective_given
    (hcrit : ∀ {p lam ρ φ : ℝ}, 1 < p → p < 2 → -1 ≤ lam → lam < 1 → 0 < ρ → 0 < φ → φ < Real.pi →
      (deriv (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ = 0 ↔
        (∃ θ ∈ Set.Ioo 0 Real.pi, (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = mobW lam (curveZ p lam θ)) ∨
        (0 < lam ∧ ∃ θ ∈ Set.Ioo 0 Real.pi,
          (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = (lam : ℂ) / conj (mobW lam (curveZ p lam θ)))))
    {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    Set.InjOn (fun θ => ‖mobW lam (curveZ p lam θ)‖) (Set.Ioo 0 Real.pi) := by
  intro θ1 h1 θ2 h2 heq
  have hnorm : ‖mobW lam (curveZ p lam θ1)‖ = ‖mobW lam (curveZ p lam θ2)‖ := heq
  have him1 := mobW_curveZ_im_pos hp1 hp2 hl hl1 h1.1 h1.2
  have him2 := mobW_curveZ_im_pos hp1 hp2 hl hl1 h2.1 h2.2
  set w1 := mobW lam (curveZ p lam θ1) with hw1
  set w2 := mobW lam (curveZ p lam θ2) with hw2
  have hρ : 0 < ‖w1‖ := norm_pos_iff.2 fun h => by rw [h, Complex.zero_im] at him1; exact lt_irrefl 0 him1
  have ha1 := arg_mem_Ioo_of_im_pos him1
  have ha2 := arg_mem_Ioo_of_im_pos him2
  have hpol1 : ((‖w1‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg w1 : ℂ) * Complex.I) = w1 :=
    Complex.norm_mul_exp_arg_mul_I w1
  have hpol2 : ((‖w1‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg w2 : ℂ) * Complex.I) = w2 := by
    rw [hnorm]; exact Complex.norm_mul_exp_arg_mul_I w2
  have hd1 := (hcrit hp1 hp2 hl hl1 hρ ha1.1 ha1.2).2 (Or.inl ⟨θ1, h1, hpol1⟩)
  have hd2 := (hcrit hp1 hp2 hl hl1 hρ ha2.1 ha2.2).2 (Or.inl ⟨θ2, h2, hpol2⟩)
  have harg : Complex.arg w1 = Complex.arg w2 := sec5_A1_proved hp1 hp2 hl hl1 hρ ⟨ha1, hd1⟩ ⟨ha2, hd2⟩
  have hw : w1 = w2 := by rw [← hpol1, ← hpol2, harg]
  exact curveZ_injOn hp1 hp2 hl hl1 h1 h2
    ((mobW_bijOn hl1.ne).injOn (curveZ_ne hp1 hp2 hl hl1 h1.1 h1.2) (curveZ_ne hp1 hp2 hl hl1 h2.1 h2.2) hw)

end GKSharp.A2Injective
