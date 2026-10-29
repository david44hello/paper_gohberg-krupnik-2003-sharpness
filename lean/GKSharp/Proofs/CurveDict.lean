/- GKSharp/Proofs/CurveDict.lean - the dictionary (5.5) on the critical curve: |Q|, rho^2, w = tau v with the explicit
tau, 2 tau cos(delta) - 1 = Y/(A s1), and Y = (1 - lam) r (s2 - r s1) > 0 (sec5_sharp_inequality.tex l.53-58).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MobiusDict

namespace GKSharp

open ComplexConjugate

/-- (5.5), sec5_sharp_inequality.tex l.53-58: on the critical curve, with `r = R(θ)`, `z = r e^{−iθ}`,
`A = |1 + z|² = 1 + 2r cos θ + r²`, `B = |1 + λz|²`: `|Q| = (1−λ)² r/A`, `ρ² = B/A`, `w = τ v` with
`τ = r sin θ/(A s₁)`, `2τ cos δ − 1 = Y/(A s₁)`, `Y := 2rs₂ − (1 + r²)s₁ = (1−λ) r (s₂ − rs₁) > 0`. -/
theorem dict_identities {p lam θ r : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) (hr : r = curveR p lam θ) :
    ‖1 + (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)‖ ^ 2 = 1 + 2 * r * Real.cos θ + r ^ 2 ∧
    ‖mobQ lam (mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)))‖ =
      (1 - lam) ^ 2 * r / (1 + 2 * r * Real.cos θ + r ^ 2) ∧
    ‖mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I))‖ ^ 2 =
      ‖1 + (lam : ℂ) * ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I))‖ ^ 2 / (1 + 2 * r * Real.cos θ + r ^ 2) ∧
    mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)) =
      ((r * Real.sin θ / ((1 + 2 * r * Real.cos θ + r ^ 2) * Real.sin ((1 - p / 2) * θ)) : ℝ) : ℂ) *
        curveV p lam θ ∧
    2 * (r * Real.sin θ / ((1 + 2 * r * Real.cos θ + r ^ 2) * Real.sin ((1 - p / 2) * θ))) *
        Real.cos ((1 - p / 2) * θ) - 1 =
      (2 * r * Real.sin (p / 2 * θ) - (1 + r ^ 2) * Real.sin ((1 - p / 2) * θ)) /
        ((1 + 2 * r * Real.cos θ + r ^ 2) * Real.sin ((1 - p / 2) * θ)) ∧
    2 * r * Real.sin (p / 2 * θ) - (1 + r ^ 2) * Real.sin ((1 - p / 2) * θ) =
      (1 - lam) * r * (Real.sin (p / 2 * θ) - r * Real.sin ((1 - p / 2) * θ)) ∧
    0 < 2 * r * Real.sin (p / 2 * θ) - (1 + r ^ 2) * Real.sin ((1 - p / 2) * θ) := by
  obtain ⟨-, -, hR0, hR1, hDR⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  obtain ⟨hs1, hs12, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  rw [← hr] at hR0 hR1 hDR
  set z := (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) with hzdef
  obtain ⟨hzr, hzi⟩ := polar_re_im r θ
  rw [← hzdef] at hzr hzi
  have hns := polar_normSq r θ
  rw [← hzdef] at hns
  have hz1 : (1 : ℂ) + z ≠ 0 := polar_one_add_ne_zero hR0 hθ0 hθ
  have hz : z ≠ -1 := by intro h; apply hz1; rw [h]; ring
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
  have hAn : Complex.normSq (1 + z) = 1 + 2 * r * Real.cos θ + r ^ 2 := by
    rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, hzr, hzi]
    linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ
  have hA : ‖1 + z‖ ^ 2 = 1 + 2 * r * Real.cos θ + r ^ 2 := by rw [Complex.sq_norm, hAn]
  have hApos : 0 < 1 + 2 * r * Real.cos θ + r ^ 2 := by rw [← hAn]; exact Complex.normSq_pos.2 hz1
  have hnz : ‖z‖ = r := by
    have h2 : ‖z‖ ^ 2 = r ^ 2 := by rw [Complex.sq_norm, hns]
    exact (pow_left_inj₀ (norm_nonneg _) hR0.le two_ne_zero).1 h2
  have hsin := sin_q_eq p θ
  have hD : (1 + lam) * r * (Real.sin θ * Real.cos ((1 - p / 2) * θ) -
      Real.cos θ * Real.sin ((1 - p / 2) * θ)) - (1 + lam * r ^ 2) * Real.sin ((1 - p / 2) * θ) = 0 := by
    have := hDR; unfold curveD at this; rw [hsin] at this; linarith
  obtain ⟨hvr, hvi⟩ := curveV_re_im p lam θ
  have hY : 2 * r * Real.sin (p / 2 * θ) - (1 + r ^ 2) * Real.sin ((1 - p / 2) * θ) =
      (1 - lam) * r * (Real.sin (p / 2 * θ) - r * Real.sin ((1 - p / 2) * θ)) := by
    unfold curveD at hDR; linear_combination hDR
  have hA0 : (1 + 2 * r * Real.cos θ + r ^ 2) ≠ 0 := hApos.ne'
  have hs10 : Real.sin ((1 - p / 2) * θ) ≠ 0 := hs1.ne'
  refine ⟨hA, ?_, ?_, ?_, ?_, hY, ?_⟩
  · rw [mobQ_mobW lam hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj, hnz, hA,
      abs_of_nonneg (by positivity)]
    ring
  · unfold mobW
    rw [norm_div, div_pow, hA]
  · apply Complex.ext
    · rw [Complex.re_ofReal_mul, hvr, mobW_re, hzr, hns, hAn]
      set s1 := Real.sin ((1 - p / 2) * θ)
      set c1 := Real.cos ((1 - p / 2) * θ)
      rw [div_mul_eq_mul_div, div_eq_div_iff hA0 (mul_ne_zero hA0 hs10)]
      linear_combination (-(1 + 2 * r * Real.cos θ + r ^ 2)) * hD
    · rw [Complex.im_ofReal_mul, hvi, mobW_im, hzi, hAn]
      set s1 := Real.sin ((1 - p / 2) * θ)
      rw [div_mul_eq_mul_div, div_eq_div_iff hA0 (mul_ne_zero hA0 hs10)]
      ring
  · rw [hsin]
    set s1 := Real.sin ((1 - p / 2) * θ)
    set c1 := Real.cos ((1 - p / 2) * θ)
    rw [eq_div_iff (mul_ne_zero hA0 hs10)]
    field_simp
    ring
  · have h1 : 0 < Real.sin (p / 2 * θ) - r * Real.sin ((1 - p / 2) * θ) := by nlinarith
    rw [hY]
    exact mul_pos (mul_pos (by linarith) hR0) h1

end GKSharp
