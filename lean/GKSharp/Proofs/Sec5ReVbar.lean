/- on the critical curve, Re(v̄ w′) = (ρ²)′/(2τ) (sec5_sharp_inequality.tex l.101, short v0.40). No cited input.
Copyright (C) Dave Goel 2026--now.

  The paper's step: on the critical curve w(θ) = τ v(θ) with τ = ρ/|v| > 0 real (critical_iff at r = R(θ), a root of
  D(θ, ·) by curveRoot_isRoot, which holds for λ = -1 too). Then (ρ²)′ = (|w|²)′ = 2 Re(w̄ w′) = 2τ Re(v̄ w′).
  Differentiability: R is analytic (curve_root_analytic), z_θ = R(θ) e^{-iθ}, and 1 + z_θ ≠ 0 (Im z_θ = -R sin θ < 0). -/
import GKSharp.Proofs.CriticalCurve
import GKSharp.Proofs.MobiusDict

namespace GKSharp

namespace Sec5ReVbar

open ComplexConjugate

variable {p lam θ : ℝ}

/-- `Im z_θ = -R(θ) sin θ`. -/
lemma curveZ_im (p lam θ : ℝ) : (curveZ p lam θ).im = -(curveR p lam θ * Real.sin θ) := by
  rw [curveZ, show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  ring

/-- `1 + z_θ ≠ 0` for `R(θ) > 0`, `0 < θ < π`. -/
lemma one_add_curveZ_ne_zero (hR : 0 < curveR p lam θ) (hθ0 : 0 < θ) (hθ : θ < Real.pi) : 1 + curveZ p lam θ ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  rw [Complex.add_im, Complex.one_im, zero_add, curveZ_im, Complex.zero_im] at him
  have := mul_pos hR (Real.sin_pos_of_pos_of_lt_pi hθ0 hθ)
  linarith

/-- `x ↦ z_x` is differentiable at `θ`. -/
lemma curveZ_differentiableAt (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) (hθ0 : 0 < θ)
    (hθ : θ < Real.pi) : DifferentiableAt ℝ (fun x => curveZ p lam x) θ := by
  have hR : DifferentiableAt ℝ (curveR p lam) θ := (curve_root_analytic hp1 hp2 hl hl1 hθ0 hθ).differentiableAt
  have h1 : DifferentiableAt ℝ (fun x : ℝ => ((curveR p lam x : ℝ) : ℂ)) θ :=
    Complex.ofRealCLM.differentiableAt.comp θ hR
  have h2 : DifferentiableAt ℝ (fun x : ℝ => Complex.exp (-(x : ℂ) * Complex.I)) θ := by
    have h3 : DifferentiableAt ℝ (fun x : ℝ => -((x : ℂ)) * Complex.I) θ :=
      (Complex.ofRealCLM.differentiableAt.neg).mul_const _
    exact h3.cexp
  exact h1.mul h2

/-- `mobW λ` is complex differentiable where `1 + z ≠ 0`. -/
lemma mobW_differentiableAt (lam : ℝ) {z : ℂ} (hz : 1 + z ≠ 0) : DifferentiableAt ℂ (mobW lam) z :=
  ((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)).div
    ((differentiableAt_const _).add differentiableAt_id) hz

/-- **sec5_sharp_inequality.tex l.101**: `Re(v̄ w′) = (ρ²)′/(2τ)` on the critical curve, `w = w(θ)`, `ρ = |w(θ)|`,
`τ = ρ/|v|` (and `w(θ)` is differentiable). -/
theorem sec5_re_vbar_wprime_proved (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    let τ := ‖mobW lam (curveZ p lam θ)‖ / ‖curveV p lam θ‖
    DifferentiableAt ℝ (fun x => mobW lam (curveZ p lam x)) θ ∧
    (conj (curveV p lam θ) * deriv (fun x => mobW lam (curveZ p lam x)) θ).re =
      deriv (fun x => ‖mobW lam (curveZ p lam x)‖ ^ 2) θ / (2 * τ) := by
  intro τ
  obtain ⟨hs1, hs12, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  have hR0 : 0 < curveR p lam θ := curveRoot_pos hl hl1 hs1 hs12.le
  have hD : curveD p lam θ (curveR p lam θ) = 0 := curveRoot_isRoot hl hl1 hs1 hs12.le
  obtain ⟨τ0, hτ0, hWV⟩ := (critical_iff hp1 hp2 hl1 hθ0 hθ hR0).mpr hD
  have hWV' : mobW lam (curveZ p lam θ) = (τ0 : ℂ) * curveV p lam θ := hWV
  have hV0 : curveV p lam θ ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    rw [(curveV_re_im p lam θ).2, Complex.zero_im] at him
    have := mul_pos (by linarith : (0:ℝ) < 1 - lam) hs1
    linarith
  have hVn : 0 < ‖curveV p lam θ‖ := norm_pos_iff.mpr hV0
  have hτ : τ = τ0 := by
    show ‖mobW lam (curveZ p lam θ)‖ / ‖curveV p lam θ‖ = τ0
    rw [hWV', norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ0.le, mul_div_assoc, div_self hVn.ne', mul_one]
  have hWd : DifferentiableAt ℝ (fun x => mobW lam (curveZ p lam x)) θ :=
    ((mobW_differentiableAt lam (one_add_curveZ_ne_zero hR0 hθ0 hθ)).restrictScalars ℝ).comp θ
      (curveZ_differentiableAt hp1 hp2 hl hl1 hθ0 hθ)
  refine ⟨hWd, ?_⟩
  set W' := deriv (fun x => mobW lam (curveZ p lam x)) θ with hW'
  have hder := hWd.hasDerivAt.norm_sq
  rw [hder.deriv, Complex.inner, hWV', map_mul, Complex.conj_ofReal, hτ]
  have e : (W' * ((τ0 : ℂ) * conj (curveV p lam θ))).re = τ0 * (conj (curveV p lam θ) * W').re := by
    rw [show W' * ((τ0 : ℂ) * conj (curveV p lam θ)) = (τ0 : ℂ) * (conj (curveV p lam θ) * W') by ring,
      Complex.re_ofReal_mul]
  rw [e]
  field_simp

end Sec5ReVbar

end GKSharp
