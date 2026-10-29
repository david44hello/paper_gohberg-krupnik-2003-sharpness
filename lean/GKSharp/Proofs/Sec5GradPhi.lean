/- on the critical curve the real gradient of Φ is q|Q|^{q-1}(2τ cos δ - 1)(K - K_f(θ)) v
(sec5_sharp_inequality.tex l.97-98, short v0.40). No cited input.
Copyright (C) Dave Goel 2026--now.

  The paper's step. On the critical curve w = w(z_θ) = τv with τ = |w|/|v| > 0 (dict_identities), Im w > 0, and
  arg Q(w) = θ (Q(w(z)) is a positive multiple of z̄ = R e^{iθ}: mobQ_mobW). So the gradients of the two parts of Φ
  (sec5_grad_parts, the RealGradients) are real multiples of v:
    ∇|w|^p = pρ^{p-2} τ v,   ∇Re Q^q = q|Q|^{q-1}(v - 2w cos δ) = q|Q|^{q-1}(1 - 2τ cos δ) v,
  and ∇Φ = -(1-λ)^p pρ^{p-2}τ v + K q|Q|^{q-1}(2τ cos δ - 1) v. The definition of K_f (Defs/CurveK), multiplied by
  E = 2τ cos δ - 1 (E > 0 by dict_identities: E = Y/(|1+z_θ|² sin δ), Y > 0), and |Q|^{q-1}|Q|^{1-q} = 1 turn the
  first term into -q|Q|^{q-1} E K_f v. -/
import GKSharp.Proofs.RealGradients
import GKSharp.Proofs.CurveDict
import GKSharp.Defs.CurveK

namespace GKSharp

namespace Sec5GradPhi

open ComplexConjugate

variable {p lam θ : ℝ}

/-- The scalar identity behind `∇Φ` on the critical curve, on plain reals: `E = 2τc - 1`,
`K_f E = 2(1-λ)^p ρ^{p-2} τ N^{1-q}`, `q = p/2`. -/
theorem scalar_key {K ρ τ N c Kf : ℝ} (hN : 0 < N)
    (hKf : Kf * (2 * τ * c - 1) = 2 * (1 - lam) ^ p * ρ ^ (p - 2) * τ * N ^ (1 - p / 2)) :
    p / 2 * N ^ (p / 2 - 1) * (2 * τ * c - 1) * (K - Kf) =
      -((1 - lam) ^ p * (p * ρ ^ (p - 2) * τ)) - K * (p / 2 * N ^ (p / 2 - 1) * (1 - 2 * τ * c)) := by
  have hNN : N ^ (p / 2 - 1) * N ^ (1 - p / 2) = 1 := by
    rw [← Real.rpow_add hN, show p / 2 - 1 + (1 - p / 2) = 0 by ring, Real.rpow_zero]
  linear_combination (-(p / 2 * N ^ (p / 2 - 1))) * hKf - (p * (1 - lam) ^ p * ρ ^ (p - 2) * τ) * hNN

/-- `conj z_θ = R(θ) e^{iθ}`. -/
theorem conj_curveZ (p lam θ : ℝ) :
    conj (curveZ p lam θ) = (curveR p lam θ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [curveZ, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal,
    Complex.conj_I, neg_mul_neg]

/-- The critical-curve facts: `w = τv` (`τ = |w|/|v|`), `Im w > 0`, `arg Q(w) = θ`, `|Q(w)| > 0`, `2τ cos δ - 1 > 0`. -/
theorem curve_facts (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) (hθ0 : 0 < θ)
    (hθ : θ < Real.pi) :
    let w := mobW lam (curveZ p lam θ)
    let τ := ‖w‖ / ‖curveV p lam θ‖
    w = (τ : ℂ) * curveV p lam θ ∧ 0 < w.im ∧ Complex.arg (mobQ lam w) = θ ∧ 0 < ‖mobQ lam w‖ ∧
      0 < 2 * τ * Real.cos ((1 - p / 2) * θ) - 1 := by
  intro w τ
  set r := curveR p lam θ with hr
  obtain ⟨hA, hQn, -, hw, h2τ, -, hYpos⟩ := dict_identities hp1 hp2 hl hl1 hθ0 hθ hr
  obtain ⟨-, -, hR0, -, -⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  rw [← hr] at hR0
  obtain ⟨hs1, -, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
  have hz1 : (1 : ℂ) + (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) ≠ 0 := polar_one_add_ne_zero hR0 hθ0 hθ
  have hApos : 0 < 1 + 2 * r * Real.cos θ + r ^ 2 := by rw [← hA]; exact pow_pos (norm_pos_iff.2 hz1) 2
  set τ0 := r * Real.sin θ / ((1 + 2 * r * Real.cos θ + r ^ 2) * Real.sin ((1 - p / 2) * θ)) with hτ0def
  have hτ0 : 0 < τ0 := div_pos (mul_pos hR0 hsθ) (mul_pos hApos hs1)
  have hwV0 : w = (τ0 : ℂ) * curveV p lam θ := hw
  have hVim : 0 < (curveV p lam θ).im := by
    rw [(curveV_re_im p lam θ).2]; exact mul_pos (by linarith) hs1
  have hV0 : 0 < ‖curveV p lam θ‖ :=
    norm_pos_iff.2 (fun h => by rw [h, Complex.zero_im] at hVim; exact lt_irrefl _ hVim)
  have hτ : τ = τ0 := by
    show ‖w‖ / ‖curveV p lam θ‖ = τ0
    rw [hwV0, norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ0.le, mul_div_assoc, div_self hV0.ne', mul_one]
  refine ⟨by rw [hτ]; exact hwV0, ?_, ?_, ?_, ?_⟩
  · rw [hwV0, Complex.im_ofReal_mul]; exact mul_pos hτ0 hVim
  · have hzne : curveZ p lam θ ≠ -1 := by
      intro h
      apply hz1
      show 1 + curveZ p lam θ = 0
      rw [h]; ring
    have hz1' : 0 < ‖1 + curveZ p lam θ‖ := norm_pos_iff.2 hz1
    have hcoef : 0 < (1 - lam) ^ 2 / ‖1 + curveZ p lam θ‖ ^ 2 * r :=
      mul_pos (div_pos (pow_pos (by linarith) 2) (pow_pos hz1' 2)) hR0
    have hQ : mobQ lam w = (((1 - lam) ^ 2 / ‖1 + curveZ p lam θ‖ ^ 2 * r : ℝ) : ℂ) *
        Complex.exp ((θ : ℂ) * Complex.I) := by
      show mobQ lam (mobW lam (curveZ p lam θ)) = _
      rw [mobQ_mobW lam hzne, conj_curveZ, ← hr]
      push_cast
      ring
    rw [hQ, Complex.arg_real_mul _ hcoef, Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], hθ.le⟩
  · show 0 < ‖mobQ lam (mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)))‖
    rw [hQn]
    exact div_pos (mul_pos (pow_pos (by linarith) 2) hR0) hApos
  · rw [hτ, h2τ]
    exact div_pos hYpos (mul_pos hApos hs1)

/-- **sec5_sharp_inequality.tex l.97-98**: on the critical curve `∇Φ(w(θ)) = q|Q|^{q-1}(2τ cos δ - 1)(K - K_f(θ)) v`
(real gradient on `ℂ`, `τ = |w|/|v|`, any `C` and `K`). -/
theorem sec5_grad_Phi_proved {C K : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    let w := mobW lam (curveZ p lam θ)
    let τ := ‖w‖ / ‖curveV p lam θ‖
    HasFDerivAt (mobPhi p C K lam)
      (innerSL ℝ ((((p / 2) * ‖mobQ lam w‖ ^ (p / 2 - 1) * (2 * τ * Real.cos ((1 - p / 2) * θ) - 1) *
        (K - curveKf p lam θ) : ℝ) : ℂ) * curveV p lam θ) : ℂ →L[ℝ] ℝ) w := by
  intro w τ
  have hf : w = (τ : ℂ) * curveV p lam θ ∧ 0 < w.im ∧ Complex.arg (mobQ lam w) = θ ∧ 0 < ‖mobQ lam w‖ ∧
      0 < 2 * τ * Real.cos ((1 - p / 2) * θ) - 1 := curve_facts hp1 hp2 hl hl1 hθ0 hθ
  obtain ⟨hwV, hwim, harg, hN, hE⟩ := hf
  obtain ⟨h1, h2⟩ := GKSharp.Proofs.RealGradients.sec5_grad_parts_proved hp1 hp2 hl hl1 hwim
  rw [harg] at h1
  set N := ‖mobQ lam w‖ with hNdef
  set ρ := ‖w‖ with hρdef
  set c := Real.cos ((1 - p / 2) * θ) with hcdef
  set V := curveV p lam θ with hVdef
  have hg1 : (((p / 2 * N ^ (p / 2 - 1) : ℝ) : ℂ) * (V - 2 * w * (c : ℂ))) =
      ((p / 2 * N ^ (p / 2 - 1) * (1 - 2 * τ * c) : ℝ) : ℂ) * V := by
    rw [hwV]; push_cast; ring
  have hg2 : ((p * ρ ^ (p - 2) : ℝ) : ℂ) * w = ((p * ρ ^ (p - 2) * τ : ℝ) : ℂ) * V := by
    rw [hwV]; push_cast; ring
  rw [hg1] at h1
  rw [hg2] at h2
  have hPhi : HasFDerivAt (mobPhi p C K lam)
      ((1 - lam) ^ p • -(innerSL ℝ (((p * ρ ^ (p - 2) * τ : ℝ) : ℂ) * V) : ℂ →L[ℝ] ℝ) -
        K • (innerSL ℝ (((p / 2 * N ^ (p / 2 - 1) * (1 - 2 * τ * c) : ℝ) : ℂ) * V) : ℂ →L[ℝ] ℝ)) w :=
    ((h2.const_sub (C ^ p)).const_mul ((1 - lam) ^ p)).sub (h1.const_mul K)
  have hKf : curveKf p lam θ * (2 * τ * c - 1) = 2 * (1 - lam) ^ p * ρ ^ (p - 2) * τ * N ^ (1 - p / 2) := by
    show (2 * (1 - lam) ^ p * ρ ^ (p - 2) * τ * N ^ (1 - p / 2) / (2 * τ * c - 1)) * (2 * τ * c - 1) = _
    exact div_mul_cancel₀ _ hE.ne'
  refine hPhi.congr_fderiv ?_
  rw [scalar_key hN hKf]
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [sub_apply, smul_apply, neg_apply,
    innerSL_apply_apply, smul_eq_mul, ← Complex.real_smul, real_inner_smul_left]
  ring

end Sec5GradPhi

end GKSharp
