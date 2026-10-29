/- (5.8), the derivative of Φ along the critical curve (sec5_sharp_inequality.tex l.101-104, short v0.40):
d/dθ Φ(w(θ)) = Re(conj(∇Φ) w′) = q|Q|^{q-1}(2τ cos δ - 1)(ρρ′/τ)(K - K_f(θ)). No cited input.
Copyright (C) Dave Goel 2026--now.

  The paper's step. Chain rule (HasFDerivAt.comp_hasDerivAt) with ∇Φ(w(θ)) = S v, S = q|Q|^{q-1} E (K - K_f)
  (sec5_grad_Phi): the derivative is ⟪S v, w′⟫ = S Re(v̄ w′) = S (ρ²)′/(2τ) (sec5_re_vbar_wprime) = S ρρ′/τ, with
  (ρ²)′ = 2ρρ′ (ρ = |w(θ)| is differentiable since w(θ) ≠ 0). F = q|Q|^{q-1} E ρρ′/τ is positive because |Q| > 0,
  E > 0 (Sec5GradPhi.curve_facts), ρ, τ > 0 and ρ′ > 0, which is (A2) (row sec5_A2): here it is the explicit
  premise `hA2`; the row eq_5_8 follows by passing sec5_A2's derivative conjunct. -/
import GKSharp.Proofs.Sec5GradPhi
import GKSharp.Proofs.Sec5ReVbar

namespace GKSharp

namespace Sec5Eq58

open ComplexConjugate

variable {p lam θ : ℝ}

/-- The derivative identity of (5.8) (no sign claim): `d/dθ Φ(w(θ)) = F (K - K_f(θ))`. -/
theorem eq_5_8_hasDerivAt {C K : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    let w := mobW lam (curveZ p lam θ)
    let τ := ‖w‖ / ‖curveV p lam θ‖
    let F := p / 2 * ‖mobQ lam w‖ ^ (p / 2 - 1) * (2 * τ * Real.cos ((1 - p / 2) * θ) - 1) *
      (‖w‖ * deriv (fun x => ‖mobW lam (curveZ p lam x)‖) θ / τ)
    HasDerivAt (fun x => mobPhi p C K lam (mobW lam (curveZ p lam x))) (F * (K - curveKf p lam θ)) θ ∧
      0 < ‖w‖ ∧ 0 < τ := by
  intro w τ F
  have hf : w = (τ : ℂ) * curveV p lam θ ∧ 0 < w.im ∧ Complex.arg (mobQ lam w) = θ ∧ 0 < ‖mobQ lam w‖ ∧
      0 < 2 * τ * Real.cos ((1 - p / 2) * θ) - 1 := Sec5GradPhi.curve_facts hp1 hp2 hl hl1 hθ0 hθ
  obtain ⟨hwV, hwim, -, -, -⟩ := hf
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_im] at hwim; exact lt_irrefl _ hwim
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hV0 : curveV p lam θ ≠ 0 := fun h => hw0 (by rw [hwV, h, mul_zero])
  have hτ : 0 < τ := div_pos hwn (norm_pos_iff.2 hV0)
  have hgrad : HasFDerivAt (mobPhi p C K lam)
      (innerSL ℝ ((((p / 2) * ‖mobQ lam w‖ ^ (p / 2 - 1) * (2 * τ * Real.cos ((1 - p / 2) * θ) - 1) *
        (K - curveKf p lam θ) : ℝ) : ℂ) * curveV p lam θ) : ℂ →L[ℝ] ℝ) w :=
    Sec5GradPhi.sec5_grad_Phi_proved hp1 hp2 hl hl1 hθ0 hθ
  have hre : DifferentiableAt ℝ (fun x => mobW lam (curveZ p lam x)) θ ∧
      (conj (curveV p lam θ) * deriv (fun x => mobW lam (curveZ p lam x)) θ).re =
        deriv (fun x => ‖mobW lam (curveZ p lam x)‖ ^ 2) θ / (2 * τ) :=
    Sec5ReVbar.sec5_re_vbar_wprime_proved hp1 hp2 hl hl1 hθ0 hθ
  obtain ⟨hWd, hRe⟩ := hre
  have hρd : DifferentiableAt ℝ (fun x => ‖mobW lam (curveZ p lam x)‖) θ := hWd.norm ℝ hw0
  have hsq : deriv (fun x => ‖mobW lam (curveZ p lam x)‖ ^ 2) θ =
      2 * ‖w‖ * deriv (fun x => ‖mobW lam (curveZ p lam x)‖) θ := by
    show deriv ((fun x => ‖mobW lam (curveZ p lam x)‖) ^ 2) θ = _
    rw [(hρd.hasDerivAt.pow 2).deriv]
    push_cast
    ring
  have hchain := hgrad.comp_hasDerivAt θ hWd.hasDerivAt
  refine ⟨hchain.congr_deriv ?_, hwn, hτ⟩
  set S := (p / 2) * ‖mobQ lam w‖ ^ (p / 2 - 1) * (2 * τ * Real.cos ((1 - p / 2) * θ) - 1) *
    (K - curveKf p lam θ) with hS
  rw [innerSL_apply_apply, ← Complex.real_smul, real_inner_smul_left, Complex.inner, mul_comm _ (conj _), hRe,
    hsq]
  show S * (2 * ‖w‖ * deriv (fun x => ‖mobW lam (curveZ p lam x)‖) θ / (2 * τ)) =
    p / 2 * ‖mobQ lam w‖ ^ (p / 2 - 1) * (2 * τ * Real.cos ((1 - p / 2) * θ) - 1) *
      (‖w‖ * deriv (fun x => ‖mobW lam (curveZ p lam x)‖) θ / τ) * (K - curveKf p lam θ)
  rw [hS]
  field_simp

/-- **(5.8)**, sec5_sharp_inequality.tex l.101-104, GIVEN `ρ′(θ) > 0` (consequence (A2), row sec5_A2): the derivative
identity for `Φ(w(θ))` and for `Λ = Φ(w(θ))/(1-λ)^p`, with the positive factors `F` and `F/(1-λ)^p`. -/
theorem eq_5_8_of_rho_deriv_pos {C K : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) (hA2 : 0 < deriv (fun x => ‖mobW lam (curveZ p lam x)‖) θ) :
    let w := mobW lam (curveZ p lam θ)
    let τ := ‖w‖ / ‖curveV p lam θ‖
    let F := p / 2 * ‖mobQ lam w‖ ^ (p / 2 - 1) * (2 * τ * Real.cos ((1 - p / 2) * θ) - 1) *
      (‖w‖ * deriv (fun x => ‖mobW lam (curveZ p lam x)‖) θ / τ)
    HasDerivAt (fun x => mobPhi p C K lam (mobW lam (curveZ p lam x))) (F * (K - curveKf p lam θ)) θ ∧ 0 < F ∧
    HasDerivAt (fun x => mobPhi p C K lam (mobW lam (curveZ p lam x)) / (1 - lam) ^ p)
      (F / (1 - lam) ^ p * (K - curveKf p lam θ)) θ ∧ 0 < F / (1 - lam) ^ p := by
  intro w τ F
  have hd : HasDerivAt (fun x => mobPhi p C K lam (mobW lam (curveZ p lam x))) (F * (K - curveKf p lam θ)) θ ∧
      0 < ‖w‖ ∧ 0 < τ := eq_5_8_hasDerivAt hp1 hp2 hl hl1 hθ0 hθ
  obtain ⟨hD, hwn, hτ⟩ := hd
  have hf : w = (τ : ℂ) * curveV p lam θ ∧ 0 < w.im ∧ Complex.arg (mobQ lam w) = θ ∧ 0 < ‖mobQ lam w‖ ∧
      0 < 2 * τ * Real.cos ((1 - p / 2) * θ) - 1 := Sec5GradPhi.curve_facts hp1 hp2 hl hl1 hθ0 hθ
  obtain ⟨-, -, -, hN, hE⟩ := hf
  have hF : 0 < F :=
    mul_pos (mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hN _)) hE) (div_pos (mul_pos hwn hA2) hτ)
  have hc : 0 < (1 - lam) ^ p := Real.rpow_pos_of_pos (by linarith) p
  refine ⟨hD, hF, (hD.div_const ((1 - lam) ^ p)).congr_deriv (by ring), div_pos hF hc⟩

end Sec5Eq58

end GKSharp
