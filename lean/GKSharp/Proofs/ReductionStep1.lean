/- Proposition (Reduction), Step 1 (sec5_sharp_inequality.tex l.143-145, short v0.70): "Λ decreases strictly
on (0, θ₀] and increases strictly on [θ₀, π). So Λ(θ) > Λ(θ₀) = 0 for θ ≠ θ₀, Λ(0⁺) > 0 exists, and
Φ(ρ₀) = (1−λ)^pΛ(0⁺) > 0". No cited input.
Copyright (C) Dave Goel 2026--now.

  The text's step, on f(θ) = Φ(w(θ)) = (1-λ)^p Λ(θ) (C = GK_p(λ), K of eq:K, θ₀ = π/p). By (5.8), f′ = F (K - K_f),
  F > 0. K_f is strictly decreasing (the premise hdec: Lemma B, or its λ = -1 case) with K_f(θ₀) = K (lemma_contact), so
  f′ < 0 on (0, θ₀) and f′ > 0 on (θ₀, π); f(θ₀) = 0 (lemma_contact + sec5_Lambda). The derivative signs give strict
  monotonicity on (0, θ₀] and [θ₀, π) (Mathlib strictAntiOn_of_deriv_neg / strictMonoOn_of_deriv_pos). For Φ(ρ₀):
  f(θ) > f(θ₀/2) > 0 for θ < θ₀/2; Φ is continuous (reQPow_continuous) and w(θ) → ρ₀, so Φ(ρ₀) ≥ f(θ₀/2) > 0. -/
import GKSharp.Proofs.Sec5Eq58
import GKSharp.Proofs.Contact
import GKSharp.Proofs.Sec5Lambda
import GKSharp.Proofs.Sec4aBasic

open Filter Topology Set

namespace GKSharp

namespace ReductionStep1

/-- `Φ` is continuous on `ℂ` (`p > 0`). -/
theorem mobPhi_continuous {p : ℝ} (hp : 0 < p) (C K lam : ℝ) : Continuous (mobPhi p C K lam) := by
  have hQ : Continuous (mobQ lam) := by
    show Continuous (fun w : ℂ => (w - (lam : ℂ)) * (1 - (starRingEnd ℂ) w))
    exact (continuous_id.sub continuous_const).mul (continuous_const.sub Complex.continuous_conj)
  have hN : Continuous (fun w : ℂ => ‖w‖ ^ p) := continuous_norm.rpow_const (fun _ => Or.inr hp.le)
  show Continuous (fun w : ℂ => (1 - lam) ^ p * (C ^ p - ‖w‖ ^ p) - K * reQPow (mobQ lam w) (p / 2))
  exact (continuous_const.mul (continuous_const.sub hN)).sub
    (continuous_const.mul ((reQPow_continuous_proved (p / 2) (by linarith)).comp hQ))

/-- **Step 1** of Proposition (Reduction), with the premises `ρ′ > 0` on `(0, π)` ((A2)) and `w(θ) → ρ₀` as `θ → 0⁺`. -/
theorem reduction_step1_of {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hdec : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi))
    (hA2 : ∀ θ ∈ Set.Ioo 0 Real.pi, 0 < deriv (fun x => ‖mobW lam (curveZ p lam x)‖) θ)
    (hlim : Tendsto (fun θ => mobW lam (curveZ p lam θ)) (𝓝[>] 0)
      (𝓝 ((((1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) : ℝ)) : ℂ))) :
    (∀ θ ∈ Set.Ioo 0 Real.pi, θ ≠ Real.pi / p →
      0 < mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam θ))) ∧
    0 < mobPhi p (gk p lam) (kConst p lam) lam
      ((((1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) : ℝ)) : ℂ) := by
  set f : ℝ → ℝ := fun θ => mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam θ)) with hfdef
  obtain ⟨hθ0, hθπ, -, -⟩ := theta0_bounds hp1 hp2
  -- (5.8): f′ = F (K - K_f), F > 0
  have hD : ∀ θ ∈ Ioo 0 Real.pi, ∃ F : ℝ, 0 < F ∧ HasDerivAt f (F * (kConst p lam - curveKf p lam θ)) θ := by
    intro θ hθ
    obtain ⟨hd, hF, -, -⟩ := Sec5Eq58.eq_5_8_of_rho_deriv_pos (C := gk p lam) (K := kConst p lam) hp1 hp2 hl hl1
      hθ.1 hθ.2 (hA2 θ hθ)
    exact ⟨_, hF, hd⟩
  have hcont : ∀ θ ∈ Ioo 0 Real.pi, ContinuousAt f θ := fun θ hθ => by
    obtain ⟨F, -, hd⟩ := hD θ hθ
    exact hd.continuousAt
  have hderiv : ∀ θ ∈ Ioo 0 Real.pi, ∃ F : ℝ, 0 < F ∧ deriv f θ = F * (kConst p lam - curveKf p lam θ) :=
    fun θ hθ => by
      obtain ⟨F, hF, hd⟩ := hD θ hθ
      exact ⟨F, hF, hd.deriv⟩
  -- the contact point: K_f(θ₀) = K and f(θ₀) = 0
  have hK : curveKf p lam (Real.pi / p) = kConst p lam := contact_Kf hp1 hp2 hl hl1
  have hf0 : f (Real.pi / p) = 0 := by
    have h1 := (Proofs.Sec5Lambda.sec5_Lambda_proved (C := gk p lam) (K := kConst p lam) hp1 hp2 hl hl1 hθ0 hθπ).2
    rw [contact_Lambda hp1 hp2 hl hl1 (kConst p lam), zero_div] at h1
    have hc : (1 - lam) ^ p ≠ 0 := (Real.rpow_pos_of_pos (by linarith) p).ne'
    exact (div_eq_zero_iff.mp h1).resolve_right hc
  -- strictly decreasing on (0, θ₀], strictly increasing on [θ₀, π)
  have hsub1 : Ioc 0 (Real.pi / p) ⊆ Ioo 0 Real.pi := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hθπ⟩
  have hanti : StrictAntiOn f (Ioc 0 (Real.pi / p)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioc 0 _) (fun x hx => (hcont x (hsub1 hx)).continuousWithinAt) ?_
    intro x hx
    rw [interior_Ioc] at hx
    obtain ⟨F, hF, hdx⟩ := hderiv x ⟨hx.1, hx.2.trans hθπ⟩
    rw [hdx]
    have hlt : kConst p lam < curveKf p lam x := by
      rw [← hK]
      exact hdec ⟨hx.1, hx.2.trans hθπ⟩ ⟨hθ0, hθπ⟩ hx.2
    exact mul_neg_of_pos_of_neg hF (by linarith)
  have hsub2 : Ico (Real.pi / p) Real.pi ⊆ Ioo 0 Real.pi := fun x hx => ⟨hθ0.trans_le hx.1, hx.2⟩
  have hmono : StrictMonoOn f (Ico (Real.pi / p) Real.pi) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico _ _) (fun x hx => (hcont x (hsub2 hx)).continuousWithinAt) ?_
    intro x hx
    rw [interior_Ico] at hx
    obtain ⟨F, hF, hdx⟩ := hderiv x ⟨hθ0.trans hx.1, hx.2⟩
    rw [hdx]
    have hlt : curveKf p lam x < kConst p lam := by
      rw [← hK]
      exact hdec ⟨hθ0, hθπ⟩ ⟨hθ0.trans hx.1, hx.2⟩ hx.1
    exact mul_pos hF (by linarith)
  -- Λ(θ) > Λ(θ₀) = 0 for θ ≠ θ₀
  have hpos : ∀ θ ∈ Ioo 0 Real.pi, θ ≠ Real.pi / p → 0 < f θ := by
    intro θ hθ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := hanti ⟨hθ.1, hlt.le⟩ ⟨hθ0, le_rfl⟩ hlt
      rwa [hf0] at h
    · have h := hmono ⟨le_rfl, hθπ⟩ ⟨hgt.le, hθ.2⟩ hgt
      rwa [hf0] at h
  refine ⟨hpos, ?_⟩
  -- Φ(ρ₀) ≥ f(θ₀/2) > 0
  have hθ1lt : Real.pi / p / 2 < Real.pi / p := half_lt_self hθ0
  have hf1 : 0 < f (Real.pi / p / 2) := hpos _ ⟨half_pos hθ0, hθ1lt.trans hθπ⟩ hθ1lt.ne
  have hlimf := ((mobPhi_continuous (p := p) (by linarith) (gk p lam) (kConst p lam) lam).tendsto _).comp hlim
  have hev : ∀ᶠ θ in 𝓝[>] 0, f (Real.pi / p / 2) ≤ f θ := by
    filter_upwards [Ioo_mem_nhdsGT (half_pos hθ0)] with θ hθ
    exact (hanti ⟨hθ.1, (hθ.2.trans hθ1lt).le⟩ ⟨half_pos hθ0, hθ1lt.le⟩ hθ.2).le
  exact hf1.trans_le (ge_of_tendsto hlimf hev)

end ReductionStep1

end GKSharp
