/- GKSharp/Proofs/AngularContact.lean - the row angular_contact_determines_cos (sec4a_criterion.tex l.26-33): a
continuous q-trigonometrically convex minorant of m_GK forces K cos(q|t|) ≤ m_GK on [-π, π]. A corollary of the
installed arch_sinusoid_proved (arch form, l.26-27) and cosine_minorant_of_arch (tangency A = K and the tangent
sinusoid, l.28-33).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.Sec4aArch
import GKSharp.Proofs.CosineNecessity
import GKSharp.Proofs.PropositionQFull

namespace GKSharp

open Set Threshold

/-- sec4a_criterion.tex l.26-33: "φ(±θ₀) = 0, and on the arch [−θ₀, θ₀] ... φ = A cos(qt)"; "hence A = K"; "So
m_GK ≥ φ ≥ K cos(qt) on [θ₀, π], on the arch m_GK ≥ φ = K cos(qt), and the rest follows by evenness". -/
theorem angular_contact_determines_cos_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) (f : ℝ → ℝ)
    (hf : Continuous f) (hq : QTrigConvex (q p) f)
    (hminor : ∀ t : ℝ, f t ≤ Threshold.obstacle p lam t) :
    ∀ t ∈ Icc (-Real.pi) Real.pi, kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t := by
  obtain ⟨-, hfzero, aa, harch⟩ := arch_sinusoid_proved p lam hp hp2 hlam f hf hq hminor
  have htt0 : 0 < theta p := div_pos Real.pi_pos (by linarith)
  have htti : theta p < Real.pi := div_lt_self Real.pi_pos hp
  have hqtt : q p * theta p = Real.pi / 2 := by
    unfold q theta
    field_simp [show p ≠ 0 by linarith]
  have hmzero : Threshold.obstacle p lam (theta p) = 0 := by
    apply le_antisymm (sec4a_obstacle_contact_nonpos_Ico hp hp2 hlam rfl)
    rw [← hfzero]
    exact hminor _
  exact (cosine_minorant_of_arch (by unfold q; linarith) (by unfold q; linarith) htt0 htti hqtt hq harch hminor
    (obstacle_even_real p (gk p lam) lam) hmzero (obstacle_contact_hasDerivAt p lam hp hp2 hlam)).2

end GKSharp
