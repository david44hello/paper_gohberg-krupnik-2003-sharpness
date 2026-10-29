/- complete Proposition Q and actual angular tangency.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.PropositionQ
import GKSharp.Proofs.ContactDtGamma
import GKSharp.Proofs.ContactObstacleSmooth
import GKSharp.Proofs.ContactOperator

namespace GKSharp
open Set Threshold
open scoped Topology ContDiff

theorem obstacle_smooth_contact_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) :
    ∃ eps > 0, ContDiffOn ℝ ∞ (Threshold.obstacle p lam)
      (Ioo (theta p - eps) (theta p + eps)) ∧
      deriv (Threshold.obstacle p lam) (theta p) = -q p * kConst p lam := by
  apply obstacle_smooth_contact_of_dt p lam hp hp2 hlam
  · exact fun hl => contact_dt_gamma p lam hp hp2 hl
  · intro heq
    subst lam
    exact endpoint_dt_gamma p hp hp2

theorem obstacle_contact_hasDerivAt (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) :
    HasDerivAt (Threshold.obstacle p lam) (-q p * kConst p lam) (theta p) := by
  obtain ⟨eps, heps, hreg, hd⟩ := obstacle_smooth_contact_proved p lam hp hp2 hlam
  have hat : ContDiffAt ℝ ∞ (Threshold.obstacle p lam) (theta p) :=
    hreg.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  have hh := (hat.differentiableAt (by simp)).hasDerivAt
  rwa [hd] at hh

/-- The full unchanged approved ClaimQ, expanded to avoid importing a proposal definition. -/
theorem sec4_prop_Q_proved (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) :
    1 < p → p < 2 → ∀ lam ∈ Ico (-1 : ℝ) 1,
      (pencilNorm P lam = gk p lam ↔
        ∀ t ∈ Icc (-Real.pi) Real.pi,
          kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t) ∧
      (pencilNorm P lam = gk p lam ↔
        ∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) := by
  intro hp hp2 lam hlam
  exact proposition_Q_of_contact P hp hp2 hlam (contact_kConst_pos p lam hp hp2 hlam).le
    (gk_le_pencilNorm_real p P hp hp2 lam hlam) (obstacle_contact_hasDerivAt p lam hp hp2 hlam)

/-- The printed coefficient and right derivative, proved by the stronger two-sided squeeze. -/
theorem sec4_angular_tangency_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) (ff : ℝ → ℝ) (hf : QSubtrig (q p) ff)
    (hminor : ∀ t, ff t ≤ Threshold.obstacle p lam t) (aa : ℝ)
    (harch : ∀ t ∈ Icc (-theta p) (theta p), ff t = aa * Real.cos (q p * t)) :
    aa = kConst p lam ∧
      HasDerivWithinAt ff (-(kConst p lam) * q p) (Ici (theta p)) (theta p) := by
  have hconv := (TheoremRIf.qsub_continuous_trigconvex_proved (q p)
    (by unfold q; linarith) ff hf).2
  have htt0 : 0 < theta p := div_pos Real.pi_pos (by linarith)
  have htti : theta p < Real.pi := div_lt_self Real.pi_pos hp
  have hqtt : q p * theta p = Real.pi / 2 := by
    unfold q theta
    field_simp [show p ≠ 0 by linarith]
  have hfzero : ff (theta p) = 0 := by
    rw [harch (theta p) ⟨by linarith, le_rfl⟩, hqtt, Real.cos_pi_div_two, mul_zero]
  have hmzero : Threshold.obstacle p lam (theta p) = 0 := by
    apply le_antisymm (sec4a_obstacle_contact_nonpos_Ico hp hp2 hlam rfl)
    rw [← hfzero]
    exact hminor _
  obtain ⟨heq, hd⟩ := cosine_tangent_derivative_of_arch
    (by unfold q; linarith) (by unfold q; linarith) htt0 htti hqtt hconv harch hminor
    (obstacle_even_real p (gk p lam) lam) hmzero (obstacle_contact_hasDerivAt p lam hp hp2 hlam)
  exact ⟨heq, hd.hasDerivWithinAt⟩

end GKSharp

#print axioms GKSharp.obstacle_smooth_contact_proved
#print axioms GKSharp.sec4_prop_Q_proved
#print axioms GKSharp.sec4_angular_tangency_proved
