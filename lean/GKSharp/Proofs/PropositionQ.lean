/- Proposition Q assembly over the actual Riesz-projection pencil.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.CosineNecessity
import GKSharp.Proofs.CosineCriterion
import GKSharp.Proofs.TheoremR
import GKSharp.Proofs.TheoremRIf

namespace GKSharp
open Set Threshold

lemma obstacle_arg_unitPoint (p C : ℝ) (rho : ℂ) (t : ℝ) :
    GKSharp.obstacle p C rho (Complex.arg (unitPoint t)) = GKSharp.obstacle p C rho t := by
  unfold GKSharp.obstacle
  congr 1
  apply congrArg Set.range
  funext y
  rw [gamma_radial, gamma_radial, unitPoint_arg]

theorem cosine_necessary_of_norm_le {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (P : RieszProjection p) {lam : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1)
    (hderiv : HasDerivAt (Threshold.obstacle p lam) (-q p * kConst p lam) (theta p))
    (hnorm : pencilNorm P lam ≤ gk p lam) :
    ∀ t ∈ Icc (-Real.pi) Real.pi,
      kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t := by
  have hC : max 1 ‖(lam : ℂ)‖ < gk p lam := gk_gt_max hp (ne_of_lt hp2) (by
    intro heq
    have : lam = 1 := by exact_mod_cast heq
    linarith [hlam.2])
  obtain ⟨ff, hf, hminor⟩ := thmR_only_if hp P (lam : ℂ) hC hnorm
  obtain ⟨hcont, hconv⟩ := TheoremRIf.qsub_continuous_trigconvex_proved (q p)
    (by unfold q; linarith) ff hf
  obtain ⟨_, hfzero, AA, harch⟩ := arch_sinusoid_proved p lam hp hp2 hlam ff hcont hconv hminor
  have htt0 : 0 < theta p := div_pos Real.pi_pos (by linarith)
  have htti : theta p < Real.pi := div_lt_self Real.pi_pos hp
  have hqtt : q p * theta p = Real.pi / 2 := by
    unfold q theta
    field_simp [show p ≠ 0 by linarith]
  have hmzero : Threshold.obstacle p lam (theta p) = 0 := by
    apply le_antisymm (sec4a_obstacle_contact_nonpos_Ico hp hp2 hlam rfl)
    rw [← hfzero]
    exact hminor _
  exact (cosine_minorant_of_arch (by unfold q; linarith) (by unfold q; linarith)
    htt0 htti hqtt hconv harch hminor
    (obstacle_even_real p (gk p lam) lam) hmzero hderiv).2

theorem norm_le_of_cosine_minorant {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (P : RieszProjection p) {lam : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) (hK : 0 ≤ kConst p lam)
    (hminor : ∀ t ∈ Icc (-Real.pi) Real.pi,
      kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t) :
    pencilNorm P lam ≤ gk p lam := by
  have hC : max 1 ‖(lam : ℂ)‖ < gk p lam := gk_gt_max hp (ne_of_lt hp2) (by
    intro heq
    have : lam = 1 := by exact_mod_cast heq
    linarith [hlam.2])
  let ff : ℝ → ℝ := fun t => kConst p lam * Real.cos
    (q p * Complex.arg (Complex.exp (Complex.I * (t : ℂ))))
  apply TheoremRIf.thmR_if hp P (lam : ℂ) hC
  refine ⟨ff, TheoremRIf.sec4_cosine_qsub_proved p (kConst p lam) hp hp2 hK, ?_⟩
  intro t
  have ht : Complex.arg (unitPoint t) ∈ Icc (-Real.pi) Real.pi :=
    ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hh := hminor (Complex.arg (unitPoint t)) ht
  rw [cosine_mul_abs] at hh
  unfold Threshold.obstacle at hh
  rw [obstacle_arg_unitPoint] at hh
  simpa only [ff, unitPoint, mul_comm Complex.I (t : ℂ)] using hh

/-- Staging assembly: both remaining analytic leaves are explicit, never hidden in a numerical Check. -/
theorem proposition_Q_of_contact {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (P : RieszProjection p) {lam : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) (hK : 0 ≤ kConst p lam)
    (hlower : gk p lam ≤ pencilNorm P lam)
    (hderiv : HasDerivAt (Threshold.obstacle p lam) (-q p * kConst p lam) (theta p)) :
    (pencilNorm P lam = gk p lam ↔
      ∀ t ∈ Icc (-Real.pi) Real.pi,
        kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t) ∧
    (pencilNorm P lam = gk p lam ↔
      ∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) := by
  have hiff : pencilNorm P lam = gk p lam ↔
      ∀ t ∈ Icc (-Real.pi) Real.pi,
        kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t :=
    ⟨fun heq => cosine_necessary_of_norm_le P hp hp2 hlam hderiv heq.le,
      fun hh => le_antisymm (norm_le_of_cosine_minorant P hp hp2 hlam hK hh) hlower⟩
  exact ⟨hiff, hiff.trans (obstacle_cos_iff_critD_proved p lam hp hp2 hlam)⟩

end GKSharp

#print axioms GKSharp.cosine_necessary_of_norm_le
#print axioms GKSharp.norm_le_of_cosine_minorant
#print axioms GKSharp.proposition_Q_of_contact

