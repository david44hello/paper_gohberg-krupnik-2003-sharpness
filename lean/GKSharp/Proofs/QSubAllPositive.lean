/- the q-subtrigonometric/chord bridge for every positive q, including q<=1/2.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.QSubLocal
import GKSharp.Proofs.TrigDistribution
import GKSharp.Proofs.TheoremRIf

open Real Set
namespace GKSharp.AngularLocal

theorem qsub_trigConvex_all {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) :
    TrigConvex q φ := by
  obtain ⟨L, hL, hlocal⟩ := qsub_centered_small hq hφ
  exact GKSharp.Proofs.TrigDistribution.trigConvex_of_centered hq
    (qsub_continuous hq hφ) hL hlocal

/-- The original periodic angular function is preserved, and no lower bound q>1/2 is assumed. -/
theorem qsub_iff_continuous_trigconvex_all {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} :
    QSubtrig q φ ↔ Function.Periodic φ (2 * Real.pi) ∧ Continuous φ ∧ TrigConvex q φ := by
  constructor
  · intro hφ
    exact ⟨hφ.1, qsub_continuous hq hφ, qsub_trigConvex_all hq hφ⟩
  · rintro ⟨hper, hc, htc⟩
    have hS := TheoremRIf.isSubharmonic_of_trigConvex hq hc hper htc
    exact ⟨hper, (fun z _ => hS.1 z), hS.2.1.upperSemicontinuousOn _,
      fun n c r hr _ => hS.2.2 n c r hr⟩

end GKSharp.AngularLocal

#print axioms GKSharp.AngularLocal.qsub_trigConvex_all
#print axioms GKSharp.AngularLocal.qsub_iff_continuous_trigconvex_all
