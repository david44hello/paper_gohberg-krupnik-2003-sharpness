/- O17: q-subtrigonometric iff continuous with nonnegative angular distribution.
Frozen target: Potential v0.40 slice_O17, with q>0 unchanged. Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.QSubAllPositive
import GKSharp.Proofs.TrigDistribution

namespace GKSharp.Proofs.AngularDistribution

theorem slice_O17_proved (q : ℝ) (hq : 0 < q) (φ : ℝ → ℝ)
    (hper : Function.Periodic φ (2 * Real.pi)) :
    QSubtrig q φ ↔ Continuous φ ∧ PositiveAngularDistribution q φ := by
  constructor
  · intro hφ
    have hc := GKSharp.AngularLocal.qsub_continuous hq hφ
    exact ⟨hc, (GKSharp.Proofs.TrigDistribution.trigConvex_iff_positiveAngularDistribution hq hc).mp
      (GKSharp.AngularLocal.qsub_trigConvex_all hq hφ)⟩
  · rintro ⟨hc, hdist⟩
    exact (GKSharp.AngularLocal.qsub_iff_continuous_trigconvex_all hq).mpr
      ⟨hper, hc, (GKSharp.Proofs.TrigDistribution.trigConvex_iff_positiveAngularDistribution hq hc).mpr hdist⟩

end GKSharp.Proofs.AngularDistribution

#print axioms GKSharp.Proofs.AngularDistribution.slice_O17_proved
