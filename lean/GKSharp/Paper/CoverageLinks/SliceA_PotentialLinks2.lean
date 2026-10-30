/- Coverage links for the approved targets of slice SliceA_PotentialLinks2: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 eb4fed10b0defe69fc42fba2af020460; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.GKRoot
import GKSharp.Proofs.Pencil
import GKSharp.Paper.Statements
import GKSharp.Proofs.PolarLaplacian
import GKSharp.Proofs.BlaschkeLift
import GKSharp.Proofs.ChordTent

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_PotentialLinks2

open Real MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator ContDiff
namespace GKSharp

def FiniteBlaschke (B : ℂ → ℂ) : Prop :=
  ∃ (phase : ℂ) (roots : List ℂ), ‖phase‖ = 1 ∧
    (∀ a ∈ roots, ‖a‖ < 1) ∧
    ∀ z : ℂ, B z = phase * (roots.map fun a => (z - a) / (1 - star a * z)).prod

noncomputable def polarLaplacian (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  deriv (deriv fun x : ℝ => u ((x : ℂ) + (z.im : ℂ) * Complex.I)) z.re +
    deriv (deriv fun y : ℝ => u ((z.re : ℂ) + (y : ℂ) * Complex.I)) z.im

noncomputable def fejerMean (u : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    ((1 - (n.natAbs : ℝ) / (N + 1) : ℝ) : ℂ) *
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      (∫ s in (0 : ℝ)..(2 * Real.pi), (u s : ℂ) * unitPoint (-(n : ℝ) * s)) *
      unitPoint ((n : ℝ) * t)).re

namespace Paper
variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- Coverage link (renamed (Proofs/PolarLaplacian)): the approved target `slice_O16` of slice SliceA_PotentialLinks2, from installed rows. Paper place: sec2_obstacle.tex l.67 (short v3.40). -/
theorem cover_slice_O16 : ∀ (q : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hper : Function.Periodic φ (2 * Real.pi)) (r t : ℝ) (hr : 0 < r),
    polarLaplacian (angularPotential q φ) ((r : ℂ) * unitPoint t) =
      r ^ (q - 2) * (deriv (deriv φ) t + q ^ 2 * φ t) :=
  GKSharp.O16.slice_O16_proved

/-- Coverage link (renamed (Proofs/BlaschkeLift)): the approved target `slice_O21` of slice SliceA_PotentialLinks2, from installed rows. Paper place: sec2_obstacle.tex l.82-85 (short v3.40). -/
theorem cover_slice_O21 : ∀ (g : Polynomial ℂ) (hg0 : g.eval 0 = 0) (hg : g ≠ 0),
    ∃ (k : ℕ) (B h H : ℂ → ℂ), 1 ≤ k ∧ FiniteBlaschke B ∧
      DifferentiableOn ℂ h (Metric.ball 0 1) ∧ DifferentiableOn ℂ H (Metric.ball 0 1) ∧
      ContinuousOn h (Metric.closedBall 0 1) ∧ ContinuousOn H (Metric.closedBall 0 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, h z ≠ 0) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, H z ^ 2 = h z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, g.eval z = z ^ k * B z * h z) :=
  GKSharp.BlaschkeLift.slice_O21_proved

/-- Coverage link (renamed (Proofs/ChordTent)): the approved target `slice_O31` of slice SliceA_PotentialLinks2, from installed rows. Paper place: sec2_obstacle.tex l.111-113 (short v3.40). -/
theorem cover_slice_O31 : ∀ (q : ℝ) (hq : 0 < q) (c s : ℝ) (hs : 0 < s ∧ s ≤ Real.pi / q),
    (∀ t, 0 ≤ chordTent q c s t) ∧ HasCompactSupport (chordTent q c s) ∧
    LipschitzWith (Real.toNNReal q) (chordTent q c s) ∧
    (∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      (∫ t : ℝ, chordTent q c s t * (deriv (deriv η) t + q ^ 2 * η t)) =
        q * (η (c - s) + η (c + s)) - 2 * q * cos (q * s) * η c) :=
  GKSharp.Proofs.ChordTent.slice_O31_proved

end Paper
end GKSharp

end GKSharp.CoverageLinks.SliceA_PotentialLinks2
