/- Coverage links for the approved targets of slice SliceA_PotentialLinks3: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 eb4fed10b0defe69fc42fba2af020460; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.GKRoot
import GKSharp.Proofs.Pencil
import GKSharp.Paper.Statements
import GKSharp.Proofs.AnalyticLift
import GKSharp.Proofs.AngularDistribution

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_PotentialLinks3

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

/-- Coverage link (renamed (Proofs/AngularDistribution)): the approved target `slice_O17` of slice SliceA_PotentialLinks3, from installed rows. Paper place: sec2_obstacle.tex l.67-69 (short v3.90). -/
theorem cover_slice_O17 : ∀ (q : ℝ) (hq : 0 < q) (φ : ℝ → ℝ) (hper : Function.Periodic φ (2 * Real.pi)),
    QSubtrig q φ ↔ Continuous φ ∧ PositiveAngularDistribution q φ :=
  GKSharp.Proofs.AngularDistribution.slice_O17_proved

/-- Coverage link (renamed (Proofs/AnalyticLift)): the approved target `slice_O22` of slice SliceA_PotentialLinks3, from installed rows. Paper place: sec2_obstacle.tex l.84-88 (short v3.90). -/
theorem cover_slice_O22 : ∀ (hp : 1 < p) (P : RieszProjection p) (C : ℝ) (ρ : ℂ)
    (hC : pencilNorm P ρ ≤ C) (g : Polynomial ℂ) (hg0 : g.eval 0 = 0) (hg : g ≠ 0)
    (Y : Polynomial ℂ),
    ∃ Z W : ℂ → ℂ, DifferentiableOn ℂ Z (Metric.ball 0 1) ∧
      DifferentiableOn ℂ W (Metric.ball 0 1) ∧ ContinuousOn Z (Metric.closedBall 0 1) ∧
      ContinuousOn W (Metric.closedBall 0 1) ∧ W 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, Z z * W z = g.eval z) ∧
      (∀ t : ℝ, ‖Z (unitPoint t)‖ ^ 2 = ‖g.eval (unitPoint t)‖ * exp (Y.eval (unitPoint t)).re ∧
        ‖W (unitPoint t)‖ ^ 2 = ‖g.eval (unitPoint t)‖ * exp (-(Y.eval (unitPoint t)).re)) ∧
      0 ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), pairObstacle p C ρ (Z (unitPoint t)) (W (unitPoint t)) :=
  GKSharp.AnalyticLift.slice_O22_proved

/-- Coverage link (renamed (Proofs/AnalyticLift)): the approved target `eq_lift` of slice SliceA_PotentialLinks3, from installed rows. Paper place: sec2_obstacle.tex l.87-89 (short v3.90). -/
theorem cover_eq_lift : ∀ (hp : 1 < p) (P : RieszProjection p) (C : ℝ) (ρ : ℂ)
    (hC : pencilNorm P ρ ≤ C) (g : Polynomial ℂ) (hg0 : g.eval 0 = 0) (hg : g ≠ 0)
    (Y : Polynomial ℂ),
    0 ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), ‖g.eval (unitPoint t)‖ ^ (p / 2) *
      gamma p C ρ (Y.eval (unitPoint t)).re (Complex.arg (g.eval (unitPoint t))) :=
  GKSharp.AnalyticLift.eq_lift_proved

end Paper
end GKSharp

end GKSharp.CoverageLinks.SliceA_PotentialLinks3
