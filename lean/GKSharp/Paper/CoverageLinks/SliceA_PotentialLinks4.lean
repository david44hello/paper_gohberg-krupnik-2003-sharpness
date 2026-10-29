/- Coverage links for the approved targets of slice SliceA_PotentialLinks4: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 eb4fed10b0defe69fc42fba2af020460; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.GKRoot
import GKSharp.Proofs.Pencil
import GKSharp.Paper.Statements
import GKSharp.Proofs.SliceO23

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_PotentialLinks4

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

/-- Coverage link (renamed (Proofs/SliceO23)): the approved target `slice_O23` of slice SliceA_PotentialLinks4, from installed rows. Paper place: sec2_obstacle.tex l.90-94 (short v0.70). -/
theorem cover_slice_O23 : ∀ (hp : 1 < p) (C : ℝ) (ρ : ℂ) (hC : max 1 ‖ρ‖ < C),
    (∀ ε : ℝ, 0 < ε → ∃ (Y : ℝ) (u : ℝ → ℝ), 0 ≤ Y ∧ Measurable u ∧
      Function.Periodic u (2 * Real.pi) ∧ (∀ t, |u t| ≤ Y) ∧
      (∀ t, gamma p C ρ (u t) t < obstacle p C ρ t + ε)) ∧
    (∀ (u : ℝ → ℝ) (Y : ℝ), Measurable u → Function.Periodic u (2 * Real.pi) →
      (∀ t, |u t| ≤ Y) → (∀ N t, |fejerMean u N t| ≤ Y) ∧
        ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))),
          Tendsto (fun N => fejerMean u N t) atTop (𝓝 (u t))) :=
  GKSharp.SliceO23.slice_O23_proved

end Paper
end GKSharp

end GKSharp.CoverageLinks.SliceA_PotentialLinks4
