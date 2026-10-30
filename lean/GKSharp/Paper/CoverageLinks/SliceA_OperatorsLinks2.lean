/- Coverage links for the approved targets of slice SliceA_OperatorsLinks2: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 bd065023525140d2dde026fe86d053c5; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.Pencil
import GKSharp.Proofs.PencilModes
import GKSharp.Paper.Statements
import GKSharp.Proofs.BandLimitedSchwartz

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_OperatorsLinks2

open MeasureTheory Real Filter Topology
namespace GKSharp

noncomputable def paperFourier (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (-Complex.I * (x : ℂ) * (ξ : ℂ))

noncomputable def periodized (f : ℝ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℤ, f ((N : ℝ) * (t + 2 * Real.pi * k))

noncomputable def circlePower (p : ℝ) (f : ℝ → ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), ‖f t‖ ^ p

namespace Paper
variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- Coverage link (renamed (Proofs/BandLimitedSchwartz)): the approved target `slice_N03` of slice SliceA_OperatorsLinks2, from installed rows. Paper place: norm_correspondence.tex l.23 (short v3.40). -/
theorem cover_slice_N03 : ∃ η : SchwartzMap ℝ ℂ, η ≠ 0 ∧ HasCompactSupport (paperFourier η) :=
  GKSharp.Proofs.BandLimitedSchwartz.slice_N03_proved

end Paper
end GKSharp

end GKSharp.CoverageLinks.SliceA_OperatorsLinks2
