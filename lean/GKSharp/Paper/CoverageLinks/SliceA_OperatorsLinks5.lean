/- Coverage links for the approved targets of slice SliceA_OperatorsLinks5: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 bd065023525140d2dde026fe86d053c5; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.Pencil
import GKSharp.Proofs.PencilModes
import GKSharp.Paper.Statements
import GKSharp.Proofs.N06Final
import GKSharp.Proofs.ReverseNormCircle

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_OperatorsLinks5

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

/-- Coverage link (renamed (Proofs/N06Final)): the approved target `slice_N06` of slice SliceA_OperatorsLinks5, from installed rows. Paper place: norm_correspondence.tex l.37-38 (short v3.90). -/
theorem cover_slice_N06 : ∀ (hp : 1 < p) (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β),
    ‖pencil P α β‖ ≤ ‖T.map‖ ∧ functionNorm (circleMinus P α β) ≤ ‖T.map‖ ∧
      functionNorm (circleMid P α β) ≤ ‖T.map‖ :=
  GKSharp.N06Final.slice_N06_proved

/-- Coverage link (renamed (Proofs/ReverseNormCircle)): the approved target `slice_N11` of slice SliceA_OperatorsLinks5, from installed rows. Paper place: norm_correspondence.tex l.53-54 (short v3.90). -/
theorem cover_slice_N11 : ∀ (hp : 1 < p) (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β),
    ‖T.map‖ ≤ ‖pencil P α β‖ ∧ ‖T.map‖ ≤ functionNorm (circleMinus P α β) ∧
      ‖T.map‖ ≤ functionNorm (circleMid P α β) :=
  GKSharp.Proofs.ReverseNormCircle.slice_N11_proved

end Paper
end GKSharp

end GKSharp.CoverageLinks.SliceA_OperatorsLinks5
