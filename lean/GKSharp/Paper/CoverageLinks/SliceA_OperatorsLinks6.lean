/- Coverage links for the approved targets of slice SliceA_OperatorsLinks6: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 bd065023525140d2dde026fe86d053c5; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.Pencil
import GKSharp.Proofs.PencilModes
import GKSharp.Paper.Statements
import GKSharp.Proofs.RealLineExists
import GKSharp.Proofs.N02Final

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_OperatorsLinks6

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

/-- Coverage link (renamed (Proofs/RealLineExists; cited HV2000 Theorem 3.1)): the approved target `slice_N01_nonvacuity` of slice SliceA_OperatorsLinks6, from installed rows. Paper place: norm_correspondence.tex l.8-10 and l.56 (short v3.40). -/
theorem cover_slice_N01_nonvacuity : ∀ (hp : 1 < p) (α β : ℂ), Nonempty (RealLinePencil p α β) :=
  GKSharp.Proofs.RealLineExists.slice_N01_nonvacuity_proved

/-- Coverage link (renamed (Proofs/N02Final)): the approved target `slice_N02` of slice SliceA_OperatorsLinks6, from installed rows. Paper place: norm_correspondence.tex l.15-20 (short v3.40). -/
theorem cover_slice_N02 : ∀ (hp : 1 < p) (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β),
    ‖pencil P α β‖ = functionNorm (circleMinus P α β) ∧
    ‖pencil P α β‖ = functionNorm (circleMid P α β) ∧
    ‖pencil P α β‖ = ‖T.map‖ :=
  GKSharp.Proofs.N02Final.slice_N02_proved

end Paper
end GKSharp

end GKSharp.CoverageLinks.SliceA_OperatorsLinks6
