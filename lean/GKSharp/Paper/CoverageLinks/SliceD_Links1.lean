/- Coverage links for the approved targets of slice SliceD_Links1: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 aa5615a19d185e84785ef87e76c517e3; do not edit. -/
import GKSharp.Defs.MonotonicityCurve
import GKSharp.Proofs.MonotoneSine
import GKSharp.Proofs.MonotoneElementary
import GKSharp.Proofs.MonotoneIdentities
import GKSharp.Proofs.MonotoneSinc
import GKSharp.Paper.Statements
import GKSharp.Proofs.CoordinateDictionaryFull

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceD_Links1

namespace GKSharp
namespace Paper

/-- Coverage link (renamed (Proofs/CoordinateDictionaryFull)): the approved target `sec5d_coordinate_dictionary` of slice SliceD_Links1, from installed rows. Paper place: sec5d_monotone.tex l.44, 62 (short v3.90). -/
theorem cover_sec5d_coordinate_dictionary : ∀ (p θ : ℝ) (hp : 1 < p ∧ p < 2)
    (hθ : 0 < θ ∧ θ < Real.pi),
    1 < p / (2 - p) ∧
    0 < (1 - p / 2) * θ ∧
    (1 - p / 2) * θ < Real.pi / (p / (2 - p) + 1) ∧
    (p / (2 - p) + 1) * ((1 - p / 2) * θ) = θ ∧
    (p / (2 - p) - 1) * ((1 - p / 2) * θ) = (p - 1) * θ ∧
      (p - 1) = (p / (2 - p) - 1) / (p / (2 - p) + 1) ∧
    p / 2 * θ = (p / (2 - p)) * ((1 - p / 2) * θ) ∧
    p / (2 - p) = (p / 2) / (1 - p / 2) ∧
    (1 - (p - 1)) * θ = 2 * ((1 - p / 2) * θ) ∧
    θ / 2 + (p - 1) * (θ / 2) = p / 2 * θ ∧
    θ / 2 - (p - 1) * (θ / 2) = (1 - p / 2) * θ :=
  GKSharp.sec5d_coordinate_dictionary_full_proved

end Paper
end GKSharp

namespace GKSharp.Paper
open Real Filter Topology
open scoped ContDiff BigOperators

end GKSharp.Paper

end GKSharp.CoverageLinks.SliceD_Links1
