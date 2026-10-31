/- Coverage links for the approved targets of slice SliceA_Endpoint: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 521c4516fd87107cc7a13754ae97e61e; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.EndpointBridge
import GKSharp.Paper.Statements

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_Endpoint

open Real
namespace GKSharp.Paper

/-- Coverage link (split): the approved target `endpoint_lambda_eq_lambdaLoc` of slice SliceA_Endpoint, from installed rows. Paper place: endpoint_estimate.tex:11–20 (short v3.70). -/
theorem cover_endpoint_lambda_eq_lambdaLoc : ∀ {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)),
    0 < Threshold.localF p ∧ endpointLambda p = Threshold.lambdaLoc p :=
  by intro p hp hp1; have hhi : p ≤ (1000001 : ℝ) / 1000000 := by { norm_num at hp1 ⊢; linarith }; exact ⟨GKSharp.Paper.sec4_localF_endpoint hp hhi, GKSharp.Paper.endpoint_threshold_identification hp hhi⟩

end GKSharp.Paper

end GKSharp.CoverageLinks.SliceA_Endpoint
