/- N02, the norm correspondence (norm_correspondence.tex:13-18): the real-line pencil norm equals the two
circle function norms and the Lp norm of the real-line operator. Assembled from the proved N06 (forward bounds) and
N11 (reverse bounds) by NormCorrespondence.slice_N02_given; no extra premise.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.NormCorrespondence
import GKSharp.Proofs.ReverseNormCircle
import GKSharp.Proofs.N06Final

namespace GKSharp.Proofs.N02Final

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

theorem slice_N02_proved (hp : 1 < p) (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β) :
    ‖pencil P α β‖ = functionNorm (circleMinus P α β) ∧
    ‖pencil P α β‖ = functionNorm (circleMid P α β) ∧
    ‖pencil P α β‖ = ‖T.map‖ :=
  GKSharp.Proofs.NormCorrespondence.slice_N02_given GKSharp.N06Final.slice_N06_proved
    GKSharp.Proofs.ReverseNormCircle.slice_N11_proved hp P α β T

end GKSharp.Proofs.N02Final
