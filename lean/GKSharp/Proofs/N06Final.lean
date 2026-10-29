/- GKSharp/Proofs/N06Final.lean - row slice_N06 at its exact frozen type with NO premise: slice_N06_given with its four
inputs discharged by their proofs (N03, N04/N04_minus, N05).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.N06Forward
import GKSharp.Proofs.BandLimitedSchwartz
import GKSharp.Proofs.RealLineFinal
import GKSharp.Proofs.N05Averaging

namespace GKSharp.N06Final

open GKSharp

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- **slice_N06** (norm_correspondence.tex l.36-37): `‖αP₊ + βP₋‖ ≤ ‖T_ℝ‖`, and the same for circleMinus and
circleMid with their actual functionNorm. -/
theorem slice_N06_proved (hp : 1 < p) (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β) :
    ‖pencil P α β‖ ≤ ‖T.map‖ ∧ functionNorm (circleMinus P α β) ≤ ‖T.map‖ ∧
      functionNorm (circleMid P α β) ≤ ‖T.map‖ :=
  N06.slice_N06_given Proofs.BandLimitedSchwartz.slice_N03_proved Proofs.RealLineFinal.slice_N04_proved
    Proofs.RealLineFinal.slice_N04_minus_proved Proofs.N05Averaging.slice_N05_proved hp P α β T

end GKSharp.N06Final
