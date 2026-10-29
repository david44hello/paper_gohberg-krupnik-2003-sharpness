/- actual reverse pencil norm bound, from proved density and the periodization limit.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ReverseNorm
import GKSharp.Proofs.SchwartzPencilFinal
import GKSharp.Proofs.N09Periodization

namespace GKSharp.Proofs.ReverseNormFinal

open GKSharp.RealLineFourier MeasureTheory

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem periodization_limit_proved (hp : 1 < p) : ReverseNorm.N09At p :=
  fun f => N09Periodization.slice_N09_proved hp f

theorem pencil_reverse_bound_proved (hp : 1 < p)
    (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β) :
    ‖T.map‖ ≤ ‖pencil P α β‖ :=
  ReverseNorm.pencil_reverse_bound SchwartzPencilFinal.density_proved
    (periodization_limit_proved hp) hp P α β T

end GKSharp.Proofs.ReverseNormFinal

#print axioms GKSharp.Proofs.ReverseNormFinal.pencil_reverse_bound_proved
