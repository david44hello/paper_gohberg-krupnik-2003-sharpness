/- unconditional Schwartz output and periodization for the actual real-line pencil.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.SchwartzPencil
import GKSharp.Proofs.N10Density

namespace GKSharp.Proofs.SchwartzPencilFinal

open GKSharp.RealLineFourier MeasureTheory

theorem density_proved : RealLineUnique.N10Prop := by
  intro q inst hq f ε hε
  exact N10Density.slice_N10_proved hq f ε hε

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

theorem slice_N08_proved (hp : 1 < p) (α β : ℂ) (T : RealLinePencil p α β)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (paperFourier f))
    (hz : 0 ∉ tsupport (paperFourier f)) :
    ∃ g : SchwartzMap ℝ ℂ, T.map (f.toLp (ENNReal.ofReal p) volume) = g.toLp (ENNReal.ofReal p) volume ∧
      ∀ ξ : ℝ, ξ ≠ 0 → paperFourier g ξ = (if 0 < ξ then α else β) * paperFourier f ξ :=
  SchwartzPencil.slice_N08_of_N10 density_proved hp α β T f hc hz

theorem slice_N08_periodization_proved (hp : 1 < p) (P : RieszProjection p) (α β : ℂ)
    (T : RealLinePencil p α β) (f g : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (paperFourier f)) (hz : 0 ∉ tsupport (paperFourier f))
    (hout : T.map (f.toLp (ENNReal.ofReal p) volume) = g.toLp (ENNReal.ofReal p) volume)
    (N : ℕ) (hN : 0 < N) (F G : C(Circ, ℂ))
    (hF : ∀ t : ℝ, F (t : Circ) = periodized f N t)
    (hG : ∀ t : ℝ, G (t : Circ) = periodized g N t) :
    pencil P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G ∧
    circleMinus P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G ∧
    circleMid P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G :=
  SchwartzPencil.slice_N08_periodization_of_N10 density_proved hp P α β T f g hc hz hout N hN F G hF hG

end GKSharp.Proofs.SchwartzPencilFinal

#print axioms GKSharp.Proofs.SchwartzPencilFinal.density_proved
#print axioms GKSharp.Proofs.SchwartzPencilFinal.slice_N08_proved
#print axioms GKSharp.Proofs.SchwartzPencilFinal.slice_N08_periodization_proved
