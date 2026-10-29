/- upper-envelope definitions.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential
namespace GKSharp

/-- Demailly §4.C.3, p. 38, on ℂ: the upper semicontinuous regularization `u⋆(z) = lim_{ε→0} sup_{B(z,ε)} u`. -/
noncomputable def uscRegC (u : ℂ → EReal) (z : ℂ) : EReal :=
  ⨅ ε : {ε : ℝ // 0 < ε}, ⨆ y ∈ Metric.ball z (ε : ℝ), u y

/-- "Locally uniformly bounded above" (Demailly §4.C.3) on ℂ: every point has a ball and a real bound valid for every member
of the family. -/
def LocUnifBddAboveC {ι : Type} (u : ι → ℂ → EReal) : Prop :=
  ∀ z : ℂ, ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ (i : ι) (y : ℂ), y ∈ Metric.ball z ε → u i y ≤ (M : EReal)

end GKSharp
