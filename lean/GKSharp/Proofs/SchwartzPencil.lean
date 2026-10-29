/- real-line Schwartz output and periodization, conditional on the genuine density theorem.
Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.SchwartzPencilTests
import GKSharp.Proofs.SchwartzPencilPeriodization
import GKSharp.Proofs.RealLineUnique

namespace GKSharp.Proofs.SchwartzPencil

open GKSharp.RealLineFourier MeasureTheory Set
open GKSharp.Proofs.RealLineUnique

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

theorem output_of_N10 (hN10 : N10Prop) (hp : 1 < p) (α β : ℂ) (T : RealLinePencil p α β)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (paperFourier f))
    (hz : 0 ∉ tsupport (paperFourier f)) :
    ∃ g : SchwartzMap ℝ ℂ,
      T.map (f.toLp (ENNReal.ofReal p) volume) = g.toLp (ENNReal.ofReal p) volume ∧
      ∀ ξ : ℝ, paperFourier g ξ = (if 0 < ξ then α else β) * paperFourier f ξ := by
  obtain ⟨g, hpaper, hpos, hneg⟩ := SchwartzPencilTests.exists_output_tests p α β f hc hz
  exact ⟨g, map_eq_of_tests hp hN10 T _ _ hpos hneg, hpaper⟩

theorem slice_N08_of_N10 (hN10 : N10Prop) (hp : 1 < p) (α β : ℂ) (T : RealLinePencil p α β)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (paperFourier f))
    (hz : 0 ∉ tsupport (paperFourier f)) :
    ∃ g : SchwartzMap ℝ ℂ, T.map (f.toLp (ENNReal.ofReal p) volume) = g.toLp (ENNReal.ofReal p) volume ∧
      ∀ ξ : ℝ, ξ ≠ 0 → paperFourier g ξ = (if 0 < ξ then α else β) * paperFourier f ξ := by
  obtain ⟨g, hmap, hpaper⟩ := output_of_N10 hN10 hp α β T f hc hz
  exact ⟨g, hmap, fun ξ _ => hpaper ξ⟩

theorem slice_N08_periodization_of_N10 (hN10 : N10Prop) (hp : 1 < p)
    (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β) (f g : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (paperFourier f)) (hz : 0 ∉ tsupport (paperFourier f))
    (hout : T.map (f.toLp (ENNReal.ofReal p) volume) = g.toLp (ENNReal.ofReal p) volume)
    (N : ℕ) (hN : 0 < N) (F G : C(Circ, ℂ))
    (hF : ∀ t : ℝ, F (t : Circ) = periodized f N t)
    (hG : ∀ t : ℝ, G (t : Circ) = periodized g N t) :
    pencil P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G ∧
    circleMinus P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G ∧
    circleMid P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G := by
  obtain ⟨g₀, hmap, hpaper⟩ := output_of_N10 hN10 hp α β T f hc hz
  have he : g = g₀ := SchwartzMap.injective_toLp (ENNReal.ofReal p) volume (hout.symm.trans hmap)
  subst g
  exact SchwartzPencilPeriodization.intertwine_of_fourier P α β f g₀ hc hz hpaper N hN F G hF hG

end GKSharp.Proofs.SchwartzPencil

#print axioms GKSharp.Proofs.SchwartzPencil.slice_N08_of_N10
#print axioms GKSharp.Proofs.SchwartzPencil.slice_N08_periodization_of_N10
