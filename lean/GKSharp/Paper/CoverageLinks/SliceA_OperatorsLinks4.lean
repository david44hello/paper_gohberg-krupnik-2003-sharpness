/- Coverage links for the approved targets of slice SliceA_OperatorsLinks4: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 bd065023525140d2dde026fe86d053c5; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.Pencil
import GKSharp.Proofs.PencilModes
import GKSharp.Paper.Statements
import GKSharp.Proofs.SchwartzPencilFinal
import GKSharp.Proofs.RealLineFinal

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_OperatorsLinks4

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

/-- Coverage link (renamed (Proofs/RealLineFinal)): the approved target `slice_N04` of slice SliceA_OperatorsLinks4, from installed rows. Paper place: norm_correspondence.tex l.23-30 (short v3.90). -/
theorem cover_slice_N04 : ∀ (hp : 1 < p) (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (η : SchwartzMap ℝ ℂ)
    (hη : HasCompactSupport (paperFourier η)) (c : ℤ →₀ ℂ),
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∃ Z W : SchwartzMap ℝ ℂ,
        (∀ x, Z x = η (h * x) * Complex.exp (Complex.I * (d : ℂ) * x) * trig c x) ∧
        (∀ x, W x = η (h * x) * Complex.exp (Complex.I * (d : ℂ) * x) *
          (α * Pplus c x + β * Pminus c x)) ∧
        T.map (Z.toLp (ENNReal.ofReal p) volume) = W.toLp (ENNReal.ofReal p) volume :=
  GKSharp.Proofs.RealLineFinal.slice_N04_proved

/-- Coverage link (renamed (Proofs/RealLineFinal)): the approved target `slice_N04_minus` of slice SliceA_OperatorsLinks4, from installed rows. Paper place: norm_correspondence.tex l.38 (short v3.90). -/
theorem cover_slice_N04_minus : ∀ (hp : 1 < p) (α β : ℂ) (T : RealLinePencil p α β)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (η : SchwartzMap ℝ ℂ)
    (hη : HasCompactSupport (paperFourier η)) (c : ℤ →₀ ℂ),
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∃ Z W : SchwartzMap ℝ ℂ,
        (∀ x, Z x = η (h * x) * Complex.exp (-(Complex.I * (d : ℂ) * x)) * trig c x) ∧
        (∀ x, W x = η (h * x) * Complex.exp (-(Complex.I * (d : ℂ) * x)) *
          (α * Pplus c x + β * Pminus c x + (β - α) * c 0)) ∧
        T.map (Z.toLp (ENNReal.ofReal p) volume) = W.toLp (ENNReal.ofReal p) volume :=
  GKSharp.Proofs.RealLineFinal.slice_N04_minus_proved

/-- Coverage link (renamed (Proofs/SchwartzPencilFinal)): the approved target `slice_N08` of slice SliceA_OperatorsLinks4, from installed rows. Paper place: norm_correspondence.tex l.46-47 (short v3.90). -/
theorem cover_slice_N08 : ∀ (hp : 1 < p) (α β : ℂ) (T : RealLinePencil p α β)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (paperFourier f))
    (hz : 0 ∉ tsupport (paperFourier f)),
    ∃ g : SchwartzMap ℝ ℂ, T.map (f.toLp (ENNReal.ofReal p) volume) = g.toLp (ENNReal.ofReal p) volume ∧
      ∀ ξ : ℝ, ξ ≠ 0 → paperFourier g ξ = (if 0 < ξ then α else β) * paperFourier f ξ :=
  GKSharp.Proofs.SchwartzPencilFinal.slice_N08_proved

/-- Coverage link (renamed (Proofs/SchwartzPencilFinal)): the approved target `slice_N08_periodization` of slice SliceA_OperatorsLinks4, from installed rows. Paper place: norm_correspondence.tex l.46 (short v3.90). -/
theorem cover_slice_N08_periodization : ∀ (hp : 1 < p) (P : RieszProjection p) (α β : ℂ)
    (T : RealLinePencil p α β) (f g : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (paperFourier f)) (hz : 0 ∉ tsupport (paperFourier f))
    (hout : T.map (f.toLp (ENNReal.ofReal p) volume) = g.toLp (ENNReal.ofReal p) volume)
    (N : ℕ) (hN : 0 < N) (F G : C(Circ, ℂ))
    (hF : ∀ t : ℝ, F (t : Circ) = periodized f N t)
    (hG : ∀ t : ℝ, G (t : Circ) = periodized g N t),
    pencil P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G ∧
    circleMinus P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G ∧
    circleMid P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G :=
  GKSharp.Proofs.SchwartzPencilFinal.slice_N08_periodization_proved

end Paper
end GKSharp

end GKSharp.CoverageLinks.SliceA_OperatorsLinks4
