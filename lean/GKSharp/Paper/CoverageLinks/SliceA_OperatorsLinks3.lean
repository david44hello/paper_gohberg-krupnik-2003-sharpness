/- Coverage links for the approved targets of slice SliceA_OperatorsLinks3: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 bd065023525140d2dde026fe86d053c5; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.Pencil
import GKSharp.Proofs.PencilModes
import GKSharp.Paper.Statements
import GKSharp.Proofs.N05Averaging
import GKSharp.Proofs.N09Periodization
import GKSharp.Proofs.N10Density
import GKSharp.Proofs.SchwartzPeriodizationMain
import GKSharp.Proofs.RealLineUnique

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_OperatorsLinks3

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

/-- Coverage link (derived (Proofs/RealLineUnique with the N10 premise discharged by Proofs/N10Density)): the approved target `slice_N01_unique` of slice SliceA_OperatorsLinks3, from installed rows. Paper place: norm_correspondence.tex l.8-10 (short v3.70). -/
theorem cover_slice_N01_unique : ∀ (hp : 1 < p) (α β : ℂ) (T S : RealLinePencil p α β), T = S :=
  fun hp α β T S => GKSharp.Proofs.RealLineUnique.slice_N01_unique_of_N10 (fun q _ hq f ε hε => GKSharp.Proofs.N10Density.slice_N10_proved hq f ε hε) hp α β T S

/-- Coverage link (renamed (Proofs/N05Averaging)): the approved target `slice_N05` of slice SliceA_OperatorsLinks3, from installed rows. Paper place: norm_correspondence.tex l.31-36 (short v3.70). -/
theorem cover_slice_N05 : ∀ (hp : 1 < p) (η : SchwartzMap ℝ ℂ) (A : ℝ → ℝ)
    (hA : Continuous A) (hper : Function.Periodic A (2 * Real.pi)),
    Tendsto (fun h : ℝ => h * ∫ x : ℝ, ‖η (h * x)‖ ^ p * A x)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((∫ x : ℝ, ‖η x‖ ^ p) * ((2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), A t))) :=
  GKSharp.Proofs.N05Averaging.slice_N05_proved

/-- Coverage link (renamed (Proofs/SchwartzPeriodizationMain)): the approved target `slice_N07` of slice SliceA_OperatorsLinks3, from installed rows. Paper place: norm_correspondence.tex l.40-45 (short v3.70). -/
theorem cover_slice_N07 : ∀ (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (paperFourier f))
    (hz : 0 ∉ tsupport (paperFourier f)) (N : ℕ) (hN : 0 < N),
    ∃ F : C(Circ, ℂ), (∀ t : ℝ, F (t : Circ) = periodized f N t) ∧
      (∀ n : ℤ, fourierCoeff (⇑F) n =
        ((2 * Real.pi * N : ℝ)⁻¹ : ℂ) * paperFourier f ((n : ℝ) / N)) ∧
      Set.Finite {n : ℤ | fourierCoeff (⇑F) n ≠ 0} ∧ fourierCoeff (⇑F) 0 = 0 :=
  GKSharp.Proofs.SchwartzPeriodizationMain.slice_N07_proved

/-- Coverage link (renamed (Proofs/N09Periodization)): the approved target `slice_N09` of slice SliceA_OperatorsLinks3, from installed rows. Paper place: norm_correspondence.tex l.47-52 (short v3.70). -/
theorem cover_slice_N09 : ∀ (hp : 1 < p) (f : SchwartzMap ℝ ℂ),
    Tendsto (fun N : ℕ => (2 * Real.pi * N) * circlePower p (periodized f N)) atTop
      (𝓝 (∫ x : ℝ, ‖f x‖ ^ p)) :=
  GKSharp.Proofs.N09Periodization.slice_N09_proved

/-- Coverage link (renamed (Proofs/N10Density)): the approved target `slice_N10` of slice SliceA_OperatorsLinks3, from installed rows. Paper place: norm_correspondence.tex l.54 (short v3.70). -/
theorem cover_slice_N10 : ∀ (hp : 1 < p) (f : LpR p) (ε : ℝ) (hε : 0 < ε),
    ∃ g : SchwartzMap ℝ ℂ, ‖g.toLp (ENNReal.ofReal p) volume - f‖ < ε ∧
      HasCompactSupport (paperFourier g) ∧ 0 ∉ tsupport (paperFourier g) :=
  GKSharp.Proofs.N10Density.slice_N10_proved

end Paper
end GKSharp

end GKSharp.CoverageLinks.SliceA_OperatorsLinks3
