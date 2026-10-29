/- Coverage links for the approved targets of slice SliceA_OperatorsDerived: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 bd065023525140d2dde026fe86d053c5; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.Pencil
import GKSharp.Proofs.PencilModes
import GKSharp.Paper.Statements

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_OperatorsDerived

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

/-- Coverage link (derived (circleMinus = pencil + (beta-alpha) zeroPart, circleMid = average: coeff_pencil, coeff_add/smul, coeff_mode, fourier_zero_eq_one)): the approved target `slice_N01` of slice SliceA_OperatorsDerived, from installed rows. Paper place: norm_correspondence.tex:6–11. -/
theorem cover_slice_N01 : ∀ (P : RieszProjection p) (α β : ℂ) (f : LpT p) (n : ℤ),
    fourierCoeff (⇑(circleMinus P α β f)) n =
      (if n ≤ 0 then β else α) * fourierCoeff (⇑f) n ∧
    fourierCoeff (⇑(circleMid P α β f)) n =
      (if n < 0 then β else if n = 0 then (α + β) / 2 else α) * fourierCoeff (⇑f) n :=
  by intro P α β f n; have hz : ∀ (a : ℂ) (m : ℤ), fourierCoeff (⇑(constantLp p a)) m = if m = 0 then a else 0 := (by intro a m; have hc : constantLp p a = a • DensityLp.toLpT p (fourier 0) := (by rw [fourier_zero_eq_one]; unfold constantLp DensityLp.toLpT; rw [← map_smul]; congr 1; ext x; simp); rw [hc, coeff_smul, coeff_mode]; split_ifs <;> simp); have hm : fourierCoeff (⇑(circleMinus P α β f)) n = (if n ≤ 0 then β else α) * fourierCoeff (⇑f) n := (by unfold circleMinus zeroPart; rw [coeff_add, coeff_smul, coeff_pencil, hz]; split_ifs with h1 h2 h3 <;> first | (exfalso; omega) | ring1 | (subst h2; ring1)); have hmid : fourierCoeff (⇑(circleMid P α β f)) n = (if n < 0 then β else if n = 0 then (α + β) / 2 else α) * fourierCoeff (⇑f) n := (by unfold circleMid; rw [coeff_smul, coeff_add, coeff_pencil, hm]; split_ifs with h1 h2 h3 h4 <;> first | (exfalso; omega) | ring1); exact ⟨hm, hmid⟩

/-- Coverage link (derived (pencil_hilbert_identity at a = (alpha+beta)/2, b = (beta-alpha)/(2i) gives pencil alpha beta; then the definitions of circleMid, circleMinus)): the approved target `slice_N01_hilbert_zero` of slice SliceA_OperatorsDerived, from installed rows. Paper place: norm_correspondence.tex:9–11. -/
theorem cover_slice_N01_hilbert_zero : ∀ (P : RieszProjection p) (α β : ℂ) (f : LpT p),
    circleMid P α β f = ((α + β) / 2) • f + ((β - α) / (2 * Complex.I)) •
      (shiftedHilbert P f + Complex.I • zeroPart p f) :=
  by intro P α β f; have h := congrArg (fun T : LpT p →L[ℂ] LpT p => T f) (pencil_hilbert_identity P ((α + β) / 2) ((β - α) / (2 * Complex.I))); simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at h; have hI : Complex.I ≠ 0 := Complex.I_ne_zero; have e1 : (α + β) / 2 - Complex.I * ((β - α) / (2 * Complex.I)) = α := (by field_simp; ring); have e2 : (α + β) / 2 + Complex.I * ((β - α) / (2 * Complex.I)) = β := (by field_simp; ring); have e3 : (β - α) / (2 * Complex.I) * Complex.I = (β - α) / 2 := (by field_simp); have e4 : ((β - α) / (2 * Complex.I)) • (Complex.I • zeroPart p f) = ((β - α) / 2) • zeroPart p f := (by rw [smul_smul, e3]); rw [e1, e2] at h; unfold circleMid circleMinus; rw [← h, smul_add ((β - α) / (2 * Complex.I)) (shiftedHilbert P f) (Complex.I • zeroPart p f), e4]; module

end Paper
end GKSharp

end GKSharp.CoverageLinks.SliceA_OperatorsDerived
