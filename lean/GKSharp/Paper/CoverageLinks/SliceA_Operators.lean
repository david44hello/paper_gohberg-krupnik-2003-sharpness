/- Coverage links for the approved targets of slice SliceA_Operators: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 bd065023525140d2dde026fe86d053c5; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.Pencil
import GKSharp.Proofs.PencilModes
import GKSharp.Paper.Statements

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_Operators

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

/-- Coverage link (stronger): the approved target `slice_I01` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:46. -/
theorem cover_slice_I01 : ∀ (hp : 1 < p), Nonempty (RieszProjection p) :=
  by intro hp; exact ⟨(GKSharp.Cited.hv2000_riesz_norm p hp).choose⟩

/-- Coverage link (split): the approved target `slice_I02` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:46. -/
theorem cover_slice_I02 : ∀ (P : RieszProjection p),
    P.plus + rieszMinus P = ContinuousLinearMap.id ℂ (LpT p) ∧
    ∀ (f : LpT p) (n : ℤ), fourierCoeff (⇑(rieszMinus P f)) n =
      if n < 0 then fourierCoeff (⇑f) n else 0 :=
  by intro P; exact ⟨GKSharp.plus_add_minus P, GKSharp.Paper.intro_minus_mask P⟩

/-- Coverage link (renamed): the approved target `slice_I03` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:47–48. -/
theorem cover_slice_I03 : ∀ (P : RieszProjection p) (a b : ℂ),
    a • ContinuousLinearMap.id ℂ (LpT p) + b • shiftedHilbert P =
      pencil P (a - Complex.I * b) (a + Complex.I * b) ∧
    shiftedHilbert P (DensityLp.toLpT p 1) = (-Complex.I) • DensityLp.toLpT p 1 :=
  GKSharp.Paper.intro_hilbert_convention (p := p)

/-- Coverage link (renamed): the approved target `slice_I04` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:50. -/
theorem cover_slice_I04 : ∀ (P : RieszProjection p) (α β : ℂ) (hα : α ≠ 0),
    ‖pencil P α β‖ = ‖α‖ * pencilNorm P (β / α) :=
  by intro P α β hα; exact GKSharp.Paper.intro_pencil_homogeneous P hα β

/-- Coverage link (split): the approved target `slice_I05` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:51. -/
theorem cover_slice_I05 : ∀ (P : RieszProjection p),
    ∃ U : LpT p → LpT p, Isometry U ∧ Function.Involutive U ∧
      (∀ f g, U (f + g) = U f + U g) ∧ (∀ (a : ℂ) f, U (a • f) = a • U f) ∧
      (∀ f, ∀ᵐ x ∂(volume : Measure Circ), U f x = fourier (-1) x * f (-x)) ∧
      (∀ f, U (P.plus f) = rieszMinus P (U f)) ∧
      (∀ f, U (rieszMinus P f) = P.plus (U f)) ∧
      (∀ (f : LpT p) (n : ℤ), fourierCoeff (⇑(U f)) n = fourierCoeff (⇑f) (-n - 1)) :=
  by intro P; refine ⟨GKSharp.reflU, Isometry.of_dist_eq (fun f g => by rw [dist_eq_norm, dist_eq_norm, ← GKSharp.reflU_sub, GKSharp.norm_reflU]), GKSharp.reflU_reflU, GKSharp.reflU_add, GKSharp.reflU_smul, GKSharp.coeFn_reflU, (fun f => by simpa only [GKSharp.pencil_one_zero, GKSharp.pencil_zero_one] using GKSharp.reflU_pencil P 1 0 f), (fun f => by simpa only [GKSharp.pencil_one_zero, GKSharp.pencil_zero_one] using GKSharp.reflU_pencil P 0 1 f), GKSharp.coeff_reflU⟩

/-- Coverage link (renamed): the approved target `slice_I06` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:52. -/
theorem cover_slice_I06 : ∀ (P : RieszProjection p),
    ∃ J : LpT p → LpT p, Isometry J ∧ Function.Involutive J ∧
      (∀ f g, J (f + g) = J f + J g) ∧ (∀ (a : ℂ) f, J (a • f) = star a • J f) ∧
      (∀ f, ∀ᵐ x ∂(volume : Measure Circ), J f x = star (f (-x))) ∧
      (∀ f, J (P.plus f) = P.plus (J f)) ∧
      (∀ f, J (rieszMinus P f) = rieszMinus P (J f)) :=
  GKSharp.Paper.intro_isometry_J (p := p)

/-- Coverage link (renamed): the approved target `slice_I07` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:53. -/
theorem cover_slice_I07 : ∀ {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hp : 1 < p)
    (hq : q = p / (p - 1)) (P : RieszProjection p) (Q : RieszProjection q)
    (f : LpT p) (g : LpT q),
    (∫ x : Circ, P.plus f x * star (g x)) = (∫ x : Circ, f x * star (Q.plus g x)) ∧
    (∫ x : Circ, rieszMinus P f x * star (g x)) =
      (∫ x : Circ, f x * star (rieszMinus Q g x)) :=
  by intro q instq hp hq P Q f g; exact GKSharp.Paper.intro_selfadjoint hp hq P Q f g

/-- Coverage link (renamed): the approved target `slice_I08` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:55. -/
theorem cover_slice_I08 : ∀ (P : RieszProjection p) (ρ : ℂ),
    pencilNorm P ρ = pencilNorm P (star ρ) :=
  GKSharp.Paper.intro_norm_conj (p := p)

/-- Coverage link (renamed): the approved target `slice_I09` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:55. -/
theorem cover_slice_I09 : ∀ (P : RieszProjection p) (ρ : ℂ) (hρ : ρ ≠ 0),
    pencilNorm P ρ = ‖ρ‖ * pencilNorm P (1 / ρ) :=
  by intro P ρ hρ; exact GKSharp.Paper.intro_norm_inv P hρ

/-- Coverage link (renamed): the approved target `slice_I10` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:55. -/
theorem cover_slice_I10 : ∀ {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hp : 1 < p)
    (hq : q = p / (p - 1)) (P : RieszProjection p) (Q : RieszProjection q) (ρ : ℂ),
    pencilNorm P ρ = pencilNorm Q (star ρ) :=
  by intro q instq hp hq P Q ρ; subst q; exact GKSharp.Paper.intro_norm_dual hp P Q ρ

/-- Coverage link (renamed): the approved target `slice_I11` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:57. -/
theorem cover_slice_I11 : ∀ (hp : 1 < p) (P : RieszProjection p) (ρ : ℂ),
    ∃ q : ℝ, ∃ hq : Fact (1 ≤ ENNReal.ofReal q), ∃ Q : @RieszProjection q hq,
      ∃ (r : ℂ) (s : ℝ), (q = p ∨ q = p / (p - 1)) ∧ 1 < q ∧ q ≤ 2 ∧
        (r = ρ ∨ r = star ρ ∨ r = 1 / ρ ∨ r = 1 / star ρ) ∧ ‖r‖ ≤ 1 ∧
        s = max 1 ‖ρ‖ ∧ pencilNorm P ρ = s * @pencilNorm q hq Q r ∧
        gk p ρ = s * gk q r :=
  GKSharp.Paper.intro_norm_reduce (p := p)

/-- Coverage link (renamed): the approved target `slice_I12` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:58. -/
theorem cover_slice_I12 : ∀ (hp : 1 < p) (P : RieszProjection p) (β : ℂ),
    ‖pencil P 0 β‖ = ‖β‖ / sin (Real.pi / p) :=
  GKSharp.Paper.intro_pencil_zero_left (p := p)

/-- Coverage link (renamed): the approved target `slice_I13` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:59. -/
theorem cover_slice_I13 : ∀ (hp : p = 2) (P : RieszProjection p) (α β : ℂ),
    ‖pencil P α β‖ = max ‖α‖ ‖β‖ :=
  GKSharp.Paper.intro_pencil_two (p := p)

/-- Coverage link (split): the approved target `slice_I14` of slice SliceA_Operators, from installed rows. Paper place: P019_paper.tex:60. -/
theorem cover_slice_I14 : ∀ (hp : 1 < p) (α β : ℂ),
    gkPair p 0 β = ‖β‖ / sin (Real.pi / p) ∧ gkPair 2 α β = max ‖α‖ ‖β‖ :=
  by intro hp α β; exact ⟨GKSharp.Paper.sec2_gk_pure_minus p hp β, GKSharp.Paper.sec2_gk_two α β⟩

/-- Coverage link (renamed): the approved target `slice_N12` of slice SliceA_Operators, from installed rows. Paper place: norm_correspondence.tex:56. -/
theorem cover_slice_N12 : ∀ (a b : ℝ) (ha : (a : ℂ) - Complex.I * b ≠ 0),
    ‖((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b)‖ = 1 :=
  @GKSharp.Paper.normcorr_ratio_unimodular

/-- Coverage link (renamed): the approved target `reduction_gk_conj` of slice SliceA_Operators, from installed rows. Paper place: sec2_obstacle.tex:21–26 (short v0.70). -/
theorem cover_reduction_gk_conj : ∀ (p : ℝ) (ρ : ℂ), gk p (star ρ) = gk p ρ :=
  @GKSharp.Paper.sec2_gk_conj

/-- Coverage link (renamed): the approved target `reduction_gk_inv` of slice SliceA_Operators, from installed rows. Paper place: sec2_obstacle.tex:21–27 (short v0.70). -/
theorem cover_reduction_gk_inv : ∀ (p : ℝ) (ρ : ℂ) (hρ : ρ ≠ 0),
    gk p ρ = ‖ρ‖ * gk p (1 / ρ) :=
  by intro p ρ hρ; exact GKSharp.Paper.sec5_gk_inv p hρ

/-- Coverage link (stronger): the approved target `classical_projection_norm` of slice SliceA_Operators, from installed rows. Paper place: sec2_obstacle.tex:36–37 (short v0.70). -/
theorem cover_classical_projection_norm : ∀ (hp : 1 < p) (P : RieszProjection p),
    pencilNorm P 0 = 1 / sin (Real.pi / p) :=
  by intro hp P; obtain ⟨Q, hQ⟩ := GKSharp.Cited.hv2000_riesz_norm p hp; simpa [GKSharp.pencilNorm, GKSharp.pencil_one_zero, GKSharp.riesz_unique P Q] using hQ

/-- Coverage link (stronger (thm_C1 at lam = -1 + sec2_gk_at_minus_one)): the approved target `classical_conjugate_norm` of slice SliceA_Operators, from installed rows. Paper place: sec2_obstacle.tex:36–37 (short v0.70). -/
theorem cover_classical_conjugate_norm : ∀ (hp : 1 < p) (hp2 : p < 2) (P : RieszProjection p),
    pencilNorm P (-1) = tan (Real.pi / (2 * p)) :=
  by intro hp hp2 P; have h := GKSharp.Paper.thm_C1 hp P (lam := -1) (by norm_num) (by norm_num); have hg := GKSharp.Paper.sec2_gk_at_minus_one hp hp2; push_cast at h; rw [h, hg]

end Paper
end GKSharp

end GKSharp.CoverageLinks.SliceA_Operators
