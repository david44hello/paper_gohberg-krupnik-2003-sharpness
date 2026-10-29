/- actual Lp pencil algebra and density.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.FourierDensity

namespace GKSharp

open MeasureTheory Filter Topology

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- P019_paper.tex:46: the sum of the actual two projections is the identity. -/
theorem plus_add_minus (P : RieszProjection p) :
    P.plus + rieszMinus P = ContinuousLinearMap.id ℂ (LpT p) := by
  simp [rieszMinus]

/-- Fourier-specified bounded projections have no arbitrary choice in their mathematical value. -/
theorem riesz_unique (P Q : RieszProjection p) : P = Q := by
  have h : P.plus = Q.plus := by
    apply ContinuousLinearMap.ext
    intro f
    apply DensityLp.fourier_ext
    intro n
    rw [P.coeff_plus, Q.coeff_plus]
  cases P
  cases Q
  cases h
  rfl

/-- P019_paper.tex:46: the complementary map has the exact negative-frequency mask. -/
theorem coeff_minus (P : RieszProjection p) (f : LpT p) (n : ℤ) :
    fourierCoeff (⇑(rieszMinus P f)) n = if n < 0 then fourierCoeff (⇑f) n else 0 := by
  have hu := DensityLp.integrable_haar_of_lp f
  have hv := DensityLp.integrable_haar_of_lp (P.plus f)
  have hae : (⇑(rieszMinus P f)) =ᵐ[AddCircle.haarAddCircle] fun x => f x - P.plus f x :=
    DensityLp.ae_haar_iff.mp (Lp.coeFn_sub f (P.plus f))
  rw [fourierCoeff_congr_ae hae]
  have hc : fourierCoeff (fun x => f x - P.plus f x) n =
      fourierCoeff (⇑f) n - fourierCoeff (⇑(P.plus f)) n := by
    unfold fourierCoeff
    simp_rw [smul_sub]
    exact integral_sub (hu.fourier_smul _) (hv.fourier_smul _)
  rw [hc, P.coeff_plus]
  split_ifs <;> simp_all <;> omega

/-- Each Fourier half is idempotent. -/
theorem plus_idempotent (P : RieszProjection p) (f : LpT p) : P.plus (P.plus f) = P.plus f := by
  apply DensityLp.fourier_ext
  intro n
  simp only [P.coeff_plus]
  split_ifs <;> rfl

/-- P019_paper.tex:48: the coefficient convention for aI+bH. -/
theorem pencil_hilbert_identity (P : RieszProjection p) (a b : ℂ) :
    a • ContinuousLinearMap.id ℂ (LpT p) + b • shiftedHilbert P =
      pencil P (a - Complex.I * b) (a + Complex.I * b) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, shiftedHilbert, pencil, rieszMinus,
    ContinuousLinearMap.sub_apply, smul_sub, smul_add, smul_smul]
  module

/-- P019_paper.tex:50: scaling of the actual pencil itself. -/
theorem pencil_homogeneous (P : RieszProjection p) (α β : ℂ) (hα : α ≠ 0) :
    pencil P α β = α • pencil P 1 (β / α) := by
  simp only [pencil, smul_add, smul_smul, mul_one]
  congr 1
  congr 1
  field_simp

/-- P019_paper.tex:50: operator norm homogeneity, including β=0. -/
theorem pencil_norm_homogeneous (P : RieszProjection p) (α β : ℂ) (hα : α ≠ 0) :
    ‖pencil P α β‖ = ‖α‖ * pencilNorm P (β / α) := by
  rw [pencil_homogeneous P α β hα, norm_smul]
  rfl

/-- The pure minus case, before the separately cited exact projection norm. -/
theorem pencil_norm_zero_left (P : RieszProjection p) (β : ℂ) :
    ‖pencil P 0 β‖ = ‖β‖ * ‖rieszMinus P‖ := by
  change ‖(0 : ℂ) • P.plus + β • rieszMinus P‖ = _
  have hz : (0 : ℂ) • P.plus = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    exact zero_smul ℂ (P.plus f)
  rw [hz, zero_add, norm_smul]

theorem pencil_same_coeff (P : RieszProjection p) (α : ℂ) :
    pencil P α α = α • ContinuousLinearMap.id ℂ (LpT p) := by
  unfold pencil
  rw [← smul_add α P.plus (rieszMinus P), plus_add_minus]

/-- At normalized ratio ρ=1 the pencil is the identity. -/
theorem pencil_one (P : RieszProjection p) :
    pencil P 1 1 = ContinuousLinearMap.id ℂ (LpT p) := by
  simpa using pencil_same_coeff P 1

/-- the all-Lp bound and the actual continuous-linear-map norm agree. -/
theorem pencil_bound_iff (P : RieszProjection p) (ρ : ℂ) {C : ℝ} (hC : 0 ≤ C) :
    PencilBound P ρ C ↔ pencilNorm P ρ ≤ C := by
  exact ⟨fun h => ContinuousLinearMap.opNorm_le_bound _ hC h,
    fun h f => (pencil P 1 ρ).le_opNorm f |>.trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg f))⟩

/-- an actual pencil bound is determined on the dense finite-Fourier class.
This is an unconditional theorem for every real bounded Fourier projection witness P. -/
theorem pencil_bound_iff_trig (P : RieszProjection p) (ρ : ℂ) (C : ℝ) :
    PencilBound P ρ C ↔ ∀ c : ℤ →₀ ℂ,
      ‖pencil P 1 ρ (DensityLp.toLpT p (DensityLp.tC c))‖ ≤
        C * ‖DensityLp.toLpT p (DensityLp.tC c)‖ := by
  constructor
  · intro h c
    exact h _
  · intro h f
    obtain ⟨c, hc⟩ := DensityLp.exists_trig_tendsto f
    have hleft := ((pencil P 1 ρ).continuous.tendsto f |>.comp hc).norm
    have hright := hc.norm.const_mul C
    exact le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall fun n => h (c n))

end GKSharp
