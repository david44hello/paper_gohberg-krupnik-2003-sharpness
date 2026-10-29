/- real-line N07 periodization and the exact Fourier normalization.
Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Defs.RealLineFourier
import GKSharp.Proofs.FourierDensity
import Mathlib.Analysis.Fourier.PoissonSummation

namespace GKSharp.Proofs.SchwartzPeriodization

open GKSharp.RealLineFourier MeasureTheory Filter Topology Set
open scoped FourierTransform

/-- Pull back a Schwartz function under an actual nonzero dilation. -/
noncomputable def dilate (A : ℝ) (hA : A ≠ 0) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    { toFun := fun x : ℝ => A * x
      invFun := fun x : ℝ => x / A
      left_inv := fun x => by dsimp; field_simp
      right_inv := fun x => by dsimp; field_simp
      map_add' := fun x y => by ring
      map_smul' := fun c x => by change A * (c * x) = c * (A * x); ring
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop } f

@[simp] theorem dilate_apply (A : ℝ) (hA : A ≠ 0) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    dilate A hA f x = f (A * x) := rfl

/-- The exact change-of-variables factor for Mathlib's 2*pi-normalized Fourier transform. -/
theorem fourier_dilate (f : ℝ → ℂ) {A : ℝ} (hA : 0 < A) (ξ : ℝ) :
    𝓕 (fun x : ℝ => f (A * x)) ξ =
      ((A⁻¹ : ℝ) : ℂ) * paperFourier f (2 * Real.pi * ξ / A) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    (∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) • f (A * x)) =
        ∫ x : ℝ, (fun y : ℝ => f y * Complex.exp
          (-Complex.I * (y : ℂ) * ((2 * Real.pi * ξ / A : ℝ) : ℂ))) (A * x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [smul_eq_mul]
      rw [mul_comm]
      congr 2
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hA.ne']
    _ = |A⁻¹| • paperFourier f (2 * Real.pi * ξ / A) := by
      simpa only [paperFourier] using Measure.integral_comp_mul_left
        (fun y : ℝ => f y * Complex.exp (-Complex.I * (y : ℂ) * ((2 * Real.pi * ξ / A : ℝ) : ℂ))) A
    _ = _ := by rw [abs_of_pos (inv_pos.mpr hA)]; rfl

/-- Compact frequency support gives finitely many sampled nonzero Fourier values. -/
theorem finite_sample_support (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (paperFourier f))
    (N : ℕ) (hN : 0 < N) :
    Set.Finite {n : ℤ | paperFourier f ((n : ℝ) / N) ≠ 0} := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨M, hM, hbound⟩ := hc.isBounded.exists_pos_norm_le
  apply (Set.finite_Icc (-⌈(N : ℝ) * M⌉) ⌈(N : ℝ) * M⌉).subset
  intro n hn
  have hnorm : |(n : ℝ) / N| ≤ M := by
    simpa only [Real.norm_eq_abs] using
      hbound _ (subset_tsupport (paperFourier f) hn)
  rw [abs_div, abs_of_pos hNr, div_le_iff₀ hNr] at hnorm
  have hceil : (N : ℝ) * M ≤ (⌈(N : ℝ) * M⌉ : ℤ) := Int.le_ceil _
  have habs : |(n : ℝ)| ≤ (⌈(N : ℝ) * M⌉ : ℤ) := hnorm.trans (by simpa [mul_comm] using hceil)
  constructor
  · exact_mod_cast (abs_le.mp habs).1
  · exact_mod_cast (abs_le.mp habs).2

theorem paperFourier_zero_of_separated (f : SchwartzMap ℝ ℂ)
    (hz : 0 ∉ tsupport (paperFourier f)) : paperFourier f 0 = 0 := by
  by_contra hn
  exact hz (subset_tsupport (paperFourier f) hn)

end GKSharp.Proofs.SchwartzPeriodization
