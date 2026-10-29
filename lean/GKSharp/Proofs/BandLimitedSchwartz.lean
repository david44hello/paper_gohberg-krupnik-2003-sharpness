/- a nonzero band-limited Schwartz window for norm_correspondence.tex:22.
Copyright (C) Dave Goel 2026--now. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open Real MeasureTheory Filter Topology
open scoped ContDiff FourierTransform

namespace GKSharp.Proofs.BandLimitedSchwartz

/-- Mathlib uses exp(-2*pi*i*x*w); the paper uses exp(-i*x*xi). -/
theorem paper_transform_eq (f : ℝ → ℂ) (ξ : ℝ) :
    (∫ x : ℝ, f x * Complex.exp (-Complex.I * (x : ℂ) * (ξ : ℂ))) =
      𝓕 f (ξ / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hreal : -2 * Real.pi * x * (ξ / (2 * Real.pi)) = -(x * ξ) := by
    field_simp
    <;> ring
  rw [hreal]
  simp only [smul_eq_mul]
  have hcomplex : ((-(x * ξ) : ℝ) : ℂ) * Complex.I =
      -Complex.I * (x : ℂ) * (ξ : ℂ) := by push_cast; ring
  rw [hcomplex, mul_comm]

theorem slice_N03_proved : ∃ η : SchwartzMap ℝ ℂ, η ≠ 0 ∧
    HasCompactSupport (fun ξ : ℝ => ∫ x : ℝ,
      η x * Complex.exp (-Complex.I * (x : ℂ) * (ξ : ℂ))) := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let f : ℝ → ℂ := fun x => (bump x : ℂ)
  have hcompact : HasCompactSupport f :=
    bump.hasCompactSupport.comp_left (show (fun x : ℝ => (x : ℂ)) 0 = 0 by simp)
  have hsmooth : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp bump.contDiff
  let window : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hsmooth
  have hb0 : bump 0 = 1 := bump.one_of_mem_closedBall (by simp [bump])
  have hwindow : window ≠ 0 := by
    intro hh
    have he := congrArg (fun g : SchwartzMap ℝ ℂ => g 0) hh
    simpa [window, f, hb0] using he
  refine ⟨𝓕⁻ window, ?_, ?_⟩
  · intro hh
    apply hwindow
    simpa using congrArg
      (fun g : SchwartzMap ℝ ℂ => (𝓕 g : SchwartzMap ℝ ℂ)) hh
  · have heq : (fun ξ : ℝ => ∫ x : ℝ,
        (𝓕⁻ window) x * Complex.exp (-Complex.I * (x : ℂ) * (ξ : ℂ))) =
        fun ξ : ℝ => window (ξ / (2 * Real.pi)) := by
      funext ξ
      rw [paper_transform_eq]
      change (𝓕 (𝓕⁻ window) : SchwartzMap ℝ ℂ) (ξ / (2 * Real.pi)) = _
      rw [FourierTransform.fourier_fourierInv_eq]
    rw [heq]
    have hscale : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    simpa [Function.comp_def, div_eq_mul_inv, window] using
      hcompact.comp_isClosedEmbedding
        (Homeomorph.mulRight₀ ((2 * Real.pi)⁻¹) hscale).isClosedEmbedding

end GKSharp.Proofs.BandLimitedSchwartz

#print axioms GKSharp.Proofs.BandLimitedSchwartz.slice_N03_proved
