/- exact continuous finite Fourier-polynomial realization of the real-line periodization, N07.
Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.SchwartzPeriodization

namespace GKSharp.Proofs.SchwartzPeriodizationMain

open GKSharp.RealLineFourier GKSharp.Proofs.SchwartzPeriodization MeasureTheory Filter Topology Set
open scoped FourierTransform

theorem slice_N07_proved (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (paperFourier f))
    (hz : 0 ∉ tsupport (paperFourier f)) (N : ℕ) (hN : 0 < N) :
    ∃ F : C(Circ, ℂ), (∀ t : ℝ, F (t : Circ) = periodized f N t) ∧
      (∀ n : ℤ, fourierCoeff (⇑F) n =
        ((2 * Real.pi * N : ℝ)⁻¹ : ℂ) * paperFourier f ((n : ℝ) / N)) ∧
      Set.Finite {n : ℤ | fourierCoeff (⇑F) n ≠ 0} ∧ fourierCoeff (⇑F) 0 = 0 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let A : ℝ := 2 * Real.pi * N
  have hA : 0 < A := by dsimp [A]; positivity
  have hsamp := finite_sample_support f hc N hN
  have hfin : (Function.support (fun n : ℤ => ((A⁻¹ : ℝ) : ℂ) * paperFourier f ((n : ℝ) / N))).Finite := by
    apply hsamp.subset
    intro n hn
    by_contra hh
    have hh0 : paperFourier f ((n : ℝ) / N) = 0 := by
      simpa only [Set.mem_ofPred_eq, not_not] using hh
    apply hn
    change ((A⁻¹ : ℝ) : ℂ) * paperFourier f ((n : ℝ) / N) = 0
    rw [hh0, mul_zero]
  let c : ℤ →₀ ℂ := Finsupp.ofSupportFinite _ hfin
  have hc_apply (n : ℤ) : c n = ((A⁻¹ : ℝ) : ℂ) * paperFourier f ((n : ℝ) / N) := rfl
  let g := dilate A hA.ne' f
  have hFT (n : ℤ) : (𝓕 g) (n : ℝ) = c n := by
    change 𝓕 (fun x : ℝ => f (A * x)) (n : ℝ) = _
    rw [fourier_dilate f hA, hc_apply]
    congr 2
    dsimp [A]
    field_simp
  let F : C(Circ, ℂ) := DensityLp.tC c
  have hcoef (n : ℤ) : fourierCoeff (⇑F) n = c n := DensityLp.coeff_tC c n
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro t
    have hP := g.tsum_eq_tsum_fourier (t / (2 * Real.pi))
    have hleft : (∑' k : ℤ, g (t / (2 * Real.pi) + k)) = periodized f N t := by
      apply tsum_congr
      intro k
      change f (A * (t / (2 * Real.pi) + k)) = _
      congr 1
      dsimp [A]
      field_simp
      <;> ring
    rw [hleft] at hP
    simp_rw [hFT] at hP
    have hmode (n : ℤ) : fourier n ((t / (2 * Real.pi) : ℝ) : UnitAddCircle) =
        fourier n (t : Circ) := by
      rw [fourier_coe_apply, DensityLp.fourier_coe_two_pi]
      congr 1
      push_cast
      field_simp
    have hright : (∑' n : ℤ, c n * fourier n ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)) =
        F (t : Circ) := by
      simp_rw [hmode]
      rw [tsum_eq_sum (s := c.support) (fun n hn => by
        rw [Finsupp.notMem_support_iff.mp hn, zero_mul])]
      change _ = DensityLp.tC c (t : Circ)
      rw [DensityLp.tC_coe]
      simp_rw [DensityLp.fourier_coe_two_pi]
      rfl
    exact (hP.trans hright).symm
  · intro n
    rw [hcoef, hc_apply]
    simp only [A, Complex.ofReal_inv]
  · have hset : {n : ℤ | fourierCoeff (⇑F) n ≠ 0} = (c.support : Set ℤ) := by
      ext n
      change (fourierCoeff (⇑F) n ≠ 0) ↔ n ∈ c.support
      rw [hcoef]
      exact Finsupp.mem_support_iff.symm
    rw [hset]
    exact c.support.finite_toSet
  · rw [hcoef, hc_apply]
    simp only [Int.cast_zero, zero_div, paperFourier_zero_of_separated f hz, mul_zero]

end GKSharp.Proofs.SchwartzPeriodizationMain

#print axioms GKSharp.Proofs.SchwartzPeriodizationMain.slice_N07_proved
