/- actual one-sided Fourier tests for the constructed Schwartz output.
Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.SchwartzPencilOutput

namespace GKSharp.Proofs.SchwartzPencilTests

open GKSharp.RealLineFourier GKSharp.Proofs.SchwartzPencilOutput MeasureTheory Set
open scoped FourierTransform ENNReal

theorem positive_test (α β : ℂ) (f g : SchwartzMap ℝ ℂ)
    (hg : ∀ ξ : ℝ, (𝓕 g) ξ = (if 0 < ξ then α else β) * (𝓕 f) ξ)
    (φ : SchwartzMap ℝ ℂ) (hφ : Function.support φ ⊆ Ioi 0) :
    (∫ x : ℝ, g x * (𝓕 φ) x) = α * ∫ x : ℝ, f x * (𝓕 φ) x := by
  rw [← SchwartzMap.integral_fourier_mul_eq g φ,
    ← SchwartzMap.integral_fourier_mul_eq f φ, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  by_cases hzero : φ ξ = 0
  · simp [hzero]
  · have hpos : 0 < ξ := hφ hzero
    rw [hg, ite_eq_left hpos]
    ring

theorem negative_test (α β : ℂ) (f g : SchwartzMap ℝ ℂ)
    (hg : ∀ ξ : ℝ, (𝓕 g) ξ = (if 0 < ξ then α else β) * (𝓕 f) ξ)
    (φ : SchwartzMap ℝ ℂ) (hφ : Function.support φ ⊆ Iio 0) :
    (∫ x : ℝ, g x * (𝓕 φ) x) = β * ∫ x : ℝ, f x * (𝓕 φ) x := by
  rw [← SchwartzMap.integral_fourier_mul_eq g φ,
    ← SchwartzMap.integral_fourier_mul_eq f φ, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  by_cases hzero : φ ξ = 0
  · simp [hzero]
  · have hneg : ξ < 0 := hφ hzero
    rw [hg, ite_eq_right (not_lt.mpr hneg.le)]
    ring

theorem lp_pairing_eq (q : ℝ≥0∞) (f : SchwartzMap ℝ ℂ) (φ : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, f.toLp q volume x * (𝓕 φ) x) = ∫ x : ℝ, f x * (𝓕 φ) x := by
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp q volume] with x hx
  rw [hx]

theorem exists_output_tests (p : ℝ) (α β : ℂ) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (paperFourier f)) (hz : 0 ∉ tsupport (paperFourier f)) :
    ∃ g : SchwartzMap ℝ ℂ,
      (∀ ξ : ℝ, paperFourier g ξ = (if 0 < ξ then α else β) * paperFourier f ξ) ∧
      (∀ φ : SchwartzMap ℝ ℂ, Function.support φ ⊆ Ioi 0 →
        (∫ x : ℝ, g.toLp (ENNReal.ofReal p) volume x * (𝓕 φ) x) =
          α * ∫ x : ℝ, f.toLp (ENNReal.ofReal p) volume x * (𝓕 φ) x) ∧
      (∀ φ : SchwartzMap ℝ ℂ, Function.support φ ⊆ Iio 0 →
        (∫ x : ℝ, g.toLp (ENNReal.ofReal p) volume x * (𝓕 φ) x) =
          β * ∫ x : ℝ, f.toLp (ENNReal.ofReal p) volume x * (𝓕 φ) x) := by
  obtain ⟨g, hg, hpaper⟩ := exists_output α β f hc hz
  refine ⟨g, hpaper, ?_, ?_⟩
  · intro φ hφ
    rw [lp_pairing_eq, lp_pairing_eq]
    exact positive_test α β f g hg φ hφ
  · intro φ hφ
    rw [lp_pairing_eq, lp_pairing_eq]
    exact negative_test α β f g hg φ hφ

end GKSharp.Proofs.SchwartzPencilTests

#print axioms GKSharp.Proofs.SchwartzPencilTests.exists_output_tests
