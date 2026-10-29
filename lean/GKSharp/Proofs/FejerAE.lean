/- O23 part 2(b): for a bounded, measurable, 2π-periodic u: |fejerMean u N t| ≤ Y, and
fejerMean u N t → u(t) at every Lebesgue point of u, hence almost everywhere. No cited input.
Copyright (C) Dave Goel 2026--now.

  fejerMean u N t - u t = (2π)⁻¹ ∫_{-π}^{π} (u(t - x) - u t) F_N(x) dx (s = t - x, periodicity, ∫ F_N = 2π).
  With g(x) = |u(t - x) - u t| ≤ 2Y and Ψ(r) = ∫_{-r}^{r} g, for 0 < r ≤ π:
  ∫_{-π}^{π} g F_N ≤ (N+1) Ψ(r) + 4Yπ²/((N+1) r)   (F_N ≤ N+1 inside, F_N ≤ π²/((N+1)x²) outside, ∫_r^π x⁻² ≤ 1/r).
  Take r = K/(N+1): the first term is K Ψ(r)/r → 0 at a Lebesgue point (Mathlib's Lebesgue differentiation
  theorem, IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub), the second is 4Yπ²/K. K is arbitrary. -/
import GKSharp.Proofs.FejerMeans
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace GKSharp

namespace Fejer

open Real MeasureTheory Filter Topology Set

/-! ### The bound -/

lemma integral_kerF_shift (N : ℕ) (t : ℝ) : ∫ s in (0 : ℝ)..(2 * π), kerF N (t - s) = 2 * π := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => kerF N x) t, sub_zero]
  have h := (kerF_periodic N).intervalIntegral_add_eq (t - 2 * π) (-π)
  rw [show t - 2 * π + 2 * π = t by ring, show -π + 2 * π = π by ring] at h
  rw [h, integral_kerF]

lemma intervalIntegrable_mul_kerF {g : ℝ → ℝ} (hg : Measurable g) {Y : ℝ} (hY : ∀ x, |g x| ≤ Y) (N : ℕ)
    (k : ℝ → ℝ) (hk : Continuous k) (a b : ℝ) :
    IntervalIntegrable (fun x => g x * kerF N (k x)) volume a b :=
  (intervalIntegrable_of_bdd hg hY a b).mul_continuousOn ((continuous_kerF N).comp hk).continuousOn

/-- O23 part 2, first claim: `|fejerMean u N t| ≤ Y`. -/
lemma fejerMean_abs_le {u : ℝ → ℝ} (hu : Measurable u) {Y : ℝ} (hY : ∀ t, |u t| ≤ Y) (N : ℕ) (t : ℝ) :
    |fejerMean u N t| ≤ Y := by
  have hπ : 0 < 2 * π := by positivity
  have hint := intervalIntegrable_mul_kerF hu hY N (fun s => t - s) (by fun_prop) 0 (2 * π)
  have hY' : IntervalIntegrable (fun s => Y * kerF N (t - s)) volume 0 (2 * π) :=
    ((continuous_kerF N).comp (by fun_prop : Continuous fun s : ℝ => t - s)).intervalIntegrable _ _ |>.const_mul Y
  rw [fejerMean_eq hu hY, abs_mul, abs_of_pos (inv_pos.2 hπ)]
  calc (2 * π)⁻¹ * |∫ s in (0 : ℝ)..(2 * π), u s * kerF N (t - s)|
      ≤ (2 * π)⁻¹ * ∫ s in (0 : ℝ)..(2 * π), |u s * kerF N (t - s)| := by
        gcongr
        exact intervalIntegral.abs_integral_le_integral_abs hπ.le
    _ ≤ (2 * π)⁻¹ * ∫ s in (0 : ℝ)..(2 * π), Y * kerF N (t - s) := by
        gcongr
        refine intervalIntegral.integral_mono_on hπ.le hint.abs hY' fun s _ => ?_
        rw [abs_mul, abs_of_nonneg (kerF_nonneg _ _)]
        exact mul_le_mul_of_nonneg_right (hY s) (kerF_nonneg _ _)
    _ = Y := by
        rw [intervalIntegral.integral_const_mul, integral_kerF_shift]
        field_simp

/-! ### The kernel form of the error -/

lemma fejerMean_sub_eq {u : ℝ → ℝ} (hu : Measurable u) (hper : Function.Periodic u (2 * π)) {Y : ℝ}
    (hY : ∀ t, |u t| ≤ Y) (N : ℕ) (t : ℝ) :
    fejerMean u N t - u t = (2 * π)⁻¹ * ∫ x in (-π)..π, (u (t - x) - u t) * kerF N x := by
  have hπ : (2 * π) ≠ 0 := by positivity
  have hint1 := intervalIntegrable_mul_kerF hu hY N (fun s => t - s) (by fun_prop) 0 (2 * π)
  have hint2 : IntervalIntegrable (fun s => u t * kerF N (t - s)) volume 0 (2 * π) :=
    ((continuous_kerF N).comp (by fun_prop : Continuous fun s : ℝ => t - s)).intervalIntegrable _ _ |>.const_mul _
  have hut : u t = (2 * π)⁻¹ * ∫ s in (0 : ℝ)..(2 * π), u t * kerF N (t - s) := by
    rw [intervalIntegral.integral_const_mul, integral_kerF_shift]
    field_simp
  have hshift : ∫ s in (0 : ℝ)..(2 * π), (u s - u t) * kerF N (t - s) =
      ∫ x in (-π)..π, (u (t - x) - u t) * kerF N x := by
    have hsub := intervalIntegral.integral_comp_sub_left (fun x => (u (t - x) - u t) * kerF N x) t
      (a := 0) (b := 2 * π)
    simp only [sub_sub_cancel, sub_zero] at hsub
    rw [hsub]
    have hper' : Function.Periodic (fun x => (u (t - x) - u t) * kerF N x) (2 * π) := fun x => by
      simp only
      rw [show t - (x + 2 * π) = t - x - 2 * π by ring, hper.sub_eq, kerF_periodic]
    have h := hper'.intervalIntegral_add_eq (t - 2 * π) (-π)
    rwa [show t - 2 * π + 2 * π = t by ring, show -π + 2 * π = π by ring] at h
  calc fejerMean u N t - u t
      = ((2 * π)⁻¹ * ∫ s in (0 : ℝ)..(2 * π), u s * kerF N (t - s)) -
          (2 * π)⁻¹ * ∫ s in (0 : ℝ)..(2 * π), u t * kerF N (t - s) := by
        rw [fejerMean_eq hu hY]
        exact congrArg (fun z => ((2 * π)⁻¹ * ∫ s in (0 : ℝ)..(2 * π), u s * kerF N (t - s)) - z) hut
    _ = (2 * π)⁻¹ * ∫ s in (0 : ℝ)..(2 * π), (u s - u t) * kerF N (t - s) := by
        have hdiff : ∫ s in (0 : ℝ)..(2 * π), (u s - u t) * kerF N (t - s) =
            (∫ s in (0 : ℝ)..(2 * π), u s * kerF N (t - s)) - ∫ s in (0 : ℝ)..(2 * π), u t * kerF N (t - s) := by
          rw [← intervalIntegral.integral_sub hint1 hint2]
          exact intervalIntegral.integral_congr fun s _ => by ring
        rw [hdiff, mul_sub]
    _ = _ := by rw [hshift]

end Fejer

end GKSharp
