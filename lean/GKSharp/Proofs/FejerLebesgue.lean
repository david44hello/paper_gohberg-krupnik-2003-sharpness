/- GKSharp/Proofs/FejerLebesgue.lean - slice (a) O23 support: every point is a Lebesgue point a.e. (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
For a bounded measurable u : ℝ → ℝ, for almost every t, (∫_{-r}^{r} |u(t - x) - u(t)| dx) / r → 0 as r → 0+.
Route: Mathlib's Lebesgue differentiation theorem for doubling measures (IsUnifLocDoublingMeasure
.ae_tendsto_average_norm_sub) on the balls closedBall t r = [t - r, t + r]; the ratio is twice the average. -/
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Filter Topology Set Metric

namespace GKSharp

namespace FejerLebesgue

/-- For `r > 0`, the symmetric integral over `[-r, r]` of `|u(t - x) - u(t)|`, divided by `r`, is twice the average of
`|u(y) - u(t)|` over the ball `closedBall t r`. -/
lemma ratio_eq_two_average (u : ℝ → ℝ) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ x in (-r)..r, |u (t - x) - u t|) / r = 2 * ⨍ y in closedBall t r, ‖u y - u t‖ := by
  have hsub : ∫ x in (-r)..r, |u (t - x) - u t| = ∫ y in (t - r)..(t + r), |u y - u t| := by
    have h := intervalIntegral.integral_comp_sub_left (fun y => |u y - u t|) (a := -r) (b := r) t
    simpa only [sub_neg_eq_add] using h
  have hball : ∫ y in closedBall t r, ‖u y - u t‖ = ∫ y in (t - r)..(t + r), |u y - u t| := by
    rw [Real.closedBall_eq_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
    simp only [Real.norm_eq_abs]
  rw [setAverage_eq, Real.volume_real_closedBall hr.le, smul_eq_mul, hball, hsub]
  field_simp

theorem lebesgue_point_ae {u : ℝ → ℝ} (hu : Measurable u) {Y : ℝ} (hY : ∀ t, |u t| ≤ Y) :
    ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Filter.Tendsto (fun r : ℝ => (∫ x in (-r)..r, |u (t - x) - u t|) / r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hloc : LocallyIntegrable u volume := by
    refine (locallyIntegrable_iff (μ := volume)).mpr fun k hk => ?_
    refine Measure.integrableOn_of_bounded (M := Y) hk.measure_lt_top.ne hu.aestronglyMeasurable ?_
    exact Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using hY t
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (μ := volume) hloc 1] with t ht
  have hmem : ∀ᶠ r in 𝓝[>] (0 : ℝ), t ∈ closedBall ((fun _ : ℝ => t) r) (1 * id r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mem_closedBall_self (by rw [one_mul]; exact le_of_lt hr)
  have hA : Tendsto (fun r : ℝ => ⨍ y in closedBall t r, ‖u y - u t‖) (𝓝[>] 0) (𝓝 0) :=
    ht (fun _ : ℝ => t) id tendsto_id hmem
  have h2 : Tendsto (fun r : ℝ => 2 * ⨍ y in closedBall t r, ‖u y - u t‖) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hA.const_mul 2
  refine Tendsto.congr' ?_ h2
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (ratio_eq_two_average u t hr).symm

end FejerLebesgue

end GKSharp
