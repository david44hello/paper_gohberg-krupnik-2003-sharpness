/- weighted periodic averaging, frozen target slice_N05 (norm_correspondence.tex l.30-35, short v0.70).
Copyright (C) Dave Goel 2026--now. -/
import Mathlib

open MeasureTheory Real Filter Topology
open scoped ContDiff

namespace GKSharp.Proofs.N05Averaging

/-- The mean of `A` over one period `[0, 2π]`. -/
noncomputable def periodMean (A : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), A t

/-- The primitive of the centered function `A - mean A`, starting at `0`. -/
noncomputable def centeredPrimitive (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, (A t - periodMean A)

/-- A continuous `2π`-periodic real function is bounded. -/
lemma exists_abs_le_of_periodic {g : ℝ → ℝ} (hg : Continuous g)
    (hper : Function.Periodic g (2 * Real.pi)) : ∃ K, 0 ≤ K ∧ ∀ x, |g x| ≤ K := by
  obtain ⟨K, hK⟩ := (hper.isBounded_of_continuous (by positivity) hg).exists_norm_le
  refine ⟨max K 0, le_max_right _ _, fun x => ?_⟩
  have := hK (g x) ⟨x, rfl⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

lemma hasDerivAt_centeredPrimitive {A : ℝ → ℝ} (hA : Continuous A) (x : ℝ) :
    HasDerivAt (centeredPrimitive A) (A x - periodMean A) x :=
  ((hA.sub continuous_const).integral_hasStrictDerivAt 0 x).hasDerivAt

lemma continuous_centeredPrimitive {A : ℝ → ℝ} (hA : Continuous A) :
    Continuous (centeredPrimitive A) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_centeredPrimitive hA x).continuousAt

lemma periodic_centeredPrimitive {A : ℝ → ℝ} (hA : Continuous A)
    (hper : Function.Periodic A (2 * Real.pi)) :
    Function.Periodic (centeredPrimitive A) (2 * Real.pi) := by
  intro x
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun t => A t - periodMean A) volume a b :=
    fun a b => (hA.sub continuous_const).intervalIntegrable a b
  have hper' : Function.Periodic (fun t => A t - periodMean A) (2 * Real.pi) := by
    intro t
    simp only [hper t]
  have hzero : ∫ t in (0 : ℝ)..(2 * Real.pi), (A t - periodMean A) = 0 := by
    rw [intervalIntegral.integral_sub (hA.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    simp only [sub_zero, smul_eq_mul, periodMean]
    rw [mul_inv_cancel_left₀ hpi, sub_self]
  unfold centeredPrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 x) (hint x (x + 2 * Real.pi)),
    hper'.intervalIntegral_add_eq x 0, zero_add, hzero, add_zero]

/-- For `h ≠ 0`, `y ↦ h * B (y / h)` is a primitive of `y ↦ A (y / h) - mean A`. -/
lemma hasDerivAt_scaledPrimitive {A : ℝ → ℝ} (hA : Continuous A) {h : ℝ} (hh : h ≠ 0) (y : ℝ) :
    HasDerivAt (fun y => h * centeredPrimitive A (y / h)) (A (y / h) - periodMean A) y := by
  have h1 := ((hasDerivAt_centeredPrimitive hA (y / h)).comp y
    ((hasDerivAt_id y).div_const h)).const_mul h
  exact h1.congr_deriv (by field_simp)

/-- Integration by parts: for a smooth compactly supported `G` the oscillating integral against the
centered function is `O(h)`. -/
lemma abs_integral_smooth_mul_centered_le {A : ℝ → ℝ} (hA : Continuous A) {G : ℝ → ℝ}
    (hGs : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) {KB : ℝ}
    (hKB : ∀ x, |centeredPrimitive A x| ≤ KB) {h : ℝ} (hh : 0 < h) :
    |∫ y, G y * (A (y / h) - periodMean A)| ≤ h * KB * ∫ y, |deriv G y| := by
  set v : ℝ → ℝ := fun y => h * centeredPrimitive A (y / h) with hv
  set v' : ℝ → ℝ := fun y => A (y / h) - periodMean A with hv'
  have hGd : Differentiable ℝ G := hGs.differentiable (by simp)
  have hG'c : Continuous (deriv G) := hGs.continuous_deriv (by simp)
  have hvc : Continuous v :=
    continuous_const.mul ((continuous_centeredPrimitive hA).comp (continuous_id.div_const h))
  have hv'c : Continuous v' := (hA.comp (continuous_id.div_const h)).sub continuous_const
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := G) (u' := deriv G) (v := v)
    (v' := v') (fun x _ => (hGd x).hasDerivAt)
    (fun x _ => hasDerivAt_scaledPrimitive hA hh.ne' x)
    ((hGs.continuous.mul hv'c).integrable_of_hasCompactSupport hGc.mul_right)
    ((hG'c.mul hvc).integrable_of_hasCompactSupport hGc.deriv.mul_right)
    ((hGs.continuous.mul hvc).integrable_of_hasCompactSupport hGc.mul_right)
  have hG'i : Integrable (fun y => |deriv G y|) :=
    (hG'c.integrable_of_hasCompactSupport hGc.deriv).abs
  rw [hibp, abs_neg]
  calc |∫ x, deriv G x * v x| ≤ ∫ x, |deriv G x| * (h * KB) := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (hG'i.mul_const _) ?_
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [hv, abs_mul, abs_of_pos hh]
        exact mul_le_mul_of_nonneg_left (hKB _) hh.le
    _ = h * KB * ∫ x, |deriv G x| := by rw [integral_mul_const, mul_comm]

/-- The averaging limit for smooth compactly supported weights. -/
lemma tendsto_integral_smooth_mul_comp_div {A : ℝ → ℝ} (hA : Continuous A)
    (hper : Function.Periodic A (2 * Real.pi)) {G : ℝ → ℝ}
    (hGs : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) :
    Tendsto (fun h => ∫ y, G y * A (y / h)) (𝓝[>] 0) (𝓝 ((∫ y, G y) * periodMean A)) := by
  obtain ⟨KB, -, hKB⟩ := exists_abs_le_of_periodic (continuous_centeredPrimitive hA)
    (periodic_centeredPrimitive hA hper)
  have hGi : Integrable G := hGs.continuous.integrable_of_hasCompactSupport hGc
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    (g := fun h => h * KB * ∫ y, |deriv G y|)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hcont : Continuous fun y => A (y / h) := hA.comp (continuous_id.div_const h)
    have hGA : Integrable (fun y => G y * A (y / h)) :=
      (hGs.continuous.mul hcont).integrable_of_hasCompactSupport hGc.mul_right
    have heq : (∫ y, G y * A (y / h)) - (∫ y, G y) * periodMean A =
        ∫ y, G y * (A (y / h) - periodMean A) := by
      rw [← integral_mul_const, ← integral_sub hGA (hGi.mul_const _)]
      congr 1
      funext y
      ring
    rw [Real.norm_eq_abs, heq]
    exact abs_integral_smooth_mul_centered_le hA hGs hGc hKB hh
  · have hlim : Tendsto (fun h : ℝ => h * KB * ∫ y, |deriv G y|) (𝓝 0)
        (𝓝 (0 * KB * ∫ y, |deriv G y|)) :=
      ((continuous_id.mul continuous_const).mul continuous_const).tendsto 0
    simpa using hlim.mono_left nhdsWithin_le_nhds

/-- `L¹` approximation of an integrable `F` by a smooth compactly supported `G`, in integral form. -/
lemma exists_smooth_integral_abs_sub_le {F : ℝ → ℝ} (hF : Integrable F) {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : ℝ → ℝ, HasCompactSupport G ∧ ContDiff ℝ ∞ G ∧ ∫ y, |F y - G y| ≤ δ := by
  obtain ⟨G, hGc, hGs, hGapprox⟩ :=
    (memLp_one_iff_integrable.2 hF).exist_eLpNorm_sub_le ENNReal.one_ne_top le_rfl hδ
  have hGi : Integrable G := hGs.continuous.integrable_of_hasCompactSupport hGc
  refine ⟨G, hGc, hGs, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm (hF.sub hGi).aestronglyMeasurable] at hGapprox
  calc ∫ y, |F y - G y| = ∫ y, ‖(F - G) y‖ := by simp [Real.norm_eq_abs]
    _ = (∫⁻ y, ‖(F - G) y‖ₑ).toReal :=
        integral_norm_eq_lintegral_enorm (hF.sub hGi).aestronglyMeasurable
    _ ≤ δ := ENNReal.toReal_le_of_le_ofReal hδ.le hGapprox

/-- Pointwise-in-`h` bound: replacing `F` by `G` changes the oscillating integral by at most
`K ∫ |F - G|`. -/
lemma abs_integral_sub_integral_le {A : ℝ → ℝ} (hA : Continuous A) {K : ℝ}
    (hK : ∀ x, |A x| ≤ K) {F G : ℝ → ℝ} (hF : Integrable F) (hG : Integrable G) (h : ℝ) :
    |(∫ y, F y * A (y / h)) - ∫ y, G y * A (y / h)| ≤ (∫ y, |F y - G y|) * K := by
  have hcont : Continuous fun y => A (y / h) := hA.comp (continuous_id.div_const h)
  have hbd : ∀ᵐ y ∂(volume : Measure ℝ), ‖A (y / h)‖ ≤ K :=
    Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hK _
  have hFA : Integrable (fun y => F y * A (y / h)) := hF.mul_bdd hcont.aestronglyMeasurable hbd
  have hGA : Integrable (fun y => G y * A (y / h)) := hG.mul_bdd hcont.aestronglyMeasurable hbd
  have hFGi : Integrable (fun y => |F y - G y|) := (hF.sub hG).abs
  rw [← integral_sub hFA hGA, ← integral_mul_const, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hFGi.mul_const K) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hK _) (abs_nonneg _)

/-- The averaging limit for an arbitrary integrable weight `F`. -/
lemma tendsto_integral_mul_comp_div {A : ℝ → ℝ} (hA : Continuous A)
    (hper : Function.Periodic A (2 * Real.pi)) {F : ℝ → ℝ} (hF : Integrable F) :
    Tendsto (fun h => ∫ y, F y * A (y / h)) (𝓝[>] 0) (𝓝 ((∫ y, F y) * periodMean A)) := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_le_of_periodic hA hper
  set M := periodMean A with hM
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := ε / (4 * (K + |M| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨G, hGc, hGs, hFG⟩ := exists_smooth_integral_abs_sub_le hF hδpos
  have hGi : Integrable G := hGs.continuous.integrable_of_hasCompactSupport hGc
  have hlimG := Metric.tendsto_nhds.1 (tendsto_integral_smooth_mul_comp_div hA hper hGs hGc)
    (ε / 2) (by positivity)
  filter_upwards [hlimG] with h hhG
  rw [Real.dist_eq] at hhG ⊢
  have h1 : |(∫ y, F y * A (y / h)) - ∫ y, G y * A (y / h)| ≤ δ * K :=
    (abs_integral_sub_integral_le hA hK hF hGi h).trans
      (mul_le_mul_of_nonneg_right hFG hK0)
  have h3 : |(∫ y, G y) * M - (∫ y, F y) * M| ≤ δ * |M| := by
    rw [← sub_mul, abs_mul, ← integral_sub hGi hF]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    calc |∫ y, (G y - F y)| ≤ ∫ y, |G y - F y| := abs_integral_le_integral_abs
      _ = ∫ y, |F y - G y| := by
          congr 1
          funext y
          exact abs_sub_comm _ _
      _ ≤ δ := hFG
  have hδ' : δ * (K + |M| + 1) = ε / 4 := by
    rw [hδ]
    field_simp
  have hring : δ * K + δ * |M| = δ * (K + |M| + 1) - δ := by ring
  have t1 := abs_sub_le (∫ y, F y * A (y / h)) (∫ y, G y * A (y / h)) ((∫ y, F y) * M)
  have t2 := abs_sub_le (∫ y, G y * A (y / h)) ((∫ y, G y) * M) ((∫ y, F y) * M)
  linarith

/-- Change of variables `y = h x`. -/
lemma mul_integral_comp_mul_eq {F A : ℝ → ℝ} {h : ℝ} (hh : 0 < h) :
    h * ∫ x, F (h * x) * A x = ∫ y, F y * A (y / h) := by
  have key := Measure.integral_comp_mul_left (fun y => F y * A (y / h)) h
  simp only [mul_div_cancel_left₀ _ hh.ne', abs_of_pos (inv_pos.2 hh), smul_eq_mul] at key
  rw [key, mul_inv_cancel_left₀ hh.ne']

theorem slice_N05_proved {p : ℝ} (hp : 1 < p) (η : SchwartzMap ℝ ℂ) (A : ℝ → ℝ)
    (hA : Continuous A) (hper : Function.Periodic A (2 * Real.pi)) :
    Tendsto (fun h : ℝ => h * ∫ x : ℝ, ‖η (h * x)‖ ^ p * A x)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((∫ x : ℝ, ‖η x‖ ^ p) * ((2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), A t))) := by
  have hF : Integrable (fun x : ℝ => ‖η x‖ ^ p) := by
    have h1 := (η.memLp (ENNReal.ofReal p)).integrable_norm_rpow
      (ENNReal.ofReal_pos.2 (by linarith)).ne' ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal (by linarith)] at h1
  have hlim := tendsto_integral_mul_comp_div hA hper hF
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (mul_integral_comp_mul_eq (F := fun x => ‖η x‖ ^ p) hh).symm

end GKSharp.Proofs.N05Averaging

#print axioms GKSharp.Proofs.N05Averaging.slice_N05_proved
