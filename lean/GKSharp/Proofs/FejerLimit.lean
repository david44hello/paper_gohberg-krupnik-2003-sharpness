/- O23 part 2(b): at a Lebesgue point t of a bounded, measurable, 2π-periodic u (Ψ(r)/r → 0 as
r → 0+, Ψ(r) = ∫_{-r}^{r} |u(t - x) - u t| dx), fejerMean u N t → u(t). No cited input.
Copyright (C) Dave Goel 2026--now.

  g(x) = |u(t - x) - u t| ≤ 2Y. For 0 < r ≤ π: ∫_{-π}^{π} g F_N ≤ (N+1) Ψ(r) + 4Yπ²/((N+1) r): on [-r, r] use
  F_N ≤ N + 1; on [r, π] and (after x ↦ -x, F_N even) on [-π, -r] use F_N ≤ π²/((N+1)x²) and ∫_r^π x⁻² ≤ 1/r.
  With K = 8πY/η + 1 and r = K/(N+1): (2π)⁻¹ (K Ψ(r)/r + 4Yπ²/K) < η once Ψ(r)/r < πη/K. -/
import GKSharp.Proofs.FejerAE

namespace GKSharp

namespace Fejer

open Real MeasureTheory Filter Topology Set

/-- `∫_r^π x⁻² ≤ 1/r`. -/
lemma integral_inv_sq_le {r : ℝ} (hr : 0 < r) (hrπ : r ≤ π) : ∫ x in r..π, x ^ (-2 : ℤ) ≤ r⁻¹ := by
  have h0 : (0 : ℝ) ∉ uIcc r π := by
    rw [uIcc_of_le hrπ, mem_Icc]
    intro h
    linarith [h.1]
  rw [integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  norm_num
  have : 0 < π⁻¹ := inv_pos.2 pi_pos
  linarith

/-- The tail: `|h| ≤ B` gives `∫_r^π h F_N ≤ B π²/((N+1) r)`. -/
lemma tail_le {h : ℝ → ℝ} (hh : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) (N : ℕ)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ π) :
    ∫ x in r..π, h x * kerF N x ≤ B * π ^ 2 / (((N : ℝ) + 1) * r) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set c := B * π ^ 2 / ((N : ℝ) + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  have h0 : (0 : ℝ) ∉ uIcc r π := by
    rw [uIcc_of_le hrπ, mem_Icc]
    intro h
    linarith [h.1]
  have hint : IntervalIntegrable (fun x => h x * kerF N x) volume r π :=
    intervalIntegrable_mul_kerF hh hB N id continuous_id r π
  have hint2 : IntervalIntegrable (fun x => c * x ^ (-2 : ℤ)) volume r π :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr h0)).const_mul c
  calc ∫ x in r..π, h x * kerF N x ≤ ∫ x in r..π, c * x ^ (-2 : ℤ) := by
        refine intervalIntegral.integral_mono_on hrπ hint hint2 fun x hx => ?_
        have hx0 : 0 < x := lt_of_lt_of_le hr hx.1
        have hxπ : |x| ≤ π := by rw [abs_of_pos hx0]; exact hx.2
        have hk := kerF_le_tail N hx0.ne' hxπ
        have hhB : h x ≤ B := (le_abs_self _).trans (hB x)
        calc h x * kerF N x ≤ B * (π ^ 2 / (((N : ℝ) + 1) * x ^ 2)) :=
              mul_le_mul hhB hk (kerF_nonneg N x) hB0
          _ = c * x ^ (-2 : ℤ) := by
              rw [hc, zpow_neg, zpow_two]
              field_simp
    _ = c * ∫ x in r..π, x ^ (-2 : ℤ) := intervalIntegral.integral_const_mul _ _
    _ ≤ c * r⁻¹ := mul_le_mul_of_nonneg_left (integral_inv_sq_le hr hrπ) hc0
    _ = B * π ^ 2 / (((N : ℝ) + 1) * r) := by rw [hc]; field_simp

/-- The split: `∫_{-π}^{π} g F_N ≤ (N+1) ∫_{-r}^{r} g + 4Yπ²/((N+1) r)` for `g = |u(t - ·) - u t|`. -/
lemma split_le {u : ℝ → ℝ} (hu : Measurable u) {Y : ℝ} (hY : ∀ t, |u t| ≤ Y) (N : ℕ) (t : ℝ)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ π) :
    ∫ x in (-π)..π, |u (t - x) - u t| * kerF N x ≤
      ((N : ℝ) + 1) * (∫ x in (-r)..r, |u (t - x) - u t|) + 4 * Y * π ^ 2 / (((N : ℝ) + 1) * r) := by
  set g : ℝ → ℝ := fun x => |u (t - x) - u t| with hg
  have hgm : Measurable g := by rw [hg]; fun_prop
  have hgB : ∀ x, |g x| ≤ 2 * Y := fun x => by
    rw [hg, abs_abs]
    calc |u (t - x) - u t| ≤ |u (t - x)| + |u t| := abs_sub _ _
      _ ≤ 2 * Y := by linarith [hY (t - x), hY t]
  have hgn : ∀ x, 0 ≤ g x := fun x => abs_nonneg _
  have hgnm : Measurable fun x => g (-x) := hgm.comp measurable_neg
  have hint : ∀ a b, IntervalIntegrable (fun x => g x * kerF N x) volume a b := fun a b =>
    intervalIntegrable_mul_kerF hgm hgB N id continuous_id a b
  have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  -- the three pieces
  have hleft : ∫ x in (-π)..(-r), g x * kerF N x ≤ 2 * Y * π ^ 2 / (((N : ℝ) + 1) * r) := by
    have h := intervalIntegral.integral_comp_neg (a := r) (b := π) (fun x => g x * kerF N x)
    simp only [kerF_neg] at h
    rw [← h]
    exact tail_le hgnm (fun x => hgB (-x)) N hr hrπ
  have hright : ∫ x in r..π, g x * kerF N x ≤ 2 * Y * π ^ 2 / (((N : ℝ) + 1) * r) :=
    tail_le hgm hgB N hr hrπ
  have hmid : ∫ x in (-r)..r, g x * kerF N x ≤ ((N : ℝ) + 1) * ∫ x in (-r)..r, g x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith) (hint _ _)
      ((intervalIntegrable_of_bdd hgm hgB _ _).const_mul _) fun x _ => ?_
    rw [mul_comm ((N : ℝ) + 1)]
    exact mul_le_mul_of_nonneg_left (kerF_le N x) (hgn x)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-π) (-r)) (hint (-r) π),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (-r) r) (hint r π)]
  have h4 : 4 * Y * π ^ 2 / (((N : ℝ) + 1) * r) =
      2 * Y * π ^ 2 / (((N : ℝ) + 1) * r) + 2 * Y * π ^ 2 / (((N : ℝ) + 1) * r) := by ring
  rw [h4]
  linarith

/-- O23 part 2(b) at one point: Fejér means converge at a Lebesgue point. -/
theorem tendsto_of_lebesgue_point {u : ℝ → ℝ} (hu : Measurable u) (hper : Function.Periodic u (2 * π))
    {Y : ℝ} (hY : ∀ t, |u t| ≤ Y) {t : ℝ}
    (hL : Tendsto (fun r : ℝ => (∫ x in (-r)..r, |u (t - x) - u t|) / r) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun N => fejerMean u N t) atTop (𝓝 (u t)) := by
  have hY0 : 0 ≤ Y := (abs_nonneg _).trans (hY 0)
  rw [Metric.tendsto_atTop]
  intro η hη
  set K : ℝ := 8 * π * Y / η + 1 with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨ρ0, hρ0, hρ⟩ := Metric.tendsto_nhdsWithin_nhds.1 hL (π * η / K) (by positivity)
  set m := min ρ0 π with hm
  have hm0 : 0 < m := lt_min hρ0 pi_pos
  refine ⟨⌈K / m⌉₊, fun N hN => ?_⟩
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set r := K / ((N : ℝ) + 1) with hr
  have hr0 : 0 < r := by positivity
  have hrm : r < m := by
    have hc : K / m ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rw [hr, div_lt_iff₀ hN1]
    rw [div_le_iff₀ hm0] at hc
    nlinarith
  have hrπ : r ≤ π := (hrm.trans_le (min_le_right _ _)).le
  have hrρ : r < ρ0 := hrm.trans_le (min_le_left _ _)
  have hΨ := hρ (mem_Ioi.2 hr0) (by rw [Real.dist_eq, sub_zero, abs_of_pos hr0]; exact hrρ)
  rw [Real.dist_eq, sub_zero] at hΨ
  have hΨ' : (∫ x in (-r)..r, |u (t - x) - u t|) / r < π * η / K := (le_abs_self _).trans_lt hΨ
  have hNr : ((N : ℝ) + 1) * r = K := by rw [hr]; field_simp
  have hmain : ((N : ℝ) + 1) * (∫ x in (-r)..r, |u (t - x) - u t|) < π * η := by
    have h1 : ((N : ℝ) + 1) * (∫ x in (-r)..r, |u (t - x) - u t|) =
        K * ((∫ x in (-r)..r, |u (t - x) - u t|) / r) := by rw [← hNr]; field_simp
    rw [h1]
    calc K * ((∫ x in (-r)..r, |u (t - x) - u t|) / r) < K * (π * η / K) :=
          mul_lt_mul_of_pos_left hΨ' hK0
      _ = π * η := by field_simp
  have htail : 4 * Y * π ^ 2 / (((N : ℝ) + 1) * r) < π * η := by
    rw [hNr, div_lt_iff₀ hK0]
    have : η * K = 8 * π * Y + η := by rw [hK]; field_simp
    nlinarith [pi_pos]
  have hsplit := split_le hu hY N t hr0 hrπ
  have hπ : 0 < 2 * π := by positivity
  rw [Real.dist_eq, fejerMean_sub_eq hu hper hY N t, abs_mul, abs_of_pos (inv_pos.2 hπ)]
  have habs : |∫ x in (-π)..π, (u (t - x) - u t) * kerF N x| ≤ ∫ x in (-π)..π, |u (t - x) - u t| * kerF N x := by
    refine (intervalIntegral.abs_integral_le_integral_abs (by linarith [pi_pos])).trans_eq ?_
    exact intervalIntegral.integral_congr fun x _ => by
      rw [abs_mul, abs_of_nonneg (kerF_nonneg N x)]
  calc (2 * π)⁻¹ * |∫ x in (-π)..π, (u (t - x) - u t) * kerF N x|
      ≤ (2 * π)⁻¹ * (((N : ℝ) + 1) * (∫ x in (-r)..r, |u (t - x) - u t|) +
          4 * Y * π ^ 2 / (((N : ℝ) + 1) * r)) := by
        gcongr
        exact habs.trans hsplit
    _ < (2 * π)⁻¹ * (π * η + π * η) := by gcongr
    _ = η := by field_simp; norm_num

end Fejer

end GKSharp
