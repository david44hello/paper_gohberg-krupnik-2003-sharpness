/- p-norm periodization limit, frozen target slice_N09 (norm_correspondence.tex l.46-51, short v0.70).
Copyright (C) Dave Goel 2026--now. -/
import Mathlib

open MeasureTheory Real Filter Topology

namespace GKSharp.Proofs.N09Periodization

/-- Quadratic decay of a Schwartz function. -/
theorem schwartz_quadratic_decay (f : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2 := by
  have key : ∀ x : ℝ, (1 + |x|) ^ 2 * ‖f x‖ ≤
      2 ^ 2 * (Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
    intro x
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((2 : ℕ), (0 : ℕ)))
      (k := 2) (n := 0) le_rfl le_rfl f x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  refine ⟨_, le_trans (by positivity) (key 0), fun x => ?_⟩
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact key x

/-- From the decay bound: a lower bound `y ≤ |x|` gives `‖f x‖ ≤ C / y ^ 2`. -/
theorem norm_le_of_le_abs {f : SchwartzMap ℝ ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2) {x y : ℝ} (hy : 0 < y) (hyx : y ≤ |x|) :
    ‖f x‖ ≤ C / y ^ 2 := by
  refine (hdec x).trans ?_
  apply div_le_div_of_nonneg_left hC (by positivity)
  have : y ≤ 1 + |x| := by linarith
  exact pow_le_pow_left₀ hy.le this 2

/-- For `|s| ≤ π N` and `k ≠ 0`, the shifted point is far away. -/
theorem abs_shift_ge {N : ℕ} {s : ℝ} (hs : |s| ≤ π * N) {k : ℤ} (hk : k ≠ 0) :
    |(k : ℝ)| * (π * N) ≤ |s + (N : ℝ) * (2 * π * k)| := by
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  have hpN : 0 ≤ π * N := by positivity
  have h1 : |(N : ℝ) * (2 * π * k)| = 2 * (π * N) * |(k : ℝ)| := by
    rw [abs_mul, abs_mul, abs_mul, Nat.abs_cast, abs_of_pos two_pos, abs_of_pos pi_pos]; ring
  have h2 : |(N : ℝ) * (2 * π * k)| - |s| ≤ |s + (N : ℝ) * (2 * π * k)| := by
    have := abs_sub_abs_le_abs_sub ((N : ℝ) * (2 * π * k)) (-s)
    rwa [abs_neg, sub_neg_eq_add, add_comm] at this
  rw [h1] at h2
  nlinarith

/-- The periodization of `f` with period `2 π N`, in the shape used by the target. -/
noncomputable def periodized (f : SchwartzMap ℝ ℂ) (N : ℕ) (s : ℝ) : ℂ :=
  ∑' k : ℤ, f (s + (N : ℝ) * (2 * π * k))

/-- The summable majorant `C / (π N)^2 * (1 / k^2)` (it vanishes at `k = 0`). -/
noncomputable def tailMajorant (C : ℝ) (N : ℕ) (k : ℤ) : ℝ :=
  C / (π * N) ^ 2 * (1 / (k : ℝ) ^ 2)

/-- `ζ = ∑_{k ∈ ℤ} 1 / k^2` (the `k = 0` term is `0` in Lean). -/
noncomputable def zetaTwo : ℝ := ∑' k : ℤ, 1 / (k : ℝ) ^ 2

theorem summable_inv_sq_int : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
  summable_one_div_int_pow.mpr one_lt_two

theorem zetaTwo_nonneg : 0 ≤ zetaTwo :=
  tsum_nonneg fun k => by positivity

theorem hasSum_tailMajorant (C : ℝ) (N : ℕ) :
    HasSum (tailMajorant C N) (C / (π * N) ^ 2 * zetaTwo) := by
  unfold tailMajorant zetaTwo
  exact summable_inv_sq_int.hasSum.mul_left _

/-- Off the zero index, each shifted term is bounded by the majorant. -/
theorem norm_shift_le_tailMajorant {f : SchwartzMap ℝ ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2) {N : ℕ} (hN : 1 ≤ N) {s : ℝ}
    (hs : |s| ≤ π * N) {k : ℤ} (hk : k ≠ 0) :
    ‖f (s + (N : ℝ) * (2 * π * k))‖ ≤ tailMajorant C N k := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hk1 : (0 : ℝ) < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have hy : 0 < |(k : ℝ)| * (π * N) := by positivity
  refine (norm_le_of_le_abs hC hdec hy (abs_shift_ge hs hk)).trans (le_of_eq ?_)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  unfold tailMajorant
  rw [mul_pow, sq_abs]
  field_simp

/-- The terms with the zero index removed are bounded by the majorant everywhere. -/
theorem norm_ite_shift_le_tailMajorant {f : SchwartzMap ℝ ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2) {N : ℕ} (hN : 1 ≤ N) {s : ℝ}
    (hs : |s| ≤ π * N) (k : ℤ) :
    ‖(if k = 0 then 0 else f (s + (N : ℝ) * (2 * π * k)))‖ ≤ tailMajorant C N k := by
  by_cases hk : k = 0
  · subst hk; simp [tailMajorant]
  · simp only [hk, ↓reduceIte]; exact norm_shift_le_tailMajorant hC hdec hN hs hk

theorem summable_shift {f : SchwartzMap ℝ ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2) {N : ℕ} (hN : 1 ≤ N) {s : ℝ}
    (hs : |s| ≤ π * N) : Summable (fun k : ℤ => f (s + (N : ℝ) * (2 * π * k))) :=
  Summable.of_norm_bounded_eventually (hasSum_tailMajorant C N).summable
    ((eventually_cofinite_ne 0).mono fun _ hk => norm_shift_le_tailMajorant hC hdec hN hs hk)

/-- The periodization differs from `f` by at most `C ζ / (π N)^2` on `|s| ≤ π N`. -/
theorem norm_periodized_sub_le {f : SchwartzMap ℝ ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2) {N : ℕ} (hN : 1 ≤ N) {s : ℝ}
    (hs : |s| ≤ π * N) :
    ‖periodized f N s - f s‖ ≤ C / (π * N) ^ 2 * zetaTwo := by
  unfold periodized
  rw [(summable_shift hC hdec hN hs).tsum_eq_add_tsum_ite 0]
  simp only [Int.cast_zero, mul_zero, add_zero, add_sub_cancel_left]
  exact tsum_of_norm_bounded (hasSum_tailMajorant C N)
    (norm_ite_shift_le_tailMajorant hC hdec hN hs)

/-- Uniform quadratic decay of the periodization on `|s| ≤ π N`. -/
theorem norm_periodized_le {f : SchwartzMap ℝ ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2) {N : ℕ} (hN : 1 ≤ N) {s : ℝ}
    (hs : |s| ≤ π * N) :
    ‖periodized f N s‖ ≤ C * (1 + 4 * zetaTwo) / (1 + |s|) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpiN : 1 ≤ π * N := by nlinarith [pi_gt_three]
  have hle : 1 + |s| ≤ 2 * (π * N) := by linarith
  have hpos : 0 < 1 + |s| := by positivity
  have hsq : (1 + |s|) ^ 2 ≤ 4 * (π * N) ^ 2 := by nlinarith
  have hfrac : C / (π * N) ^ 2 ≤ 4 * C / (1 + |s|) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ‖periodized f N s‖ ≤ ‖f s‖ + ‖periodized f N s - f s‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ C / (1 + |s|) ^ 2 + C / (π * N) ^ 2 * zetaTwo :=
        add_le_add (hdec s) (norm_periodized_sub_le hC hdec hN hs)
    _ ≤ C / (1 + |s|) ^ 2 + 4 * C / (1 + |s|) ^ 2 * zetaTwo := by
        gcongr; exact zetaTwo_nonneg
    _ = C * (1 + 4 * zetaTwo) / (1 + |s|) ^ 2 := by ring

theorem tendsto_bound_zero (K : ℝ) :
    Tendsto (fun N : ℕ => K / (π * N) ^ 2 * zetaTwo) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => (π * N) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp
      (Tendsto.const_mul_atTop pi_pos tendsto_natCast_atTop_atTop)
  simpa using (tendsto_const_nhds.div_atTop h).mul_const zetaTwo

/-- Eventually in `N`, a fixed point `s` satisfies `|s| < π N`. -/
theorem eventually_abs_lt_pi_mul (s : ℝ) : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ |s| < π * N := by
  filter_upwards [eventually_ge_atTop (max 1 (⌈|s|⌉₊ + 1))] with N hN
  refine ⟨le_of_max_le_left hN, ?_⟩
  have h0 : ((⌈|s|⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have h1 : |s| < (N : ℝ) := by
    push_cast at h0
    linarith [Nat.le_ceil |s|]
  have h2 : (N : ℝ) ≤ π * N := by
    nlinarith [pi_gt_three, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  linarith

/-- Pointwise convergence of the periodization to `f`. -/
theorem tendsto_periodized {f : SchwartzMap ℝ ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2) (s : ℝ) :
    Tendsto (fun N : ℕ => periodized f N s) atTop (𝓝 (f s)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (tendsto_bound_zero C)
  filter_upwards [eventually_abs_lt_pi_mul s] with N hN
  exact norm_periodized_sub_le hC hdec hN.1 hN.2.le

/-- The periodization is continuous on `[-π N, π N]` (Weierstrass M-test). -/
theorem continuousOn_periodized {f : SchwartzMap ℝ ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2) {N : ℕ} (hN : 1 ≤ N) :
    ContinuousOn (periodized f N) (Set.Icc (-(π * N)) (π * N)) := by
  refine continuousOn_tsum (u := fun k => tailMajorant C N k + if k = 0 then C else 0)
    (fun k => (f.continuous.comp (continuous_id.add continuous_const)).continuousOn)
    ((hasSum_tailMajorant C N).summable.add (hasSum_ite_eq (0 : ℤ) C).summable) ?_
  intro k x hx
  have hs : |x| ≤ π * N := abs_le.mpr ⟨hx.1, hx.2⟩
  by_cases hk : k = 0
  · subst hk
    have h1 : (1 : ℝ) ≤ (1 + |x|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg x])
    simp only [Int.cast_zero, mul_zero, add_zero, tailMajorant, ↓reduceIte]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, mul_zero,
      zero_add]
    exact (hdec x).trans (div_le_self hC h1)
  · simp only [hk, ↓reduceIte, add_zero]
    exact norm_shift_le_tailMajorant hC hdec hN hs hk

/-- The cut-off `p`-th power of the periodization, as a function on `ℝ`. -/
noncomputable def cutPower (f : SchwartzMap ℝ ℂ) (p : ℝ) (N : ℕ) : ℝ → ℝ :=
  Set.indicator (Set.Ioc (-(π * N)) (π * N)) (fun s => ‖periodized f N s‖ ^ p)

theorem aestronglyMeasurable_cutPower {f : SchwartzMap ℝ ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2) {p : ℝ} (hp : 0 ≤ p) {N : ℕ} (hN : 1 ≤ N) :
    AEStronglyMeasurable (cutPower f p N) volume := by
  unfold cutPower
  rw [aestronglyMeasurable_indicator_iff measurableSet_Ioc]
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
  exact ((continuousOn_periodized hC hdec hN).mono Set.Ioc_subset_Icc_self).norm.rpow_const
    (fun _ _ => Or.inr hp)

/-- The integrable majorant `(K / (1 + |s|)^2)^p`. -/
theorem integrable_majorant {K p : ℝ} (hK : 0 ≤ K) (hp : 1 < p) :
    Integrable (fun s : ℝ => (K / (1 + |s|) ^ 2) ^ p) volume := by
  have hint : Integrable (fun s : ℝ => K ^ p * (1 + ‖s‖) ^ (-(2 * p))) volume :=
    (integrable_one_add_norm (by rw [Module.finrank_self]; push_cast; linarith)).const_mul _
  refine hint.congr (Eventually.of_forall fun s => ?_)
  have hpos : 0 ≤ 1 + |s| := by positivity
  simp only [Real.norm_eq_abs]
  rw [Real.div_rpow hK (by positivity), ← Real.rpow_natCast_mul hpos, Real.rpow_neg hpos,
    div_eq_mul_inv]
  push_cast
  ring_nf

theorem norm_cutPower_le {f : SchwartzMap ℝ ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2) {p : ℝ} (hp : 0 ≤ p) {N : ℕ} (hN : 1 ≤ N)
    (s : ℝ) : ‖cutPower f p N s‖ ≤ (C * (1 + 4 * zetaTwo) / (1 + |s|) ^ 2) ^ p := by
  unfold cutPower
  by_cases hs : s ∈ Set.Ioc (-(π * N)) (π * N)
  · rw [Set.indicator_of_mem hs, Real.norm_of_nonneg (by positivity)]
    have habs : |s| ≤ π * N := abs_le.mpr ⟨hs.1.le, hs.2⟩
    exact Real.rpow_le_rpow (norm_nonneg _) (norm_periodized_le hC hdec hN habs) hp
  · rw [Set.indicator_of_notMem hs, norm_zero]
    have : 0 ≤ C * (1 + 4 * zetaTwo) := mul_nonneg hC (by linarith [zetaTwo_nonneg])
    positivity

theorem tendsto_cutPower {f : SchwartzMap ℝ ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ x : ℝ, ‖f x‖ ≤ C / (1 + |x|) ^ 2) {p : ℝ} (hp : 0 ≤ p) (s : ℝ) :
    Tendsto (fun N : ℕ => cutPower f p N s) atTop (𝓝 (‖f s‖ ^ p)) := by
  refine Tendsto.congr' ?_ ((tendsto_periodized hC hdec s).norm.rpow_const (Or.inr hp))
  filter_upwards [eventually_abs_lt_pi_mul s] with N hN
  have hs : s ∈ Set.Ioc (-(π * N)) (π * N) := ⟨by linarith [neg_abs_le s, hN.2], by
    linarith [le_abs_self s, hN.2]⟩
  unfold cutPower
  rw [Set.indicator_of_mem hs]

/-- Dominated convergence for the cut-off powers. -/
theorem tendsto_integral_cutPower {p : ℝ} (hp : 1 < p) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => ∫ s, cutPower f p N s) atTop (𝓝 (∫ x : ℝ, ‖f x‖ ^ p)) := by
  obtain ⟨C, hC, hdec⟩ := schwartz_quadratic_decay f
  have hp0 : 0 ≤ p := by linarith
  have hK : 0 ≤ C * (1 + 4 * zetaTwo) := mul_nonneg hC (by linarith [zetaTwo_nonneg])
  refine tendsto_integral_filter_of_dominated_convergence
    (fun s => (C * (1 + 4 * zetaTwo) / (1 + |s|) ^ 2) ^ p) ?_ ?_ (integrable_majorant hK hp)
    (Eventually.of_forall fun s => tendsto_cutPower hC hdec hp0 s)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact aestronglyMeasurable_cutPower hC hdec hp0 hN
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact Eventually.of_forall fun s => norm_cutPower_le hC hdec hp0 hN s

/-- The periodization has period `2 π N` (reindex `k ↦ k + 1`). -/
theorem periodized_periodic (f : SchwartzMap ℝ ℂ) (N : ℕ) :
    Function.Periodic (periodized f N) ((N : ℝ) * (2 * π)) := by
  intro s
  unfold periodized
  calc ∑' k : ℤ, f (s + (N : ℝ) * (2 * π) + (N : ℝ) * (2 * π * k))
      = ∑' k : ℤ, f (s + (N : ℝ) * (2 * π * ((Equiv.addRight (1 : ℤ) k : ℤ) : ℝ))) :=
        tsum_congr fun k => by
          simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
          congr 1; ring
    _ = ∑' k : ℤ, f (s + (N : ℝ) * (2 * π * k)) :=
        (Equiv.addRight (1 : ℤ)).tsum_eq (fun j : ℤ => f (s + (N : ℝ) * (2 * π * j)))

/-- Substitution `s = N t`: the target integral over `[0, 2π]` becomes one over `[0, 2πN]`. -/
theorem integral_comp_periodized {p : ℝ} (f : SchwartzMap ℝ ℂ) {N : ℕ} (hN : 1 ≤ N) :
    ∫ t in (0 : ℝ)..(2 * Real.pi),
        ‖(∑' k : ℤ, f ((N : ℝ) * (t + 2 * Real.pi * k)))‖ ^ p =
      (N : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(N : ℝ) * (2 * π), ‖periodized f N s‖ ^ p := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 2 * π)
    (fun s => ‖periodized f N s‖ ^ p) hNpos.ne'
  simp only [mul_zero, smul_eq_mul] at h
  rw [← h]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [periodized, mul_add]

/-- Periodicity: the integral over `[0, 2πN]` equals the integral over `[-πN, πN]`. -/
theorem integral_period_shift {p : ℝ} (f : SchwartzMap ℝ ℂ) (N : ℕ) :
    ∫ s in (0 : ℝ)..(N : ℝ) * (2 * π), ‖periodized f N s‖ ^ p =
      ∫ s in (-(π * N))..(π * N), ‖periodized f N s‖ ^ p := by
  have hper : Function.Periodic (fun s => ‖periodized f N s‖ ^ p) ((N : ℝ) * (2 * π)) :=
    fun s => by simp only [periodized_periodic f N s]
  have h1 := hper.intervalIntegral_add_eq 0 (-(π * N))
  rw [zero_add, show -(π * N) + (N : ℝ) * (2 * π) = π * N by ring] at h1
  exact h1

/-- For `N ≥ 1` the target expression equals the integral of the cut-off power. -/
theorem target_eq_integral_cutPower {p : ℝ} (f : SchwartzMap ℝ ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (2 * Real.pi * N) *
        ((2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi),
          ‖(∑' k : ℤ, f ((N : ℝ) * (t + 2 * Real.pi * k)))‖ ^ p) =
      ∫ s, cutPower f p N s := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [integral_comp_periodized f hN, integral_period_shift f N,
    intervalIntegral.integral_of_le (by nlinarith [pi_pos]), cutPower,
    integral_indicator measurableSet_Ioc]
  field_simp

theorem slice_N09_proved {p : ℝ} (hp : 1 < p) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => (2 * Real.pi * N) *
        ((2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi),
          ‖(∑' k : ℤ, f ((N : ℝ) * (t + 2 * Real.pi * k)))‖ ^ p))
      atTop (𝓝 (∫ x : ℝ, ‖f x‖ ^ p)) := by
  refine (tendsto_integral_cutPower hp f).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (target_eq_integral_cutPower f hN).symm

end GKSharp.Proofs.N09Periodization

#print axioms GKSharp.Proofs.N09Periodization.slice_N09_proved
