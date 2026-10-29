/-
  GKSharp/Proofs/Select.lean - generic continuous and trigonometric near-minimizers

  Route. (A) Grid `θ_j = j h`, `h = 2π/N`; a minimizer `v_j` at each `θ_j` is `2ε₁`-near-minimal on all of
  `[θ_j, θ_{j+1}]` (uniform continuity of `F` on a compact box). A continuous plateau function (value `v_j`,
  ramps of width `η` before each `θ_{j+1}`, clamped to `[-R, R]`, `v_N := v_0`) then has
  `∫ F θ (g θ) ≤ ∫ μ + 2ε₁·2π + N η K`. (B) Stone-Weierstrass on `AddCircle (2π)`
  (`span_fourier_closure_eq_top`) gives a trigonometric polynomial uniformly close to `g`; uniform continuity
  of `F` again transfers the integral bound.
-/
import GKSharp.Defs.Pencil

open Real Set

namespace GKSharp

/-- Uniform continuity of `F` on the box `[0,2π] × [-(R+1), R+1]`, coordinate-wise. -/
lemma box_uc (F : ℝ → ℝ → ℝ) (hF : Continuous (Function.uncurry F)) (R ε1 : ℝ) (hε1 : 0 < ε1) :
    ∃ δ > 0, ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ θ' ∈ Icc (0 : ℝ) (2 * π), ∀ u ∈ Icc (-(R + 1)) (R + 1),
      ∀ v ∈ Icc (-(R + 1)) (R + 1), |θ - θ'| < δ → |u - v| < δ → |F θ u - F θ' v| < ε1 := by
  have hK : IsCompact (Icc (0 : ℝ) (2 * π) ×ˢ Icc (-(R + 1)) (R + 1)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ, hδ, h⟩ :=
    Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hF.continuousOn) ε1 hε1
  refine ⟨δ, hδ, fun θ hθ θ' hθ' u hu v hv h1 h2 => ?_⟩
  have := h (θ, u) ⟨hθ, hu⟩ (θ', v) ⟨hθ', hv⟩
    (by rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact max_lt h1 h2)
  simpa [Real.dist_eq] using this

/-- `F` is bounded on the box `[0,2π] × [-(R+1), R+1]`. -/
lemma box_bound (F : ℝ → ℝ → ℝ) (hF : Continuous (Function.uncurry F)) (R : ℝ) :
    ∃ M, ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ u ∈ Icc (-(R + 1)) (R + 1), |F θ u| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (2 * π) ×ˢ Icc (-(R + 1)) (R + 1)) hF.continuousOn
  exact ⟨M, fun θ hθ u hu => by simpa using hM (θ, u) ⟨hθ, hu⟩⟩

/-- A pointwise bound `f ≤ m + c` on `[a, b]` integrates to `∫ f ≤ ∫ m + c (b - a)`. -/
lemma integral_le_of_pointwise (f m : ℝ → ℝ) (hf : Continuous f) (hm : Continuous m) {a b c : ℝ}
    (hab : a ≤ b) (h : ∀ θ ∈ Icc a b, f θ ≤ m θ + c) :
    ∫ θ in a..b, f θ ≤ (∫ θ in a..b, m θ) + c * (b - a) := by
  have h1 := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (g := fun θ => m θ + c) hab (hf.intervalIntegrable a b)
    ((hm.add continuous_const).intervalIntegrable a b) h
  rw [intervalIntegral.integral_add (hm.intervalIntegrable a b) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at h1
  linarith

/-- The ramp from `0` (at `t - η`) up to `1` (at `t`). -/
noncomputable def ramp (t η θ : ℝ) : ℝ := max 0 (min 1 ((θ - (t - η)) / η))

lemma ramp_eq_one {t η θ : ℝ} (hη : 0 < η) (h : t ≤ θ) : ramp t η θ = 1 := by
  unfold ramp
  have : 1 ≤ (θ - (t - η)) / η := by rw [le_div_iff₀ hη]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

lemma ramp_eq_zero {t η θ : ℝ} (hη : 0 < η) (h : θ ≤ t - η) : ramp t η θ = 0 := by
  unfold ramp
  have : (θ - (t - η)) / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
  exact max_eq_left (le_trans (min_le_right _ _) this)

lemma continuous_ramp (t η : ℝ) : Continuous (ramp t η) := by
  unfold ramp
  fun_prop

/-- The plateau function: value `w j` on `[j h, (j+1) h - η]`, a ramp of width `η` before each `(j+1) h`. -/
noncomputable def plateau (w : ℕ → ℝ) (N : ℕ) (h η θ : ℝ) : ℝ :=
  w 0 + ∑ i ∈ Finset.range N, (w (i + 1) - w i) * ramp ((i + 1) * h) η θ

lemma continuous_plateau (w : ℕ → ℝ) (N : ℕ) (h η : ℝ) : Continuous (plateau w N h η) := by
  unfold plateau
  exact continuous_const.add
    (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_ramp _ _))

lemma plateau_eq (w : ℕ → ℝ) {N : ℕ} {h η θ : ℝ} (hη : 0 < η) (hh : 0 ≤ h) {j : ℕ} (hj : j ≤ N)
    (hθ : θ ∈ Icc (j * h) ((j + 1) * h - η)) : plateau w N h η θ = w j := by
  unfold plateau
  rw [← Finset.sum_range_add_sum_Ico _ hj]
  have h1 : ∑ i ∈ Finset.range j, (w (i + 1) - w i) * ramp ((i + 1) * h) η θ
      = ∑ i ∈ Finset.range j, (w (i + 1) - w i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : (i : ℝ) + 1 ≤ j := by exact_mod_cast Finset.mem_range.mp hi
    have := mul_le_mul_of_nonneg_right hij hh
    rw [ramp_eq_one hη (by linarith [hθ.1]), mul_one]
  have h2 : ∑ i ∈ Finset.Ico j N, (w (i + 1) - w i) * ramp ((i + 1) * h) η θ = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hji : (j : ℝ) + 1 ≤ i + 1 := by
      have : (j : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Ico.mp hi).1
      linarith
    have := mul_le_mul_of_nonneg_right hji hh
    rw [ramp_eq_zero hη (by linarith [hθ.2]), mul_zero]
  rw [h1, h2, Finset.sum_range_sub w j]
  ring

/-- Step A: a continuous, `2π`-periodic-at-the-ends, `[-R, R]`-valued near-minimizer. -/
lemma exists_cont_near_min (F : ℝ → ℝ → ℝ) (hF : Continuous (Function.uncurry F)) (μ : ℝ → ℝ)
    (hμ : Continuous μ) (R : ℝ)
    (hmin : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∃ v ∈ Icc (-R) R, F θ v = μ θ)
    (hle : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ v : ℝ, μ θ ≤ F θ v)
    (ε' : ℝ) (hε' : 0 < ε') :
    ∃ g : ℝ → ℝ, Continuous g ∧ g 0 = g (2 * π) ∧ (∀ θ, g θ ∈ Icc (-R) R) ∧
      ∫ θ in (0 : ℝ)..(2 * π), F θ (g θ) ≤ (∫ θ in (0 : ℝ)..(2 * π), μ θ) + ε' := by
  have hπ : 0 < 2 * π := by positivity
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) (2 * π) := ⟨le_rfl, hπ.le⟩
  have hR : 0 ≤ R := by
    obtain ⟨v, hv, -⟩ := hmin 0 h0mem
    linarith [hv.1, hv.2]
  have hbox : ∀ v ∈ Icc (-R) R, v ∈ Icc (-(R + 1)) (R + 1) := fun v hv => ⟨by linarith [hv.1], by linarith [hv.2]⟩
  -- bounds
  obtain ⟨Fm, hFm⟩ := box_bound F hF R
  obtain ⟨Mμ, hMμ⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) (2 * π)) hμ.continuousOn
  have hFm0 : 0 ≤ Fm := le_trans (abs_nonneg _) (hFm 0 h0mem 0 (hbox 0 ⟨by linarith, hR⟩))
  have hMμ0 : 0 ≤ Mμ := le_trans (norm_nonneg _) (hMμ 0 h0mem)
  set K := Fm + Mμ with hKdef
  have hK : 0 ≤ K := by positivity
  have hcrude : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ v ∈ Icc (-R) R, F θ v ≤ μ θ + K := by
    intro θ hθ v hv
    have h1 := (abs_le.mp (hFm θ hθ v (hbox v hv))).2
    have h2 := hMμ θ hθ
    rw [Real.norm_eq_abs] at h2
    linarith [(abs_le.mp h2).1]
  -- uniform continuity
  set ε1 := ε' / (8 * π) with hε1def
  have hε1 : 0 < ε1 := by positivity
  obtain ⟨δ, hδ, hUC⟩ := box_uc F hF R ε1 hε1
  -- the grid
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * π / δ)
  have hN0 : (0 : ℝ) < N := lt_trans (div_pos hπ hδ) hN
  set h := 2 * π / N with hhdef
  have hh : 0 < h := div_pos hπ hN0
  have hhδ : h < δ := by
    rw [div_lt_iff₀ hN0]; rw [div_lt_iff₀ hδ] at hN; linarith
  have hNh : (N : ℝ) * h = 2 * π := by rw [hhdef]; field_simp
  set η := min (h / 2) (ε' / (2 * (N * K + 1))) with hηdef
  have hd : 0 < 2 * ((N : ℝ) * K + 1) := by positivity
  have hη : 0 < η := lt_min (by positivity) (div_pos hε' hd)
  have hηh : η < h := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hNKη : (N : ℝ) * K * η ≤ ε' / 2 := by
    have h1 : η * (2 * ((N : ℝ) * K + 1)) ≤ ε' := (le_div_iff₀ hd).mp (min_le_right _ _)
    nlinarith
  -- plateau values: a minimizer at each grid point
  have hsel : ∀ j : ℕ, ∃ v ∈ Icc (-R) R,
      j < N → ∀ θ ∈ Icc ((j : ℝ) * h) ((j + 1) * h), F θ v ≤ μ θ + 2 * ε1 := by
    intro j
    by_cases hj : j < N
    · have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
      have hj1 : ((j : ℝ) + 1) * h ≤ 2 * π := by
        rw [← hNh]; exact mul_le_mul_of_nonneg_right hjN hh.le
      have hθj : (j : ℝ) * h ∈ Icc (0 : ℝ) (2 * π) := ⟨by positivity, by nlinarith⟩
      obtain ⟨v0, hv0R, hv0⟩ := hmin _ hθj
      refine ⟨v0, hv0R, fun _ θ hθ => ?_⟩
      have hθmem : θ ∈ Icc (0 : ℝ) (2 * π) := ⟨le_trans hθj.1 hθ.1, le_trans hθ.2 hj1⟩
      obtain ⟨vθ, hvθR, hvθ⟩ := hmin θ hθmem
      have hdist : |θ - (j : ℝ) * h| < δ := by
        rw [abs_lt]; constructor <;> nlinarith [hθ.1, hθ.2]
      have hdist' : |(j : ℝ) * h - θ| < δ := by rwa [abs_sub_comm]
      have e1 := (abs_lt.mp (hUC θ hθmem _ hθj v0 (hbox v0 hv0R) v0 (hbox v0 hv0R) hdist
        (by simp [hδ]))).2
      have e2 := hle _ hθj vθ
      have e3 := (abs_lt.mp (hUC _ hθj θ hθmem vθ (hbox vθ hvθR) vθ (hbox vθ hvθR) hdist'
        (by simp [hδ]))).2
      linarith
    · exact ⟨0, ⟨by linarith, hR⟩, fun h' => absurd h' hj⟩
  choose vs hvsR hvs using hsel
  set w : ℕ → ℝ := fun j => vs (j % N) with hwdef
  have hwR : ∀ j, w j ∈ Icc (-R) R := fun j => hvsR _
  have hwlt : ∀ j < N, w j = vs j := fun j hj => by rw [hwdef]; dsimp only; rw [Nat.mod_eq_of_lt hj]
  set g : ℝ → ℝ := fun θ => max (-R) (min R (plateau w N h η θ)) with hgdef
  have hclamp : ∀ x ∈ Icc (-R) R, max (-R) (min R x) = x := fun x hx => by
    rw [min_eq_right hx.2, max_eq_right hx.1]
  have hg_eq : ∀ j ≤ N, ∀ θ ∈ Icc ((j : ℝ) * h) ((j + 1) * h - η), g θ = w j := by
    intro j hj θ hθ
    rw [hgdef]; dsimp only
    rw [plateau_eq w hη hh.le hj hθ, hclamp _ (hwR j)]
  have hgc : Continuous g := continuous_const.max (continuous_const.min (continuous_plateau w N h η))
  have hgR : ∀ θ, g θ ∈ Icc (-R) R := fun θ =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hNpos : 0 < N := by exact_mod_cast hN0
  have hg0 : g 0 = w 0 := hg_eq 0 (Nat.zero_le _) 0 ⟨by simp, by simp; linarith⟩
  have hg2π : g (2 * π) = w N := hg_eq N le_rfl (2 * π) ⟨by rw [hNh], by nlinarith⟩
  have hwN : w N = w 0 := by rw [hwdef]; dsimp only; rw [Nat.mod_self, Nat.zero_mod]
  refine ⟨g, hgc, by rw [hg0, hg2π, hwN], hgR, ?_⟩
  -- the integral estimate
  have hfc : Continuous fun θ => F θ (g θ) := hF.comp (continuous_id.prodMk hgc)
  have hpiece : ∀ j < N, ∫ θ in ((j : ℝ) * h)..((j + 1) * h), F θ (g θ)
      ≤ (∫ θ in ((j : ℝ) * h)..((j + 1) * h), μ θ) + (2 * ε1 * h + K * η) := by
    intro j hj
    have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    have hj1 : ((j : ℝ) + 1) * h ≤ 2 * π := by
      rw [← hNh]; exact mul_le_mul_of_nonneg_right hjN hh.le
    have hj0 : 0 ≤ (j : ℝ) * h := by positivity
    have hab1 : (j : ℝ) * h ≤ (j + 1) * h - η := by nlinarith
    have hab2 : ((j : ℝ) + 1) * h - η ≤ (j + 1) * h := by linarith
    have i1 := integral_le_of_pointwise _ _ hfc hμ (c := 2 * ε1) hab1 fun θ hθ => by
      rw [hg_eq j hj.le θ hθ, hwlt j hj]
      exact hvs j hj θ ⟨hθ.1, by linarith [hθ.2]⟩
    have i2 := integral_le_of_pointwise _ _ hfc hμ (c := K) hab2 fun θ hθ =>
      hcrude θ ⟨by linarith [hθ.1], le_trans hθ.2 hj1⟩ (g θ) (hgR θ)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _), ← intervalIntegral.integral_add_adjacent_intervals
      (b := ((j : ℝ) + 1) * h - η) (hμ.intervalIntegrable _ _) (hμ.intervalIntegrable _ _)]
    nlinarith
  have hsum : ∀ f : ℝ → ℝ, Continuous f →
      ∑ j ∈ Finset.range N, ∫ θ in ((j : ℝ) * h)..((j + 1) * h), f θ = ∫ θ in (0 : ℝ)..(2 * π), f θ := by
    intro f hf
    have := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) * h) (n := N)
      (f := f) (μ := MeasureTheory.volume) (fun k _ => hf.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one] at this
    rw [hNh] at this
    exact this
  rw [← hsum _ hfc, ← hsum _ hμ]
  calc ∑ j ∈ Finset.range N, ∫ θ in ((j : ℝ) * h)..((j + 1) * h), F θ (g θ)
      ≤ ∑ j ∈ Finset.range N, ((∫ θ in ((j : ℝ) * h)..((j + 1) * h), μ θ) + (2 * ε1 * h + K * η)) :=
        Finset.sum_le_sum fun j hj => hpiece j (Finset.mem_range.mp hj)
    _ = (∑ j ∈ Finset.range N, ∫ θ in ((j : ℝ) * h)..((j + 1) * h), μ θ)
          + N * (2 * ε1 * h + K * η) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ _ := by
        have e1 : (N : ℝ) * (2 * ε1 * h + K * η) = 2 * ε1 * (N * h) + N * K * η := by ring
        have e2 : 2 * ε1 * (2 * π) = ε' / 2 := by rw [hε1def]; field_simp; ring
        rw [e1, hNh, e2]
        linarith

/-- Evaluating a Fourier span element at `↑θ` gives `trig`. -/
lemma fourier_sum_coe_eq_trig (c : ℤ →₀ ℂ) (θ : ℝ) [Fact (0 < 2 * π)] :
    (c.sum fun n a => a • (fourier n : C(AddCircle (2 * π), ℂ))) (θ : AddCircle (2 * π)) = trig c θ := by
  unfold trig Finsupp.sum
  dsimp only
  rw [ContinuousMap.sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ContinuousMap.smul_apply, fourier_coe_apply, smul_eq_mul, mode]
  congr 2
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- A continuous `g` with `g 0 = g (2π)` is uniformly approximated on `[0, 2π]` by `Re` of a trig polynomial. -/
lemma exists_trig_approx (g : ℝ → ℝ) (hg : Continuous g) (hper : g 0 = g (2 * π)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℤ →₀ ℂ, ∀ θ ∈ Icc (0 : ℝ) (2 * π), |(trig c θ).re - g θ| < δ := by
  have : Fact (0 < 2 * π) := ⟨by positivity⟩
  set G : C(AddCircle (2 * π), ℂ) :=
    ⟨fun x => ((AddCircle.liftIco (2 * π) 0 g x : ℝ) : ℂ),
      Complex.continuous_ofReal.comp (AddCircle.liftIco_zero_continuous hper hg.continuousOn)⟩ with hG
  have hGmem : G ∈ ((Submodule.span ℂ (range (@fourier (2 * π)))).topologicalClosure : Set _) := by
    rw [span_fourier_closure_eq_top]; trivial
  rw [Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hGmem
  obtain ⟨P, hP, hdist⟩ := hGmem δ hδ
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hP
  refine ⟨c, fun θ hθ => ?_⟩
  have hGθ : G (θ : AddCircle (2 * π)) = (g θ : ℂ) := by
    rcases eq_or_lt_of_le hθ.2 with h | h
    · rw [h, hG]
      simp only [ContinuousMap.coe_mk]
      rw [AddCircle.coe_period, ← hper]
      rw [show (0 : AddCircle (2 * π)) = ((0 : ℝ) : AddCircle (2 * π)) from rfl]
      rw [AddCircle.liftIco_zero_coe_apply ⟨le_rfl, by positivity⟩]
    · rw [hG]
      simp only [ContinuousMap.coe_mk]
      rw [AddCircle.liftIco_zero_coe_apply ⟨hθ.1, h⟩]
  have hpt := ContinuousMap.dist_apply_le_dist (f := G) (g := c.sum fun i a => a • fourier i)
    (θ : AddCircle (2 * π))
  rw [fourier_sum_coe_eq_trig, hGθ, Complex.dist_eq] at hpt
  have hre : |(trig c θ).re - g θ| ≤ ‖(g θ : ℂ) - trig c θ‖ := by
    rw [← norm_neg, neg_sub]
    calc |(trig c θ).re - g θ| = |(trig c θ - (g θ : ℂ)).re| := by simp
      _ ≤ ‖trig c θ - (g θ : ℂ)‖ := Complex.abs_re_le_norm _
  linarith


lemma continuous_trig (c : ℤ →₀ ℂ) : Continuous (trig c) := by
  unfold trig Finsupp.sum mode
  fun_prop

theorem exists_trig_near_min (F : ℝ → ℝ → ℝ) (hF : Continuous (Function.uncurry F)) (μ : ℝ → ℝ)
    (hμ : Continuous μ) (R : ℝ)
    (hmin : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∃ v ∈ Icc (-R) R, F θ v = μ θ)
    (hle : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ v : ℝ, μ θ ≤ F θ v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℤ →₀ ℂ, ∫ θ in (0 : ℝ)..(2 * π), F θ (trig c θ).re ≤ (∫ θ in (0 : ℝ)..(2 * π), μ θ) + ε := by
  obtain ⟨g, hgc, hgper, hgR, hgint⟩ := exists_cont_near_min F hF μ hμ R hmin hle (ε / 2) (by positivity)
  set ε1 := ε / (8 * π) with hε1def
  obtain ⟨δ, hδ, hUC⟩ := box_uc F hF R ε1 (by positivity)
  obtain ⟨c, hc⟩ := exists_trig_approx g hgc hgper (min δ 1) (lt_min hδ one_pos)
  refine ⟨c, ?_⟩
  have htc : Continuous fun θ => (trig c θ).re := Complex.continuous_re.comp (continuous_trig c)
  have h1 : ∫ θ in (0 : ℝ)..(2 * π), F θ (trig c θ).re
      ≤ (∫ θ in (0 : ℝ)..(2 * π), F θ (g θ)) + ε1 * (2 * π - 0) :=
    integral_le_of_pointwise (fun θ => F θ (trig c θ).re) (fun θ => F θ (g θ))
      (hF.comp (continuous_id.prodMk htc)) (hF.comp (continuous_id.prodMk hgc))
      (by positivity) fun θ hθ => by
        show F θ (trig c θ).re ≤ F θ (g θ) + ε1
        have hcθ := abs_lt.mp (hc θ hθ)
        have hg := hgR θ
        have hδ1 : |(trig c θ).re - g θ| < δ := lt_of_lt_of_le (hc θ hθ) (min_le_left _ _)
        have hm1 : min δ 1 ≤ 1 := min_le_right _ _
        have := hUC θ hθ θ hθ ((trig c θ).re) ⟨by linarith [hg.1, hcθ.1], by linarith [hg.2, hcθ.2]⟩
          (g θ) ⟨by linarith [hg.1], by linarith [hg.2]⟩ (by simp [hδ]) hδ1
        linarith [(abs_lt.mp this).2]
  have e1 : ε1 * (2 * π - 0) = ε / 4 := by rw [hε1def]; field_simp; ring
  linarith

end GKSharp
