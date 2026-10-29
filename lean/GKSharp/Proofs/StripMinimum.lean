/-
GKSharp/Proofs/StripMinimum.lean — the attained rescaled minimum of paper 019 (sec5f_strip.tex l. 16, 20-21, 38-39):
rows `rescaled_minimum` and `h_positive_of_g`, with the exact types of the statement draft.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Route: on the axis `t = 0` at `e^y = (1-s)/s` (every real `y` arises from one `s ∈ (0,1)`),
`Γ(y, 0) - K(1-δ) = δ g(δ, s)`; `g(δ, ·)` is continuous on `(0,1)` and exceeds `g(δ, 1/2)` near both ends
(`g(δ, u) ≥ T₁/u^q - κ`, `≥ T₁/(1-u)^q - κ`, `T₁ > 0`), so it attains its minimum on a compact `[a, 1-a]`;
that minimum gives the least element of the range of `Γ(·, 0)`, hence `h = δ g(δ, s*)`.
-/
import GKSharp.Proofs.StripAnalytic
import GKSharp.Proofs.Sec4bAxis

namespace GKSharp

open Set GKSharp.Threshold GKSharp.Strip

namespace Strip

/-- `C = cDelta p δ > 1` for `δ ∈ (0,1)`. -/
lemma cDelta_gt_one {p delta : ℝ} (hp : 1 < p) (hp2 : p < 2) (hd : delta ∈ Ioo (0 : ℝ) 1) :
    1 < cDelta p delta := by
  rw [cDelta_eq_gk_proved p delta hp hp2 ⟨hd.1.le, hd.2⟩]
  exact lt_of_le_of_lt (le_max_left _ _) (gk_gt_max hp (ne_of_lt hp2) (ρ := ((1 - delta : ℝ) : ℂ))
    (fun h => by
      have : (1 - delta : ℝ) = 1 := by exact_mod_cast h
      linarith [hd.1]))

/-- `T₁ > 0` for `δ ∈ (0,1)`. -/
lemma tOne_pos {p delta : ℝ} (hp : 1 < p) (hp2 : p < 2) (hd : delta ∈ Ioo (0 : ℝ) 1) :
    0 < tOne p delta := by
  have hC := cDelta_gt_one hp hp2 hd
  have hsn := sn_pos hp
  have hsn1 := sn_lt_one hp hp2
  have hCp : 1 < cDelta p delta ^ p := Real.one_lt_rpow hC (by linarith)
  unfold tOne powSlope
  rw [ite_eq_right hC.ne']
  exact div_pos (mul_pos (div_pos (by linarith) (by linarith)) (by linarith)) (mul_pos hsn (by linarith))

/-- The two end bounds `g(δ, u) ≥ T₁/u^q - κ` and `g(δ, u) ≥ T₁/(1-u)^q - κ`. -/
lemma g_lower {p delta u : ℝ} (hp : 1 < p) (hp2 : p < 2) (hd : delta ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    tOne p delta / u ^ q p - kap p delta ≤ g p delta u ∧
      tOne p delta / (1 - u) ^ q p - kap p delta ≤ g p delta u := by
  obtain ⟨hu0, hu1⟩ := hu
  have hT := tOne_pos hp hp2 hd
  have hq : 0 < q p := by unfold q; linarith
  have hphi : 1 ≤ phi p (u * delta) :=
    phi_ge_one_proved p (u * delta) hp.le ⟨by nlinarith [hd.1], by nlinarith [hd.2]⟩
  have hN : tOne p delta ≤ tOne p delta + u * phi p (u * delta) := by nlinarith
  have hv : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
  have hvq : 0 < (u * (1 - u)) ^ q p := Real.rpow_pos_of_pos hv _
  have h1 : (u * (1 - u)) ^ q p ≤ u ^ q p := Real.rpow_le_rpow hv.le (by nlinarith) hq.le
  have h2 : (u * (1 - u)) ^ q p ≤ (1 - u) ^ q p := Real.rpow_le_rpow hv.le (by nlinarith) hq.le
  have hbase : tOne p delta / (u * (1 - u)) ^ q p ≤
      (tOne p delta + u * phi p (u * delta)) / (u * (1 - u)) ^ q p :=
    div_le_div_of_nonneg_right hN hvq.le
  unfold g
  constructor
  · have := div_le_div_of_nonneg_left hT.le hvq h1
    linarith
  · have := div_le_div_of_nonneg_left hT.le hvq h2
    linarith

/-- `g(δ, ·)` is continuous on `(0,1)`. -/
lemma g_continuousOn {p delta : ℝ} (hd : delta ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun u => g p delta u) (Ioo 0 1) := by
  intro u hu
  obtain ⟨hu0, hu1⟩ := hu
  apply ContinuousAt.continuousWithinAt
  have hx : 0 < 1 - u * delta := by nlinarith [hd.1, hd.2]
  have hv : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
  have hphi : ContinuousAt (fun v => phi p (v * delta)) u :=
    (analyticAt_powSlope p hx).continuousAt.comp (f := fun v : ℝ => 1 - v * delta) (by fun_prop)
  have hden : ContinuousAt (fun v : ℝ => (v * (1 - v)) ^ q p) u :=
    ContinuousAt.rpow_const (by fun_prop) (Or.inl hv.ne')
  have hne : (u * (1 - u)) ^ q p ≠ 0 := (Real.rpow_pos_of_pos hv _).ne'
  unfold g
  exact ((continuousAt_const.add (continuousAt_id.mul hphi)).div hden hne).sub continuousAt_const

/-- `g(δ, ·)` attains its minimum on `(0,1)`. -/
lemma g_attains_min {p delta : ℝ} (hp : 1 < p) (hp2 : p < 2) (hd : delta ∈ Ioo (0 : ℝ) 1) :
    ∃ s ∈ Ioo (0 : ℝ) 1, ∀ u ∈ Ioo (0 : ℝ) 1, g p delta s ≤ g p delta u := by
  have hT := tOne_pos hp hp2 hd
  have hq : 0 < q p := by unfold q; linarith
  obtain ⟨M, hM⟩ : ∃ m : ℝ, m = g p delta (1 / 2) := ⟨_, rfl⟩
  have hMk : 0 < M + kap p delta := by
    have h1 := (g_lower hp hp2 hd (u := 1 / 2) ⟨by norm_num, by norm_num⟩).1
    have h2 : 0 < tOne p delta / (1 / 2 : ℝ) ^ q p := div_pos hT (Real.rpow_pos_of_pos (by norm_num) _)
    rw [← hM] at h1
    linarith
  obtain ⟨b, hb⟩ : ∃ x : ℝ, x = (tOne p delta / (M + kap p delta)) ^ (q p)⁻¹ := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; exact Real.rpow_pos_of_pos (div_pos hT hMk) _
  have hbq : b ^ q p = tOne p delta / (M + kap p delta) := by
    rw [hb]; exact Real.rpow_inv_rpow (div_pos hT hMk).le hq.ne'
  obtain ⟨a, ha⟩ : ∃ x : ℝ, x = min (1 / 4) b := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact lt_min (by norm_num) hb0
  have ha4 : a ≤ 1 / 4 := by rw [ha]; exact min_le_left _ _
  have hab : a ≤ b := by rw [ha]; exact min_le_right _ _
  -- below `a`, the end bound exceeds `M`
  have hfar : ∀ v : ℝ, 0 < v → v < a → M < tOne p delta / v ^ q p - kap p delta := by
    intro v hv0 hva
    have hvq : v ^ q p < b ^ q p := Real.rpow_lt_rpow hv0.le (lt_of_lt_of_le hva hab) hq
    have hvq0 : 0 < v ^ q p := Real.rpow_pos_of_pos hv0 _
    rw [hbq, lt_div_iff₀ hMk] at hvq
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hvq0]
    linarith [mul_comm (v ^ q p) (M + kap p delta)]
  have hsub : Icc a (1 - a) ⊆ Ioo 0 1 := fun v hv => ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hhalf_mem : (1 / 2 : ℝ) ∈ Icc a (1 - a) := ⟨by linarith, by linarith⟩
  obtain ⟨s, hs, hmin⟩ :=
    isCompact_Icc.exists_isMinOn ⟨_, hhalf_mem⟩ ((g_continuousOn hd).mono hsub)
  refine ⟨s, hsub hs, fun u hu => ?_⟩
  have hhalf : g p delta s ≤ M := by rw [hM]; exact isMinOn_iff.1 hmin _ hhalf_mem
  by_cases hua : u < a
  · have h1 := hfar u hu.1 hua
    have h2 := (g_lower hp hp2 hd hu).1
    linarith
  by_cases hub : 1 - a < u
  · have h1 := hfar (1 - u) (by linarith [hu.2]) (by linarith)
    have h2 := (g_lower hp hp2 hd hu).2
    linarith
  exact isMinOn_iff.1 hmin _ ⟨not_lt.1 hua, not_lt.1 hub⟩

/-- On the axis at `e^y = (1-s)/s`: `Γ(y, 0) - K(1-δ) = δ g(δ, s)`. -/
lemma gamma_axis_eq {p delta s : ℝ} (hp : 1 < p) (hp2 : p < 2) (hd : delta ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    GKSharp.gamma p (gk p ((1 - delta : ℝ) : ℂ)) ((1 - delta : ℝ) : ℂ) (Real.log ((1 - s) / s)) 0 -
      kConst p (1 - delta) = delta * g p delta s := by
  obtain ⟨hd0, hd1⟩ := hd
  obtain ⟨hs0, hs1⟩ := hs
  have hcD := cDelta_eq_gk_proved p delta hp hp2 ⟨hd0.le, hd1⟩
  have hs0' : s ≠ 0 := hs0.ne'
  have hs1' : 1 - s ≠ 0 := by linarith
  have hr : 0 < (1 - s) / s := div_pos (by linarith) hs0
  have hey : Real.exp (Real.log ((1 - s) / s)) = (1 - s) / s := Real.exp_log hr
  have hemy : Real.exp (-Real.log ((1 - s) / s)) = s / (1 - s) := by rw [Real.exp_neg, hey, inv_div]
  have hv : 0 < s * (1 - s) := mul_pos hs0 (by linarith)
  have hu : 0 < 1 - s * delta := by nlinarith
  have hA : 2 * Real.cosh (Real.log ((1 - s) / s)) + 2 = 1 ^ 2 / (s * (1 - s)) := by
    rw [Real.cosh_eq, hey, hemy]
    field_simp
    ring
  have hB : Real.exp (Real.log ((1 - s) / s)) + (1 - delta) ^ 2 * Real.exp (-Real.log ((1 - s) / s)) +
      2 * (1 - delta) = (1 - s * delta) ^ 2 / (s * (1 - s)) := by
    rw [hey, hemy]
    field_simp
    ring
  have hN := num_form hp hp2 hd1 hd0.ne' hs0
  have hK : delta * kap p delta = kConst p (1 - delta) := by
    unfold kap kConst
    rw [hcD]
    simp only [sn, cs, q]
    ring_nf
  have hvq : (s * (1 - s)) ^ (p / 2) ≠ 0 := (Real.rpow_pos_of_pos hv _).ne'
  rw [sec4b_gamma_axis, hA, hB, sec4b_sq_div_rpow zero_le_one hv.le, sec4b_sq_div_rpow hu.le hv.le,
    Real.one_rpow, ← hK, ← hcD]
  unfold g
  rw [hN]
  unfold q
  field_simp

/-- Every real `y` is `log((1-s)/s)` for some `s ∈ (0,1)`. -/
lemma log_ratio_surj (y : ℝ) : ∃ s ∈ Ioo (0 : ℝ) 1, Real.log ((1 - s) / s) = y := by
  have he := Real.exp_pos y
  have h1 : (1 + Real.exp y) ≠ 0 := by positivity
  refine ⟨1 / (1 + Real.exp y), ⟨by positivity, by rw [div_lt_one (by positivity)]; linarith⟩, ?_⟩
  have hratio : (1 - 1 / (1 + Real.exp y)) / (1 / (1 + Real.exp y)) = Real.exp y := by
    field_simp
    ring
  rw [hratio, Real.log_exp]

end Strip

/-- S:16,20–21, row `rescaled_minimum`: the minimum exists, and `h(1-δ) = δ g(δ, s*)`. -/
theorem rescaled_minimum_proved (p delta : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hd : delta ∈ Ioo (0 : ℝ) 1) :
    ∃ s ∈ Ioo (0 : ℝ) 1, h p (1 - delta) = delta * g p delta s ∧
      ∀ u ∈ Ioo (0 : ℝ) 1, g p delta s ≤ g p delta u := by
  obtain ⟨s, hs, hmin⟩ := Strip.g_attains_min hp hp2 hd
  refine ⟨s, hs, ?_, hmin⟩
  obtain ⟨Γ, hΓ⟩ : ∃ f : ℝ → ℝ,
      f = fun y => GKSharp.gamma p (gk p ((1 - delta : ℝ) : ℂ)) ((1 - delta : ℝ) : ℂ) y 0 := ⟨_, rfl⟩
  have hs_eq := Strip.gamma_axis_eq hp hp2 hd hs
  have hleast : IsLeast (Set.range Γ) (Γ (Real.log ((1 - s) / s))) := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    rintro _ ⟨y, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Strip.log_ratio_surj y
    have hu_eq := Strip.gamma_axis_eq hp hp2 hd hu
    have hle := mul_le_mul_of_nonneg_left (hmin u hu) hd.1.le
    rw [hΓ]
    linarith
  unfold Threshold.h GKSharp.axisGap GKSharp.obstacle
  rw [← hΓ, hleast.csInf_eq, hΓ]
  linarith

/-- S:16,38–39, row `h_positive_of_g`: an actual positive minimum. -/
theorem h_positive_of_g_proved (p delta : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hd : delta ∈ Ioo (0 : ℝ) 1) (hg : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < g p delta s) :
    0 < h p (1 - delta) := by
  obtain ⟨s, hs, heq, -⟩ := rescaled_minimum_proved p delta hp hp2 hd
  rw [heq]
  exact mul_pos hd.1 (hg s hs)

end GKSharp
