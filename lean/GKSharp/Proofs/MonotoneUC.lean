/- Lemma U power series, frozen sec5d_monotone.tex:93-99 (row sec5d_Y_series; type verbatim from the
proposal v020).
Route: the coefficients a_n are bounded (|a_(n+1)| ≤ |a_n| once n ≥ m²), so S(t) = Σ a_n tⁿ and its first two
derivatives are term by term on (-1,1); the recurrence makes every coefficient of t(1-t)S'' + (1/2-t)S' + m²S vanish.
Then F(α) = S(sin²α) solves F'' = -4m²F with F(0) = 1, F'(0) = 0. For G = F - cos(2mα) the energy G'² + 4m²G² is
constant on (-π/2,π/2), hence 0; so G' = 0 and G = 0. (The text states the series from the ODE; this is the
uniqueness step it leaves implicit.)
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneUB

namespace GKSharp

open Filter Topology

namespace USeries

/-- Σ (n+1)^j rⁿ converges for 0 < r < 1. -/
theorem summable_succ_pow_mul_geometric (j : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ j * r ^ n) := by
  have hg : Summable (fun n : ℕ => (n : ℝ) ^ j * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one j (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
  have h := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ j * r ^ n) 1).mpr hg
  refine (h.div_const r).congr fun n => ?_
  push_cast
  rw [div_eq_iff hr0.ne', pow_succ]
  ring

/-- n r^(n-1) ≤ (n+1) rⁿ / r. -/
theorem nat_mul_pow_pred_le (n : ℕ) {r : ℝ} (hr0 : 0 < r) :
    (n : ℝ) * r ^ (n - 1) ≤ ((n : ℝ) + 1) * r ^ n / r := by
  rcases n with _ | j
  · simp only [Nat.cast_zero, zero_mul]
    exact div_nonneg (by positivity) hr0.le
  · rw [le_div_iff₀ hr0, Nat.add_sub_cancel, pow_succ]
    push_cast
    nlinarith [mul_pos (pow_pos hr0 j) hr0]

/-- The power series Σ cₙ yⁿ. -/
noncomputable def pseries (c : ℕ → ℝ) (y : ℝ) : ℝ := ∑' n, c n * y ^ n

/-- Coefficients of the derivative series: (n+1) c_(n+1). -/
noncomputable def coefD (c : ℕ → ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) * c (n + 1)

/-- Convergence of a power series with coefficients bounded by M (n+1)^k, on (-1,1). -/
theorem hasSum_pseries {c : ℕ → ℝ} {M : ℝ} {k : ℕ} (hc : ∀ n, |c n| ≤ M * ((n : ℝ) + 1) ^ k)
    {t : ℝ} (ht : |t| < 1) : HasSum (fun n => c n * t ^ n) (pseries c t) := by
  rcases eq_or_lt_of_le (abs_nonneg t) with h0 | hpos
  · have ht0 : t = 0 := abs_eq_zero.mp h0.symm
    subst ht0
    exact ((hasSum_single 0 fun n hn => by simp [hn]).summable).hasSum
  · refine (Summable.of_norm_bounded ((summable_succ_pow_mul_geometric k hpos ht).mul_left M)
      (fun n => ?_)).hasSum
    rw [Real.norm_eq_abs, abs_mul, abs_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hc n) (by positivity)

/-- Term-by-term derivative of a power series with coefficients bounded by M (n+1)^k, on (-1,1). -/
theorem hasDerivAt_powerSeries {c : ℕ → ℝ} {M : ℝ} {k : ℕ} (hc : ∀ n, |c n| ≤ M * ((n : ℝ) + 1) ^ k)
    {t : ℝ} (ht : |t| < 1) : HasDerivAt (pseries c) (pseries (coefD c) t) t := by
  obtain ⟨r, hr⟩ : ∃ r, r = (|t| + 1) / 2 := ⟨_, rfl⟩
  have htr : |t| < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg t) htr
  have hbound : ∀ n (y : ℝ), y ∈ Set.Ioo (-r) r →
      ‖c n * ((n : ℝ) * y ^ (n - 1))‖ ≤ M / r * (((n : ℝ) + 1) ^ (k + 1) * r ^ n) := by
    intro n y hy
    have hy' : |y| ≤ r := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
    have hM : 0 ≤ M * ((n : ℝ) + 1) ^ k := (abs_nonneg _).trans (hc n)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    calc |c n| * ((n : ℝ) * |y| ^ (n - 1))
        ≤ M * ((n : ℝ) + 1) ^ k * ((n : ℝ) * r ^ (n - 1)) := by
          apply mul_le_mul (hc n) _ (by positivity) hM
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) hy' _) (Nat.cast_nonneg n)
      _ ≤ M * ((n : ℝ) + 1) ^ k * (((n : ℝ) + 1) * r ^ n / r) :=
          mul_le_mul_of_nonneg_left (nat_mul_pow_pred_le n hr0) hM
      _ = M / r * (((n : ℝ) + 1) ^ (k + 1) * r ^ n) := by ring
  have ht' : t ∈ Set.Ioo (-r) r := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have h0 : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr0⟩
  have hsum0 : Summable (fun n => c n * (0 : ℝ) ^ n) :=
    (hasSum_single 0 fun n hn => by simp [hn]).summable
  have hsumu : Summable (fun n : ℕ => M / r * (((n : ℝ) + 1) ^ (k + 1) * r ^ n)) :=
    (summable_succ_pow_mul_geometric (k + 1) hr0 hr1).mul_left _
  have hd := hasDerivAt_tsum_of_isPreconnected (g := fun n y => c n * y ^ n)
    (g' := fun n y => c n * ((n : ℝ) * y ^ (n - 1))) hsumu isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => (hasDerivAt_pow n y).const_mul (c n)) hbound h0 hsum0 ht'
  have hsumd : Summable (fun n => c n * ((n : ℝ) * t ^ (n - 1))) :=
    Summable.of_norm_bounded hsumu (fun n => hbound n t ht')
  refine hd.congr_deriv ?_
  rw [hsumd.tsum_eq_zero_add, pseries]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel]
  congr 1
  funext n
  simp only [coefD]
  push_cast
  ring

/-- A HasSum whose first k terms vanish can be read off its shifted tail. -/
theorem hasSum_of_shift {f : ℕ → ℝ} {s : ℝ} (k : ℕ) (h0 : ∀ i < k, f i = 0)
    (h : HasSum (fun n => f (n + k)) s) : HasSum f s := by
  have := (hasSum_nat_add_iff k).mp h
  rwa [Finset.sum_eq_zero (fun i hi => h0 i (Finset.mem_range.mp hi)), add_zero] at this

/-- The coefficients a_n of sec5d:93-95 are bounded. -/
theorem monoCoeffA_bounded (m : ℝ) : ∃ M, ∀ n, |monoCoeffA m n| ≤ M := by
  obtain ⟨N, hN⟩ : ∃ N, N = ⌈m ^ 2⌉₊ := ⟨_, rfl⟩
  refine ⟨∑ j ∈ Finset.range (N + 1), |monoCoeffA m j|, fun n => ?_⟩
  have hle : ∀ j ≤ N, |monoCoeffA m j| ≤ ∑ j ∈ Finset.range (N + 1), |monoCoeffA m j| := fun j hj =>
    Finset.single_le_sum (f := fun j => |monoCoeffA m j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have htail : ∀ j, |monoCoeffA m (N + j)| ≤ |monoCoeffA m N| := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (monoCoeffA_abs_succ_le m (n := N + j) (by omega)).trans ih
  rcases le_or_gt n N with h | h
  · exact hle n h
  · obtain ⟨j, rfl⟩ : ∃ j, n = N + j := ⟨n - N, by omega⟩
    exact (htail j).trans (hle N le_rfl)

/-- The bounds for a, its first and its second derivative coefficients. -/
theorem monoCoeffA_bounds (m : ℝ) : ∃ M, (∀ n, |monoCoeffA m n| ≤ M * ((n : ℝ) + 1) ^ 0) ∧
    (∀ n, |coefD (monoCoeffA m) n| ≤ M * ((n : ℝ) + 1) ^ 1) ∧
    (∀ n, |coefD (coefD (monoCoeffA m)) n| ≤ (2 * M) * ((n : ℝ) + 1) ^ 2) := by
  obtain ⟨M, hM⟩ := monoCoeffA_bounded m
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨M, fun n => by simpa using hM n, fun n => ?_, fun n => ?_⟩
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [coefD, abs_mul, abs_of_pos (by positivity), pow_one, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM _) (by positivity)
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [coefD, coefD, abs_mul, abs_mul, abs_of_pos (by positivity), abs_of_pos (by positivity)]
    push_cast
    have h := hM (n + 1 + 1)
    calc ((n : ℝ) + 1) * (((n : ℝ) + 1 + 1) * |monoCoeffA m (n + 1 + 1)|)
        ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1 + 1) * M) := by gcongr
      _ ≤ 2 * M * ((n : ℝ) + 1) ^ 2 := by
          nlinarith [mul_nonneg (mul_nonneg hM0 hn) (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]

/-- sec5d:91-95: the series S = Σ a_n tⁿ solves the transformed ODE on (-1,1): every coefficient vanishes. -/
theorem pseries_ode (m : ℝ) {M : ℝ} (hb0 : ∀ n, |monoCoeffA m n| ≤ M * ((n : ℝ) + 1) ^ 0)
    (hb1 : ∀ n, |coefD (monoCoeffA m) n| ≤ M * ((n : ℝ) + 1) ^ 1)
    (hb2 : ∀ n, |coefD (coefD (monoCoeffA m)) n| ≤ (2 * M) * ((n : ℝ) + 1) ^ 2) {t : ℝ} (ht : |t| < 1) :
    t * (1 - t) * pseries (coefD (coefD (monoCoeffA m))) t + (1 / 2 - t) * pseries (coefD (monoCoeffA m)) t +
      m ^ 2 * pseries (monoCoeffA m) t = 0 := by
  have hS := hasSum_pseries hb0 ht
  have hS1 := hasSum_pseries hb1 ht
  have hS2 := hasSum_pseries hb2 ht
  have hT1 : HasSum (fun n : ℕ => (n : ℝ) * coefD (monoCoeffA m) n * t ^ n)
      (t * pseries (coefD (coefD (monoCoeffA m))) t) :=
    hasSum_of_shift 1 (fun i hi => by simp [show i = 0 by omega]) (by
      convert hS2.mul_left t using 1
      funext n
      simp only [coefD]
      push_cast
      ring)
  have hT2 : HasSum (fun n : ℕ => ((n : ℝ) - 1) * (n : ℝ) * monoCoeffA m n * t ^ n)
      (t ^ 2 * pseries (coefD (coefD (monoCoeffA m))) t) :=
    hasSum_of_shift 2 (fun i hi => by interval_cases i <;> simp) (by
      convert hS2.mul_left (t ^ 2) using 1
      funext n
      rw [show n + 2 = n + 1 + 1 from rfl]
      simp only [coefD]
      push_cast
      ring)
  have hT3 : HasSum (fun n : ℕ => (n : ℝ) * monoCoeffA m n * t ^ n)
      (t * pseries (coefD (monoCoeffA m)) t) :=
    hasSum_of_shift 1 (fun i hi => by simp [show i = 0 by omega]) (by
      convert hS1.mul_left t using 1
      funext n
      simp only [coefD]
      push_cast
      ring)
  have hall := ((((hT1.sub hT2).add (hS1.mul_left (1 / 2))).sub hT3).add (hS.mul_left (m ^ 2)))
  have hzero : (fun n : ℕ => (n : ℝ) * coefD (monoCoeffA m) n * t ^ n -
      ((n : ℝ) - 1) * (n : ℝ) * monoCoeffA m n * t ^ n + 1 / 2 * (coefD (monoCoeffA m) n * t ^ n) -
      (n : ℝ) * monoCoeffA m n * t ^ n + m ^ 2 * (monoCoeffA m n * t ^ n)) = fun _ => 0 := by
    funext n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hden : ((n : ℝ) + 1) * ((n : ℝ) + 1 / 2) ≠ 0 := by positivity
    simp only [coefD]
    rw [(sec5d_coefficient_recurrence_proved m).2 n]
    field_simp
    ring
  have h0 : HasSum (fun _ : ℕ => (0 : ℝ)) (t * pseries (coefD (coefD (monoCoeffA m))) t -
      t ^ 2 * pseries (coefD (coefD (monoCoeffA m))) t + 1 / 2 * pseries (coefD (monoCoeffA m)) t -
      t * pseries (coefD (monoCoeffA m)) t + m ^ 2 * pseries (monoCoeffA m) t) := by
    convert hall using 1
    exact hzero.symm
  have := h0.unique hasSum_zero
  linear_combination this

end USeries

open USeries

/-- Row `sec5d_Y_series`. -/
theorem sec5d_Y_series_proved (m : ℝ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    HasSum (fun n : ℕ => monoCoeffA m n * t ^ n) (monoY m t) := by
  obtain ⟨M, hb0, hb1, hb2⟩ := monoCoeffA_bounds m
  have hpi := Real.pi_pos
  -- the three series and their derivatives on the open disc
  have hsq : ∀ x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), |Real.sin x ^ 2| < 1 := fun x hx => by
    have hc := Real.cos_pos_of_mem_Ioo hx
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sin_sq_add_cos_sq x, mul_pos hc hc]
  have hD0 := fun x hx => hasDerivAt_powerSeries hb0 (hsq x hx)
  have hD1 := fun x hx => hasDerivAt_powerSeries hb1 (hsq x hx)
  have h2sc : ∀ x : ℝ, HasDerivAt (fun y => 2 * Real.sin y * Real.cos y)
      (2 * (Real.cos x * Real.cos x + Real.sin x * -Real.sin x)) x := fun x => by
    convert ((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)).const_mul 2 using 1
    funext y
    simp only [Pi.mul_apply]
    ring
  -- F = S(sin²), F' = S1(sin²) · 2 sin cos, and F'' = -4 m² F
  have hF : ∀ x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt (fun y => pseries (monoCoeffA m) (Real.sin y ^ 2))
        (pseries (coefD (monoCoeffA m)) (Real.sin x ^ 2) * (2 * Real.sin x * Real.cos x)) x :=
    fun x hx => by
      have h := (hD0 x hx).comp x (sec5d_t_derivatives_proved x).1
      exact h
  have hF1 : ∀ x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt (fun y => pseries (coefD (monoCoeffA m)) (Real.sin y ^ 2) * (2 * Real.sin y * Real.cos y))
        (-4 * m ^ 2 * pseries (monoCoeffA m) (Real.sin x ^ 2)) x := fun x hx => by
    refine (((hD1 x hx).comp x (sec5d_t_derivatives_proved x).1).mul (h2sc x)).congr_deriv ?_
    have hode := pseries_ode m hb0 hb1 hb2 (hsq x hx)
    simp only [Function.comp_apply]
    linear_combination 4 * hode + (4 * Real.sin x ^ 2 * pseries (coefD (coefD (monoCoeffA m))) (Real.sin x ^ 2) +
      2 * pseries (coefD (monoCoeffA m)) (Real.sin x ^ 2)) * Real.sin_sq_add_cos_sq x
  -- G = F - cos(2m·), G1 = G'; the energy G1² + 4m²G² has derivative 0
  have hcos : ∀ x : ℝ, HasDerivAt (fun y => Real.cos (2 * m * y)) (-(2 * m) * Real.sin (2 * m * x)) x :=
    fun x => ((Real.hasDerivAt_cos (2 * m * x)).comp x ((hasDerivAt_id x).const_mul (2 * m))).congr_deriv
      (by simp only [mul_one]; ring)
  have hsin : ∀ x : ℝ, HasDerivAt (fun y => 2 * m * Real.sin (2 * m * y))
      (4 * m ^ 2 * Real.cos (2 * m * x)) x :=
    fun x => (((Real.hasDerivAt_sin (2 * m * x)).comp x ((hasDerivAt_id x).const_mul (2 * m))).const_mul
      (2 * m)).congr_deriv (by simp only [mul_one]; ring)
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ,
      G = fun y => pseries (monoCoeffA m) (Real.sin y ^ 2) - Real.cos (2 * m * y) := ⟨_, rfl⟩
  obtain ⟨G1, hG1def⟩ : ∃ G1 : ℝ → ℝ, G1 = fun y => pseries (coefD (monoCoeffA m)) (Real.sin y ^ 2) *
      (2 * Real.sin y * Real.cos y) + 2 * m * Real.sin (2 * m * y) := ⟨_, rfl⟩
  have hG : ∀ x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), HasDerivAt G (G1 x) x := fun x hx => by
    simp only [hGdef, hG1def]
    exact ((hF x hx).sub (hcos x)).congr_deriv (by ring)
  have hG1 : ∀ x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), HasDerivAt G1 (-4 * m ^ 2 * G x) x := fun x hx => by
    simp only [hG1def, hGdef]
    exact ((hF1 x hx).add (hsin x)).congr_deriv (by ring)
  have hE : ∀ x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt (fun y => G1 y ^ 2 + 4 * m ^ 2 * G y ^ 2) 0 x := fun x hx =>
    (((hG1 x hx).pow 2).add (((hG x hx).pow 2).const_mul (4 * m ^ 2))).congr_deriv (by
      simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
      ring)
  have h0U : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hS0 : pseries (monoCoeffA m) 0 = 1 := by
    rw [pseries, tsum_eq_single 0 (fun n hn => by simp [hn])]
    simp [(sec5d_coefficient_recurrence_proved m).1]
  have hG0 : G 0 = 0 := by simp [hGdef, hS0]
  have hG10 : G1 0 = 0 := by simp [hG1def]
  have hEconst : ∀ x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), G1 x ^ 2 + 4 * m ^ 2 * G x ^ 2 = 0 :=
    fun x hx => by
      have := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        (fun y hy => (hE y hy).differentiableAt.differentiableWithinAt) (fun y hy => (hE y hy).deriv) hx h0U
      simpa [hG0, hG10] using this
  have hG1zero : ∀ x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), G1 x = 0 := fun x hx => by
    have h := hEconst x hx
    have hsq0 : G1 x ^ 2 = 0 := by nlinarith [sq_nonneg (G1 x), sq_nonneg (m * G x)]
    exact (pow_eq_zero_iff two_ne_zero).mp hsq0
  have hGzero : ∀ x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2), G x = 0 := fun x hx => by
    rw [← hG0]
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun y hy => (hG y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => by simp [(hG y hy).deriv, hG1zero y hy]) hx h0U
  -- read off at α = arcsin √t
  have hsqrt1 : Real.sqrt t < 1 := (Real.sqrt_lt' one_pos).mpr (by rw [one_pow]; exact ht1)
  have hαU : Real.arcsin (Real.sqrt t) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.arcsin_nonneg.mpr (Real.sqrt_nonneg t)], Real.arcsin_lt_pi_div_two.mpr hsqrt1⟩
  have hsinα : Real.sin (Real.arcsin (Real.sqrt t)) ^ 2 = t := by
    rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg t]) hsqrt1.le, Real.sq_sqrt ht]
  have hval : pseries (monoCoeffA m) t = monoY m t := by
    have h := hGzero _ hαU
    simp only [hGdef, hsinα] at h
    unfold monoY
    linarith
  rw [← hval]
  exact hasSum_pseries hb0 (by rw [abs_of_nonneg ht]; exact ht1)

end GKSharp

