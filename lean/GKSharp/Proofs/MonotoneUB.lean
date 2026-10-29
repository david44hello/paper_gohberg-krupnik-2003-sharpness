/- Lemma U series inputs, frozen sec5d_monotone.tex:89-99 (rows sec5d_Y_coordinate,
sec5d_Y_series_convergence; types verbatim from the proposal v020).
Convergence: |a_(n+1)| ≤ |a_n| once n ≥ m², so the ratio test applies with ratio |t| < 1.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.MonotonicityCurve
import GKSharp.Proofs.MonotoneUA

namespace GKSharp

open Filter Topology

/-- Row `sec5d_Y_coordinate`. -/
theorem sec5d_Y_coordinate_proved (m : ℝ) {α : ℝ} (hα : 0 < α) (hαπ : α < Real.pi / 2) :
    monoY m (Real.sin α ^ 2) = Real.cos (2 * m * α) := by
  have hpi := Real.pi_pos
  unfold monoY
  rw [Real.sqrt_sq (Real.sin_pos_of_pos_of_lt_pi hα (by linarith)).le,
    Real.arcsin_sin (by linarith) hαπ.le]

/-- Row `sec5d_Y_ode`. Route: g = arcsin √t has sin g = √t, cos g = √(1-t), g' = 1/sin 2g; then
Y' = -2m sin(2mg)/sin 2g, Y'' by the quotient rule, and t(1-t) = sin² 2g/4, 1/2 - t = cos 2g/2. -/
theorem sec5d_Y_ode_proved (m : ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    t * (1 - t) * deriv (deriv (monoY m)) t + (1 / 2 - t) * deriv (monoY m) t +
      m ^ 2 * monoY m t = 0 := by
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ, g = fun s => Real.arcsin (Real.sqrt s) := ⟨_, rfl⟩
  have hYg : monoY m = fun s => Real.cos (2 * m * g s) := by
    funext s
    rw [hgdef]
    rfl
  have hsq1 : ∀ s ∈ Set.Ioo (0 : ℝ) 1, Real.sqrt s < 1 := fun s hs =>
    (Real.sqrt_lt' one_pos).mpr (by rw [one_pow]; exact hs.2)
  have hsin : ∀ s ∈ Set.Ioo (0 : ℝ) 1, Real.sin (g s) = Real.sqrt s := fun s hs => by
    simp only [hgdef]
    exact Real.sin_arcsin (by linarith [Real.sqrt_nonneg s]) (hsq1 s hs).le
  have hcos : ∀ s ∈ Set.Ioo (0 : ℝ) 1, Real.cos (g s) = Real.sqrt (1 - s) := fun s hs => by
    simp only [hgdef]
    rw [Real.cos_arcsin, Real.sq_sqrt hs.1.le]
  have hD : ∀ s ∈ Set.Ioo (0 : ℝ) 1, Real.sin (2 * g s) = 2 * Real.sqrt s * Real.sqrt (1 - s) :=
    fun s hs => by rw [Real.sin_two_mul, hsin s hs, hcos s hs, mul_assoc]
  have hDpos : ∀ s ∈ Set.Ioo (0 : ℝ) 1, 0 < Real.sin (2 * g s) := fun s hs => by
    rw [hD s hs]
    exact mul_pos (mul_pos two_pos (Real.sqrt_pos.mpr hs.1)) (Real.sqrt_pos.mpr (by linarith [hs.2]))
  have hg' : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (1 / Real.sin (2 * g s)) s := fun s hs => by
    have h := (Real.hasDerivAt_arcsin (ne_of_gt (show Real.sqrt s > -1 by linarith [Real.sqrt_nonneg s]))
      (hsq1 s hs).ne).comp s (Real.hasDerivAt_sqrt hs.1.ne')
    rw [hD s hs, hgdef]
    refine h.congr_deriv ?_
    rw [Real.sq_sqrt hs.1.le]
    ring
  have hY : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun s => Real.cos (2 * m * g s))
      (-(2 * m) * Real.sin (2 * m * g s) / Real.sin (2 * g s)) s := fun s hs => by
    refine ((Real.hasDerivAt_cos (2 * m * g s)).comp s ((hg' s hs).const_mul (2 * m))).congr_deriv ?_
    ring
  have htI : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht, ht1⟩
  have hYeq : deriv (fun s => Real.cos (2 * m * g s)) =ᶠ[𝓝 t]
      fun s => -(2 * m) * Real.sin (2 * m * g s) / Real.sin (2 * g s) := by
    filter_upwards [Ioo_mem_nhds ht ht1] with s hs
    exact (hY s hs).deriv
  have hN : HasDerivAt (fun s => -(2 * m) * Real.sin (2 * m * g s))
      (-(2 * m) * (Real.cos (2 * m * g t) * (2 * m * (1 / Real.sin (2 * g t))))) t :=
    ((Real.hasDerivAt_sin (2 * m * g t)).comp t ((hg' t htI).const_mul (2 * m))).const_mul (-(2 * m))
  have hDd' := (Real.hasDerivAt_sin (2 * g t)).comp t ((hg' t htI).const_mul 2)
  have hDd : HasDerivAt (fun s => Real.sin (2 * g s))
      (Real.cos (2 * g t) * (2 * (1 / Real.sin (2 * g t)))) t := hDd'
  have h2' := hN.div hDd (hDpos t htI).ne'
  have h2 : HasDerivAt (fun s => -(2 * m) * Real.sin (2 * m * g s) / Real.sin (2 * g s)) _ t := h2'
  have e1 : t * (1 - t) = Real.sin (2 * g t) ^ 2 / 4 := by
    rw [hD t htI, mul_pow, mul_pow, Real.sq_sqrt ht.le, Real.sq_sqrt (by linarith)]
    ring
  have e2 : 1 / 2 - t = Real.cos (2 * g t) / 2 := by
    rw [Real.cos_two_mul, hcos t htI, Real.sq_sqrt (by linarith)]
    ring
  have hne := (hDpos t htI).ne'
  simp only [hYg]
  rw [hYeq.deriv_eq, h2.deriv, (hY t htI).deriv, e1, e2]
  field_simp
  ring

/-- Eventually the recurrence ratio has absolute value at most one. -/
theorem monoCoeffA_abs_succ_le (m : ℝ) {n : ℕ} (hn : ⌈m ^ 2⌉₊ ≤ n) :
    |monoCoeffA m (n + 1)| ≤ |monoCoeffA m n| := by
  have hmn : m ^ 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : 0 < ((n : ℝ) + 1) * ((n : ℝ) + 1 / 2) := by positivity
  have hratio : |((n : ℝ) ^ 2 - m ^ 2) / (((n : ℝ) + 1) * ((n : ℝ) + 1 / 2))| ≤ 1 := by
    rw [abs_div, abs_of_pos hden, div_le_one hden, abs_le]
    constructor <;> nlinarith [sq_nonneg m]
  rw [(sec5d_coefficient_recurrence_proved m).2 n, abs_mul]
  calc _ ≤ 1 * |monoCoeffA m n| := by gcongr
    _ = |monoCoeffA m n| := one_mul _

/-- Row `sec5d_Y_series_convergence`. -/
theorem sec5d_Y_series_convergence_proved (m : ℝ) {t : ℝ} (ht : |t| < 1) :
    Summable (fun n : ℕ => |monoCoeffA m n| * |t| ^ n) := by
  refine summable_of_ratio_norm_eventually_le ht ?_
  filter_upwards [eventually_ge_atTop ⌈m ^ 2⌉₊] with n hn
  simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_pow]
  rw [pow_succ]
  calc |monoCoeffA m (n + 1)| * (|t| ^ n * |t|) ≤ |monoCoeffA m n| * (|t| ^ n * |t|) :=
        mul_le_mul_of_nonneg_right (monoCoeffA_abs_succ_le m hn) (by positivity)
    _ = |t| * (|monoCoeffA m n| * |t| ^ n) := by ring

end GKSharp

