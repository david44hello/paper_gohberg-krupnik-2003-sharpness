/- GKSharp/Proofs/Sec4aAngular.lean - slice (b): the wrapped cosine is q-trigonometrically convex (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v0.90, each as `<row>_proved` with the row's exact type.
- wrapped_cosine_trigconvex (A:22-23): `cos(q arg e^{it}) = cos(q arccos(cos t))` (even in `arg`), so `f` is continuous
  and `2π`-periodic. For `F(x) = f(x/q)` put `δ(x) = q arccos(cos(x/q))`, the distance from `x` to the lattice
  `L = 2πq ℤ` (`arccos(cos u) ≤ |u - 2πk|` for all `k`, with equality for `k = round(u/2π)`). For `c ∈ L`:
  `cos(x - c) ≤ cos δ(x)` once `|x - c| ≤ π + πq` (for `|x - c| > π` use the neighbour `c ± 2πq`, at distance
  `||x - c| - 2πq| ≤ 2π - |x - c|`). Given `x < t < y`, `y - x < π`, take `c ∈ L` nearest to `t`: `F(t) = K cos(t - c)`,
  `|x - c|, |y - c| < π + πq`, and `cos(t - c) sin(y - x) = cos(x - c) sin(y - t) + cos(y - c) sin(t - x)`.
-/
import GKSharp.Defs.ThresholdAnalysis

namespace GKSharp

open Set GKSharp.Threshold

/-- `cos(q arg e^{it}) = cos(q arccos(cos t))`: `cos(q θ)` is even in `θ = arg e^{it}`, and `|θ| = arccos(cos t)`. -/
lemma sec4a_cos_arg_exp (qq t : ℝ) :
    Real.cos (qq * Complex.arg (Complex.exp (Complex.I * (t : ℂ)))) =
      Real.cos (qq * Real.arccos (Real.cos t)) := by
  obtain ⟨w, hw⟩ : ∃ w, w = Complex.exp (Complex.I * (t : ℂ)) := ⟨_, rfl⟩
  rw [← hw]
  have hw0 : w ≠ 0 := by rw [hw]; exact Complex.exp_ne_zero _
  have hc : Real.cos (Complex.arg w) = Real.cos t := by
    rw [Complex.cos_arg hw0, hw, mul_comm Complex.I (t : ℂ), Complex.norm_exp_ofReal_mul_I,
      Complex.exp_ofReal_mul_I_re, div_one]
  rw [← hc]
  rcases le_total 0 (Complex.arg w) with h | h
  · rw [Real.arccos_cos h (Complex.arg_le_pi w)]
  · rw [← Real.cos_neg (Complex.arg w),
      Real.arccos_cos (neg_nonneg.2 h) (by linarith [Complex.neg_pi_lt_arg w]), mul_neg, Real.cos_neg]

/-- `arccos(cos u) ≤ |u - 2πk|` for every integer `k`. -/
lemma sec4a_arccos_cos_le (u : ℝ) (k : ℤ) : Real.arccos (Real.cos u) ≤ |u - k * (2 * Real.pi)| := by
  rw [← Real.cos_sub_int_mul_two_pi u k]
  rcases le_or_gt |u - k * (2 * Real.pi)| Real.pi with h | h
  · rw [← Real.cos_abs, Real.arccos_cos (abs_nonneg _) h]
  · exact (Real.arccos_le_pi _).trans h.le

/-- The bound is attained: `arccos(cos u) = |u - 2πk|` for `k = round(u/2π)`. -/
lemma sec4a_arccos_cos_eq (u : ℝ) : ∃ k : ℤ, Real.arccos (Real.cos u) = |u - k * (2 * Real.pi)| := by
  refine ⟨round (u / (2 * Real.pi)), ?_⟩
  have hpi := Real.pi_pos
  have hr := abs_sub_round (u / (2 * Real.pi))
  have hle : |u - (round (u / (2 * Real.pi)) : ℝ) * (2 * Real.pi)| ≤ Real.pi := by
    have he : u - (round (u / (2 * Real.pi)) : ℝ) * (2 * Real.pi) =
        (u / (2 * Real.pi) - round (u / (2 * Real.pi))) * (2 * Real.pi) := by
      rw [sub_mul, div_mul_cancel₀ u (by positivity : (2 * Real.pi) ≠ 0)]
    rw [he, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have := mul_le_mul_of_nonneg_right hr (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    linarith
  rw [← Real.cos_sub_int_mul_two_pi u (round (u / (2 * Real.pi))), ← Real.cos_abs,
    Real.arccos_cos (abs_nonneg _) hle]

/-- Lattice comparison: for `c = 2πq k` and `|x - c| ≤ π + πq`, `cos(x - c) ≤ cos(q arccos(cos(x/q)))`. -/
lemma sec4a_wrapped_ge {qq : ℝ} (hq0 : 0 < qq) (hq1 : qq < 1) (x : ℝ) (k : ℤ)
    (hx : |x - k * (2 * Real.pi * qq)| ≤ Real.pi + Real.pi * qq) :
    Real.cos (x - k * (2 * Real.pi * qq)) ≤ Real.cos (qq * Real.arccos (Real.cos (x / qq))) := by
  have hpi := Real.pi_pos
  have hqne : qq ≠ 0 := hq0.ne'
  obtain ⟨δ, hδ⟩ : ∃ d, d = qq * Real.arccos (Real.cos (x / qq)) := ⟨_, rfl⟩
  rw [← hδ]
  have hδ0 : 0 ≤ δ := by rw [hδ]; exact mul_nonneg hq0.le (Real.arccos_nonneg _)
  -- `δ ≤ |x - 2πq j|` for every integer `j`
  have hlat : ∀ j : ℤ, δ ≤ |x - j * (2 * Real.pi * qq)| := by
    intro j
    have h1 := sec4a_arccos_cos_le (x / qq) j
    have he : x - j * (2 * Real.pi * qq) = qq * (x / qq - j * (2 * Real.pi)) := by field_simp
    rw [he, abs_mul, abs_of_pos hq0, hδ]
    exact mul_le_mul_of_nonneg_left h1 hq0.le
  obtain ⟨w, hw⟩ : ∃ w, w = x - k * (2 * Real.pi * qq) := ⟨_, rfl⟩
  have hlk := hlat k
  rw [← hw] at hx hlk ⊢
  rw [← Real.cos_abs w]
  rcases le_or_gt |w| Real.pi with hw1 | hw1
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hδ0 hw1 hlk
  · -- `π < |w| ≤ π + πq`: the neighbour `c ± 2πq` is at distance `||w| - 2πq| ≤ 2π - |w|`
    have hb : δ ≤ |(|w| - 2 * Real.pi * qq)| := by
      rcases le_or_gt 0 w with hw0 | hw0
      · have h := hlat (k + 1)
        rw [show x - ((k + 1 : ℤ) : ℝ) * (2 * Real.pi * qq) = w - 2 * Real.pi * qq by
          rw [hw]; push_cast; ring] at h
        rwa [abs_of_nonneg hw0]
      · have h := hlat (k - 1)
        rw [show x - ((k - 1 : ℤ) : ℝ) * (2 * Real.pi * qq) = -(-w - 2 * Real.pi * qq) by
          rw [hw]; push_cast; ring, abs_neg] at h
        rwa [abs_of_neg hw0]
    have hpq := mul_le_mul_of_nonneg_left hq1.le hpi.le
    have hb2 : |(|w| - 2 * Real.pi * qq)| ≤ 2 * Real.pi - |w| := by
      rw [abs_le]
      constructor <;> linarith
    rw [← Real.cos_two_pi_sub |w|]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hδ0 (by linarith) (hb.trans hb2)

/-- A:22-23, row `wrapped_cosine_trigconvex`. -/
theorem wrapped_cosine_trigconvex_proved (qq KK : ℝ) (hq : qq ∈ Ioo (0 : ℝ) 1) (hK : 0 ≤ KK) :
    let f := fun t : ℝ => KK * Real.cos (qq * Complex.arg (Complex.exp (Complex.I * (t : ℂ))))
    Continuous f ∧ Function.Periodic f (2 * Real.pi) ∧ QTrigConvex qq f := by
  obtain ⟨hq0, hq1⟩ := hq
  intro f
  have hf : f = fun t : ℝ => KK * Real.cos (qq * Real.arccos (Real.cos t)) := by
    funext t
    show KK * Real.cos (qq * Complex.arg (Complex.exp (Complex.I * (t : ℂ)))) = _
    rw [sec4a_cos_arg_exp]
  rw [hf]
  refine ⟨continuous_const.mul (Real.continuous_cos.comp
      (continuous_const.mul (Real.continuous_arccos.comp Real.continuous_cos))),
    fun t => by simp [Real.cos_add_two_pi], ?_⟩
  intro x _ y _ t _ hxt hty hyx
  show KK * Real.cos (qq * Real.arccos (Real.cos (t / qq))) ≤
    (KK * Real.cos (qq * Real.arccos (Real.cos (x / qq))) * Real.sin (y - t) +
      KK * Real.cos (qq * Real.arccos (Real.cos (y / qq))) * Real.sin (t - x)) / Real.sin (y - x)
  have hpi := Real.pi_pos
  have hqne : qq ≠ 0 := hq0.ne'
  -- the lattice point `c = 2πq k` nearest to `t`
  obtain ⟨k, hk⟩ := sec4a_arccos_cos_eq (t / qq)
  have htc : qq * Real.arccos (Real.cos (t / qq)) = |t - k * (2 * Real.pi * qq)| := by
    have he : t - k * (2 * Real.pi * qq) = qq * (t / qq - k * (2 * Real.pi)) := by field_simp
    rw [hk, he, abs_mul, abs_of_pos hq0]
  have htc1 : |t - k * (2 * Real.pi * qq)| ≤ Real.pi * qq := by
    rw [← htc]
    have := mul_le_mul_of_nonneg_left (Real.arccos_le_pi (Real.cos (t / qq))) hq0.le
    linarith
  have hFt : Real.cos (qq * Real.arccos (Real.cos (t / qq))) = Real.cos (t - k * (2 * Real.pi * qq)) := by
    rw [htc, Real.cos_abs]
  have hxc : |x - k * (2 * Real.pi * qq)| ≤ Real.pi + Real.pi * qq := by
    have := abs_sub_le x t (k * (2 * Real.pi * qq))
    rw [abs_of_neg (by linarith : x - t < 0)] at this
    linarith
  have hyc : |y - k * (2 * Real.pi * qq)| ≤ Real.pi + Real.pi * qq := by
    have := abs_sub_le y t (k * (2 * Real.pi * qq))
    rw [abs_of_pos (by linarith : 0 < y - t)] at this
    linarith
  have hX := sec4a_wrapped_ge hq0 hq1 x k hxc
  have hY := sec4a_wrapped_ge hq0 hq1 y k hyc
  have hs := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < y - x) hyx
  have hs1 := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < y - t) (by linarith)
  have hs2 := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < t - x) (by linarith)
  -- a sinusoid meets its own chord identity
  have key : ∀ A B T : ℝ, Real.cos T * Real.sin (B - A) =
      Real.cos A * Real.sin (B - T) + Real.cos B * Real.sin (T - A) := by
    intro A B T
    simp only [Real.sin_sub]
    ring
  have hid := key (x - k * (2 * Real.pi * qq)) (y - k * (2 * Real.pi * qq)) (t - k * (2 * Real.pi * qq))
  rw [show y - k * (2 * Real.pi * qq) - (x - k * (2 * Real.pi * qq)) = y - x by ring,
    show y - k * (2 * Real.pi * qq) - (t - k * (2 * Real.pi * qq)) = y - t by ring,
    show t - k * (2 * Real.pi * qq) - (x - k * (2 * Real.pi * qq)) = t - x by ring] at hid
  have hsum : Real.cos (t - k * (2 * Real.pi * qq)) * Real.sin (y - x) ≤
      Real.cos (qq * Real.arccos (Real.cos (x / qq))) * Real.sin (y - t) +
        Real.cos (qq * Real.arccos (Real.cos (y / qq))) * Real.sin (t - x) := by
    rw [hid]
    linarith [mul_le_mul_of_nonneg_right hX hs1.le, mul_le_mul_of_nonneg_right hY hs2.le]
  rw [le_div_iff₀ hs, hFt]
  have := mul_le_mul_of_nonneg_left hsum hK
  linarith

end GKSharp
