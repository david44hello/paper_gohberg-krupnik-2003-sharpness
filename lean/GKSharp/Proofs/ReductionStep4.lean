/- GKSharp/Proofs/ReductionStep4.lean - Reduction Step 4: z = -1 is not a zero of D_C (short v0.70 sec5 l.162-163).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Route (named route difference: the unit circle instead of the vertical line `-1 + iy`): on `z_s = e^{i(π - s)}`,
`s ∈ (0, 2π)`, one has `‖z_s‖ = 1`, `arg z_s = π - s`, `Re z_s^q = cos(qπ - qs)`, `q = p/2`, and
`D(z_s) = C^p (2 - 2cos s)^{p/2} - (1 - 2λ cos s + λ²)^{p/2} - K cos(qπ - qs)`. As `s → 0+`: the first term over `s`
tends to `0` (`0 ≤ 2 - 2cos s ≤ s²`, so it is `≤ s^{p-1}` times `C^p`, `p > 1`); the second has derivative `0` at
`s = 0` (`λ < 1`, base `(1 - λ)² > 0`); the third has derivative `K q sin(qπ) > 0` (`0 < q < 1`). So
`(D(z_s) - D(-1))/s → -K q sin(qπ) < 0`, and `z_s → -1` with `z_s ≠ -1`: for small `s`, `0 ≤ D(z_s) < D(-1)`.
-/
import GKSharp.Defs.RealLine

namespace GKSharp

open Set Filter
open scoped Topology

/-- `‖w‖^p = (Re² + Im²)^{p/2}`. -/
lemma sec5s_norm_rpow (w : ℂ) (p : ℝ) : ‖w‖ ^ p = (w.re ^ 2 + w.im ^ 2) ^ (p / 2) := by
  rw [show w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 by rw [Complex.sq_norm, Complex.normSq_apply]; ring,
    ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg w)]
  congr 1
  push_cast
  ring

lemma sec5s_arg_circle {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 2 * Real.pi) :
    Complex.arg (Complex.exp (((Real.pi - s : ℝ) : ℂ) * Complex.I)) = Real.pi - s := by
  rw [Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩

lemma sec5s_circle_ne {s : ℝ} (hs0 : 0 < s) (hs : s < 2 * Real.pi) :
    Complex.exp (((Real.pi - s : ℝ) : ℂ) * Complex.I) ≠ -1 := by
  intro h
  have harg := sec5s_arg_circle hs0.le hs
  rw [h, Complex.arg_neg_one] at harg
  linarith

/-- `D_C` on the unit circle near `-1`. -/
lemma sec5s_critD_circle {p C K lam s : ℝ} (hs0 : 0 ≤ s) (hs : s < 2 * Real.pi) :
    critD p C K lam (Complex.exp (((Real.pi - s : ℝ) : ℂ) * Complex.I)) =
      C ^ p * (2 - 2 * Real.cos s) ^ (p / 2) - (1 - 2 * lam * Real.cos s + lam ^ 2) ^ (p / 2) -
        K * Real.cos (p / 2 * (Real.pi - s)) := by
  have hre : (Complex.exp (((Real.pi - s : ℝ) : ℂ) * Complex.I)).re = -Real.cos s := by
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_sub]
  have him : (Complex.exp (((Real.pi - s : ℝ) : ℂ) * Complex.I)).im = Real.sin s := by
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_sub]
  have e1 : ‖1 + Complex.exp (((Real.pi - s : ℝ) : ℂ) * Complex.I)‖ ^ p = (2 - 2 * Real.cos s) ^ (p / 2) := by
    rw [sec5s_norm_rpow]
    congr 1
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, hre, him]
    linear_combination Real.sin_sq_add_cos_sq s
  have e2 : ‖1 + (lam : ℂ) * Complex.exp (((Real.pi - s : ℝ) : ℂ) * Complex.I)‖ ^ p =
      (1 - 2 * lam * Real.cos s + lam ^ 2) ^ (p / 2) := by
    rw [sec5s_norm_rpow]
    congr 1
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul, hre, him]
    linear_combination lam ^ 2 * Real.sin_sq_add_cos_sq s
  have e3 : reQPow (Complex.exp (((Real.pi - s : ℝ) : ℂ) * Complex.I)) (p / 2) =
      Real.cos (p / 2 * (Real.pi - s)) := by
    unfold reQPow
    rw [Complex.norm_exp_ofReal_mul_I, Real.one_rpow, one_mul, sec5s_arg_circle hs0 hs]
  unfold critD
  rw [e1, e2, e3]

/-- `s⁻¹ (2 - 2cos s)^{p/2} → 0` as `s → 0+`, for `p > 1`. -/
lemma sec5s_A_slope {p : ℝ} (hp : 1 < p) :
    Tendsto (fun s : ℝ => s⁻¹ * (2 - 2 * Real.cos s) ^ (p / 2)) (𝓝[>] 0) (𝓝 0) := by
  have hcont : Tendsto (fun s : ℝ => s ^ (p - 1)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (p - 1) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith : p - 1 ≠ 0)] at this
    exact this.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcont
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : (0 : ℝ) < s := hs
    exact mul_nonneg (inv_nonneg.2 hs0.le) (Real.rpow_nonneg (by linarith [Real.cos_le_one s]) _)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : (0 : ℝ) < s := hs
    have hle : 2 - 2 * Real.cos s ≤ s ^ 2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := s)]
    have h1 : (2 - 2 * Real.cos s) ^ (p / 2) ≤ (s ^ 2) ^ (p / 2) :=
      Real.rpow_le_rpow (by linarith [Real.cos_le_one s]) hle (by linarith)
    have h2 : (s ^ 2) ^ (p / 2) = s ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
      congr 1
      push_cast
      ring
    have h3 : s⁻¹ * s ^ p = s ^ (p - 1) := by rw [Real.rpow_sub_one hs0.ne', inv_mul_eq_div]
    calc s⁻¹ * (2 - 2 * Real.cos s) ^ (p / 2) ≤ s⁻¹ * s ^ p := by
          rw [← h2]
          exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hs0.le)
      _ = s ^ (p - 1) := h3

lemma sec5s_B_deriv {p lam : ℝ} (hl1 : lam < 1) :
    HasDerivAt (fun s : ℝ => (1 - 2 * lam * Real.cos s + lam ^ 2) ^ (p / 2)) 0 0 := by
  have hf : HasDerivAt (fun s : ℝ => 1 - 2 * lam * Real.cos s + lam ^ 2) (-(2 * lam * -Real.sin 0)) 0 :=
    (((Real.hasDerivAt_cos 0).const_mul (2 * lam)).const_sub 1).add_const (lam ^ 2)
  have h0 : 1 - 2 * lam * Real.cos 0 + lam ^ 2 ≠ 0 := by
    rw [Real.cos_zero, show 1 - 2 * lam * 1 + lam ^ 2 = (1 - lam) ^ 2 by ring]
    exact pow_ne_zero 2 (sub_pos.2 hl1).ne'
  convert hf.rpow_const (p := p / 2) (Or.inl h0) using 1
  simp [Real.sin_zero]

lemma sec5s_E_deriv (p K : ℝ) :
    HasDerivAt (fun s : ℝ => K * Real.cos (p / 2 * (Real.pi - s))) (K * (p / 2) * Real.sin (p / 2 * Real.pi)) 0 := by
  have hin : HasDerivAt (fun s : ℝ => p / 2 * (Real.pi - s)) (p / 2 * (-1)) 0 :=
    ((hasDerivAt_id' 0).const_sub Real.pi).const_mul (p / 2)
  convert hin.cos.const_mul K using 1
  rw [sub_zero]
  ring

lemma sec5s_mul_slope {s c a b e : ℝ} (hs : 0 < s) (h : c * (s⁻¹ * a) - s⁻¹ * b - s⁻¹ * e < 0) :
    c * a - b - e < 0 := by
  have key : s * (c * (s⁻¹ * a) - s⁻¹ * b - s⁻¹ * e) = c * a - b - e := by
    linear_combination (c * a - b - e) * mul_inv_cancel₀ hs.ne'
  have := mul_neg_of_pos_of_neg hs h
  rwa [key] at this

/-- Reduction Step 4 (sec5_sharp_inequality.tex l.162-163): `D_C(-1) > 0`. -/
theorem reduction_step4 {p C K lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl1 : lam < 1) (hK : 0 < K)
    (hnn : ∀ᶠ z in 𝓝[≠] (-1 : ℂ), 0 ≤ critD p C K lam z) : 0 < critD p C K lam (-1) := by
  have hp0 : 0 < p := by linarith
  have hpi := Real.pi_pos
  -- the path `s ↦ e^{i(π - s)}` tends to `-1` inside the punctured neighbourhood
  have hzt : Tendsto (fun s : ℝ => Complex.exp (((Real.pi - s : ℝ) : ℂ) * Complex.I)) (𝓝[>] 0)
      (𝓝[≠] (-1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun s : ℝ => Complex.exp (((Real.pi - s : ℝ) : ℂ) * Complex.I)) := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simp only [sub_zero, Complex.exp_pi_mul_I] at this
      exact this
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * Real.pi by linarith)] with s hs
      exact sec5s_circle_ne hs.1 hs.2
  have hnn' := hzt.eventually hnn
  -- the slope of `D` along the path
  have hBs := (sec5s_B_deriv (p := p) hl1).tendsto_slope_zero_right
  have hEs := (sec5s_E_deriv p K).tendsto_slope_zero_right
  simp only [zero_add, smul_eq_mul] at hBs hEs
  have hT := (((sec5s_A_slope hp1).const_mul (C ^ p)).sub hBs).sub hEs
  have hsin : 0 < Real.sin (p / 2 * Real.pi) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos (half_pos hp0) hpi) (by nlinarith)
  have hlim : C ^ p * 0 - 0 - K * (p / 2) * Real.sin (p / 2 * Real.pi) < 0 := by
    have := mul_pos (mul_pos hK (half_pos hp0)) hsin
    linarith
  have hI : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 Real.pi := Ioo_mem_nhdsGT hpi
  obtain ⟨s, hs, hsI, h0⟩ := ((hT.eventually (gt_mem_nhds hlim)).and (hI.and hnn')).exists
  have hs' : C ^ p * (s⁻¹ * (2 - 2 * Real.cos s) ^ (p / 2)) -
      s⁻¹ * ((1 - 2 * lam * Real.cos s + lam ^ 2) ^ (p / 2) - (1 - 2 * lam * Real.cos 0 + lam ^ 2) ^ (p / 2)) -
      s⁻¹ * (K * Real.cos (p / 2 * (Real.pi - s)) - K * Real.cos (p / 2 * (Real.pi - 0))) < 0 := hs
  have hX := sec5s_mul_slope hsI.1 hs'
  rw [sec5s_critD_circle hsI.1.le (by linarith [hsI.2])] at h0
  have hm1 := sec5s_critD_circle (p := p) (C := C) (K := K) (lam := lam) (s := 0) le_rfl (by linarith)
  rw [show Complex.exp (((Real.pi - 0 : ℝ) : ℂ) * Complex.I) = -1 by
    rw [sub_zero]; exact Complex.exp_pi_mul_I] at hm1
  have ha0 : (2 - 2 * Real.cos 0) ^ (p / 2) = (0 : ℝ) := by
    rw [Real.cos_zero, show (2 : ℝ) - 2 * 1 = 0 by norm_num, Real.zero_rpow (half_pos hp0).ne']
  rw [ha0, mul_zero] at hm1
  linarith

end GKSharp

