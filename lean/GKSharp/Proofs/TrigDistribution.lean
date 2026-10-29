/- trigonometric q-convexity versus the weak inequality φ'' + q²φ ≥ 0 (sec2_obstacle.tex l.58-60).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.TrigContGK
import GKSharp.Proofs.ChordTent
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

open Real Set Filter Topology MeasureTheory
open scoped ContDiff

namespace GKSharp.Proofs.TrigDistribution

/-- Centered sum rule: `sin (a - b) + sin (a + b) = 2 cos b sin a`. -/
theorem sin_sub_add_sin_add (a b : ℝ) : sin (a - b) + sin (a + b) = 2 * cos b * sin a := by
  rw [sin_sub, sin_add]; ring

/-- Continuity plus the centered chord inequality on all chords shorter than `L` gives trigonometric `q`-convexity
on every chord with `q (y - x) < π`. Maximum principle: divide `φ - chord` by a positive sinusoid; at the leftmost
point of a positive maximum, a centered chord forces the maximum one step further left. -/
theorem trigConvex_of_centered {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (hc : Continuous φ) {L : ℝ} (hL : 0 < L)
    (hloc : ∀ t d : ℝ, 0 < d → d < L → 2 * cos (q * d) * φ t ≤ φ (t - d) + φ (t + d)) : TrigConvex q φ := by
  intro x t y hxt hty hlen
  have hs : 0 < sin (q * (y - x)) := sin_pos_of_pos_of_lt_pi (mul_pos hq (by linarith)) hlen
  obtain ⟨chord, hchord⟩ : ∃ S : ℝ → ℝ, ∀ u,
      S u = (φ x * sin (q * (y - u)) + φ y * sin (q * (u - x))) / sin (q * (y - x)) := ⟨_, fun _ => rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (π - q * (y - x)) / 2 := ⟨_, rfl⟩
  obtain ⟨weight, hweight⟩ : ∃ w : ℝ → ℝ, ∀ u, w u = sin (q * (u - x) + δ) := ⟨_, fun _ => rfl⟩
  obtain ⟨ratio, hratio⟩ : ∃ r : ℝ → ℝ, ∀ u, r u = (φ u - chord u) / weight u := ⟨_, fun _ => rfl⟩
  have hw : ∀ u ∈ Icc x y, 0 < weight u := by
    intro u hu
    have h1 : 0 ≤ q * (u - x) := mul_nonneg hq.le (by linarith [hu.1])
    have h2 : q * (u - x) ≤ q * (y - x) := mul_le_mul_of_nonneg_left (by linarith [hu.2]) hq.le
    rw [hweight u]
    exact sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hchord_c : Continuous chord := (continuous_congr hchord).mpr (by fun_prop)
  have hweight_c : Continuous weight := (continuous_congr hweight).mpr (by fun_prop)
  have hratio_c : ContinuousOn ratio (Icc x y) :=
    ((hc.sub hchord_c).continuousOn.div hweight_c.continuousOn (fun u hu => (hw u hu).ne')).congr
      (fun u _ => hratio u)
  have hratio_x : ratio x = 0 := by
    have hcx : chord x = φ x := by
      rw [hchord]
      simp only [sub_self, mul_zero, sin_zero, add_zero]
      exact mul_div_cancel_right₀ (φ x) hs.ne'
    rw [hratio, hcx, sub_self, zero_div]
  have hratio_y : ratio y = 0 := by
    have hcy : chord y = φ y := by
      rw [hchord]
      simp only [sub_self, mul_zero, sin_zero, zero_add]
      exact mul_div_cancel_right₀ (φ y) hs.ne'
    rw [hratio, hcy, sub_self, zero_div]
  have hchord_cen : ∀ u d : ℝ, chord (u - d) + chord (u + d) = 2 * cos (q * d) * chord u := by
    intro u d
    rw [hchord, hchord, hchord]
    have e1 : q * (y - (u - d)) = q * (y - u) + q * d := by ring
    have e2 : q * (y - (u + d)) = q * (y - u) - q * d := by ring
    have e3 : q * (u - d - x) = q * (u - x) - q * d := by ring
    have e4 : q * (u + d - x) = q * (u - x) + q * d := by ring
    rw [e1, e2, e3, e4]
    simp only [sin_add, sin_sub]
    ring
  have hweight_cen : ∀ u d : ℝ, weight (u - d) + weight (u + d) = 2 * cos (q * d) * weight u := by
    intro u d
    rw [hweight, hweight, hweight]
    have e1 : q * (u - d - x) + δ = (q * (u - x) + δ) - q * d := by ring
    have e2 : q * (u + d - x) + δ = (q * (u - x) + δ) + q * d := by ring
    rw [e1, e2]
    exact sin_sub_add_sin_add _ _
  have hle : φ t ≤ chord t := by
    by_contra hcon
    push_neg at hcon
    have htI : t ∈ Icc x y := ⟨hxt.le, hty.le⟩
    have hrt : 0 < ratio t := by rw [hratio]; exact div_pos (by linarith) (hw t htI)
    obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨t, htI⟩ hratio_c
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ratio t0 := ⟨_, rfl⟩
    have hbound : ∀ u ∈ Icc x y, ratio u ≤ m := fun u hu => hm ▸ isMaxOn_iff.mp hmax u hu
    have hm0 : 0 < m := lt_of_lt_of_le hrt (hbound t htI)
    have hA : IsClosed (Icc x y ∩ ratio ⁻¹' {m}) :=
      hratio_c.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    obtain ⟨t1, ⟨ht1I, ht1m⟩, hleast⟩ :=
      (isCompact_Icc.of_isClosed_subset hA inter_subset_left).exists_isLeast ⟨t0, ht0, hm.symm⟩
    have hr1 : ratio t1 = m := ht1m
    have hx1 : x < t1 := by
      refine lt_of_le_of_ne ht1I.1 (fun he => ?_)
      rw [← he, hratio_x] at hr1
      linarith
    have h1y : t1 < y := by
      refine lt_of_le_of_ne ht1I.2 (fun he => ?_)
      rw [he, hratio_y] at hr1
      linarith
    obtain ⟨d, hd⟩ : ∃ d : ℝ, d = min (L / 2) (min (t1 - x) (y - t1)) := ⟨_, rfl⟩
    have hd0 : 0 < d := by rw [hd]; exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hdL : d < L := by rw [hd]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hd1 : d ≤ t1 - x := by rw [hd]; exact (min_le_right _ _).trans (min_le_left _ _)
    have hd2 : d ≤ y - t1 := by rw [hd]; exact (min_le_right _ _).trans (min_le_right _ _)
    have hG : ∀ u ∈ Icc x y, φ u - chord u - m * weight u ≤ 0 := by
      intro u hu
      have hb := hbound u hu
      rw [hratio, div_le_iff₀ (hw u hu)] at hb
      linarith
    have hG1 : φ t1 - chord t1 - m * weight t1 = 0 := by
      have hb := hr1
      rw [hratio, div_eq_iff (hw t1 ht1I).ne'] at hb
      linarith
    have hmem1 : t1 - d ∈ Icc x y := ⟨by linarith, by linarith⟩
    have hmem2 : t1 + d ∈ Icc x y := ⟨by linarith, by linarith⟩
    have hcen := hloc t1 d hd0 hdL
    have hsum : (φ (t1 - d) - chord (t1 - d) - m * weight (t1 - d)) +
        (φ (t1 + d) - chord (t1 + d) - m * weight (t1 + d)) =
        (φ (t1 - d) + φ (t1 + d) - 2 * cos (q * d) * φ t1) +
          2 * cos (q * d) * (φ t1 - chord t1 - m * weight t1) := by
      linear_combination -(hchord_cen t1 d) - m * hweight_cen t1 d
    have hGa := hG _ hmem1
    have hGb := hG _ hmem2
    rw [hG1, mul_zero, add_zero] at hsum
    have hzero : φ (t1 - d) - chord (t1 - d) - m * weight (t1 - d) = 0 := by linarith
    have hrd : ratio (t1 - d) = m := by
      rw [hratio, div_eq_iff (hw _ hmem1).ne']
      linarith
    have := hleast ⟨hmem1, hrd⟩
    linarith
  rw [hchord, le_div_iff₀ hs] at hle
  exact hle

/-! ### Trigonometric convexity gives the weak inequality -/

/-- The centered chord inequality from trigonometric convexity (`2 q d < π`). -/
theorem centered_of_trigConvex {q : ℝ} {φ : ℝ → ℝ} (htc : TrigConvex q φ) {t d : ℝ} (hq : 0 < q) (hd : 0 < d)
    (hqd : q * d < π / 2) : 2 * cos (q * d) * φ t ≤ φ (t - d) + φ (t + d) := by
  have h := htc (t - d) t (t + d) (by linarith) (by linarith) (by nlinarith)
  have e1 : q * (t + d - (t - d)) = 2 * (q * d) := by ring
  have e2 : q * (t + d - t) = q * d := by ring
  have e3 : q * (t - (t - d)) = q * d := by ring
  rw [e1, e2, e3, sin_two_mul] at h
  have hs : 0 < sin (q * d) := sin_pos_of_pos_of_lt_pi (mul_pos hq hd) (by linarith [pi_pos])
  have key : (2 * cos (q * d) * φ t) * sin (q * d) ≤ (φ (t - d) + φ (t + d)) * sin (q * d) := by linarith
  exact le_of_mul_le_mul_right key hs

/-- Shifted derivative of `h ↦ F (t + h)`. -/
theorem hasDerivAt_shift_add {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x) (t h : ℝ) :
    HasDerivAt (fun h => F (t + h)) (F' (t + h)) h := by
  have := (hF (t + h)).comp h ((hasDerivAt_id' h).const_add t)
  rw [mul_one] at this
  exact this

/-- Shifted derivative of `h ↦ F (t - h)`. -/
theorem hasDerivAt_shift_sub {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x) (t h : ℝ) :
    HasDerivAt (fun h => F (t - h)) (-F' (t - h)) h := by
  have := (hF (t - h)).comp h ((hasDerivAt_id' h).const_sub t)
  rw [mul_neg, mul_one] at this
  exact this

/-- The centered second difference, corrected by `cos (q h)`, tends to `η'' + q² η` (L'Hôpital twice). -/
theorem second_diff_tendsto {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (q t : ℝ) :
    Tendsto (fun h => (η (t + h) + η (t - h) - 2 * cos (q * h) * η t) / h ^ 2) (𝓝[>] 0)
      (𝓝 (deriv (deriv η) t + q ^ 2 * η t)) := by
  have hη' : ContDiff ℝ ∞ (deriv η) := (contDiff_infty_iff_deriv.mp hη).2
  have hd1 : ∀ x, HasDerivAt η (deriv η x) x := fun x => ((hη.differentiable (by simp)) x).hasDerivAt
  have hd2 : ∀ x, HasDerivAt (deriv η) (deriv (deriv η) x) x := fun x =>
    ((hη'.differentiable (by simp)) x).hasDerivAt
  have hc1 : Continuous (deriv η) := hη'.continuous
  have hc2 : Continuous (deriv (deriv η)) := (contDiff_infty_iff_deriv.mp hη').2.continuous
  have hc0 : Continuous η := hη.continuous
  have hcos : ∀ h : ℝ, HasDerivAt (fun h => 2 * cos (q * h) * η t) (2 * (-sin (q * h) * q) * η t) h := fun h =>
    ((((hasDerivAt_id' h).const_mul q).cos).const_mul 2).mul_const (η t) |>.congr_deriv (by ring)
  have hsin : ∀ h : ℝ, HasDerivAt (fun h => 2 * q * sin (q * h) * η t) (2 * q * (cos (q * h) * q) * η t) h :=
    fun h => ((((hasDerivAt_id' h).const_mul q).sin).const_mul (2 * q)).mul_const (η t) |>.congr_deriv (by ring)
  have hf1 : ∀ h : ℝ, HasDerivAt (fun h => η (t + h) + η (t - h) - 2 * cos (q * h) * η t)
      (deriv η (t + h) - deriv η (t - h) + 2 * q * sin (q * h) * η t) h := fun h =>
    ((hasDerivAt_shift_add hd1 t h).add (hasDerivAt_shift_sub hd1 t h)).sub (hcos h) |>.congr_deriv (by ring)
  have hf2 : ∀ h : ℝ, HasDerivAt (fun h => deriv η (t + h) - deriv η (t - h) + 2 * q * sin (q * h) * η t)
      (deriv (deriv η) (t + h) + deriv (deriv η) (t - h) + 2 * q ^ 2 * cos (q * h) * η t) h := fun h =>
    ((hasDerivAt_shift_add hd2 t h).sub (hasDerivAt_shift_sub hd2 t h)).add (hsin h) |>.congr_deriv (by ring)
  have hg1 : ∀ h : ℝ, HasDerivAt (fun h : ℝ => h ^ 2) (2 * h) h := fun h => by
    simpa using hasDerivAt_pow 2 h
  have hg2 : ∀ h : ℝ, HasDerivAt (fun h : ℝ => 2 * h) 2 h := fun h => by
    simpa using (hasDerivAt_id' h).const_mul (2 : ℝ)
  have hne : ∀ᶠ h in 𝓝[>] (0 : ℝ), 2 * h ≠ 0 :=
    eventually_nhdsWithin_of_forall fun h hh => (mul_pos two_pos (mem_Ioi.mp hh)).ne'
  have hne2 : ∀ᶠ h in 𝓝[>] (0 : ℝ), (2 : ℝ) ≠ 0 := Eventually.of_forall fun _ => two_ne_zero
  have lim0 : ∀ F : ℝ → ℝ, Continuous F → F 0 = 0 → Tendsto F (𝓝[>] 0) (𝓝 0) := fun F hF h0 =>
    (hF.tendsto' 0 0 h0).mono_left nhdsWithin_le_nhds
  have inner : Tendsto (fun h => (deriv η (t + h) - deriv η (t - h) + 2 * q * sin (q * h) * η t) / (2 * h))
      (𝓝[>] 0) (𝓝 (deriv (deriv η) t + q ^ 2 * η t)) := by
    refine HasDerivAt.lhopital_zero_nhdsGT (Eventually.of_forall hf2) (Eventually.of_forall hg2) hne2
      (lim0 _ (by fun_prop) (by simp)) (lim0 _ (by fun_prop) (by simp)) ?_
    have hcont : Continuous (fun h => (deriv (deriv η) (t + h) + deriv (deriv η) (t - h) +
        2 * q ^ 2 * cos (q * h) * η t) / 2) := by fun_prop
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    convert this using 2
    simp only [add_zero, sub_zero, mul_zero, cos_zero, mul_one]
    ring
  exact HasDerivAt.lhopital_zero_nhdsGT (Eventually.of_forall hf1) (Eventually.of_forall hg1) hne
    (lim0 _ (by fun_prop) (by simp; ring)) (lim0 _ (by fun_prop) (by simp)) inner

/-- Uniform bound on the corrected second difference quotient. -/
theorem second_diff_bound {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) {M0 M2 : ℝ} (h0 : ∀ x, |η x| ≤ M0)
    (h2 : ∀ x, |deriv (deriv η) x| ≤ M2) (q t : ℝ) {h : ℝ} (hh : 0 < h) :
    |(η (t + h) + η (t - h) - 2 * cos (q * h) * η t) / h ^ 2| ≤ 2 * M2 + q ^ 2 * M0 := by
  have hη' : ContDiff ℝ ∞ (deriv η) := (contDiff_infty_iff_deriv.mp hη).2
  have hd1 : ∀ x, HasDerivAt η (deriv η x) x := fun x => ((hη.differentiable (by simp)) x).hasDerivAt
  have hd2 : ∀ x, HasDerivAt (deriv η) (deriv (deriv η) x) x := fun x =>
    ((hη'.differentiable (by simp)) x).hasDerivAt
  have hstep1 : ∀ s : ℝ, |deriv η (t + s) - deriv η (t - s)| ≤ M2 * (2 * |s|) := by
    intro s
    have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (f := deriv η) (f' := deriv (deriv η))
      (fun x _ => (hd2 x).hasDerivWithinAt) (fun x _ => by rw [Real.norm_eq_abs]; exact h2 x)
      (mem_univ (t - s)) (mem_univ (t + s))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, show t + s - (t - s) = 2 * s by ring, abs_mul,
      abs_of_pos (two_pos : (0 : ℝ) < 2)] at this
    exact this
  have hk : |η (t + h) + η (t - h) - 2 * η t| ≤ 2 * M2 * h ^ 2 := by
    have := (convex_Icc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => η (t + s) + η (t - s)) (f' := fun s => deriv η (t + s) - deriv η (t - s))
      (C := M2 * (2 * h))
      (fun s _ => ((hasDerivAt_shift_add hd1 t s).add (hasDerivAt_shift_sub hd1 t s)).hasDerivWithinAt.congr_deriv
        (by ring))
      (fun s hs => by
        rw [Real.norm_eq_abs]
        refine (hstep1 s).trans ?_
        have hM2 : 0 ≤ M2 := (abs_nonneg _).trans (h2 0)
        rw [abs_of_nonneg hs.1]
        exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) hM2)
      (left_mem_Icc.mpr hh.le) (right_mem_Icc.mpr hh.le)
    simp only [add_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hh] at this
    have e1 : η (t + h) + η (t - h) - 2 * η t = η (t + h) + η (t - h) - (η t + η t) := by ring
    calc |η (t + h) + η (t - h) - 2 * η t| = |η (t + h) + η (t - h) - (η t + η t)| := by rw [e1]
      _ ≤ M2 * (2 * h) * h := this
      _ = 2 * M2 * h ^ 2 := by ring
  have hc1 : 0 ≤ 1 - cos (q * h) := by linarith [cos_le_one (q * h)]
  have hc2 : 1 - cos (q * h) ≤ (q * h) ^ 2 / 2 := by linarith [one_sub_sq_div_two_le_cos (x := q * h)]
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (h0 0)
  have hB : |2 * (1 - cos (q * h)) * η t| ≤ q ^ 2 * M0 * h ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 2 * (1 - cos (q * h)))]
    calc 2 * (1 - cos (q * h)) * |η t| ≤ 2 * (1 - cos (q * h)) * M0 :=
          mul_le_mul_of_nonneg_left (h0 t) (by linarith)
      _ ≤ 2 * ((q * h) ^ 2 / 2) * M0 := by gcongr
      _ = q ^ 2 * M0 * h ^ 2 := by ring
  have hsplit : η (t + h) + η (t - h) - 2 * cos (q * h) * η t =
      (η (t + h) + η (t - h) - 2 * η t) + 2 * (1 - cos (q * h)) * η t := by ring
  have hnum : |η (t + h) + η (t - h) - 2 * cos (q * h) * η t| ≤ (2 * M2 + q ^ 2 * M0) * h ^ 2 := by
    rw [hsplit]
    calc _ ≤ |η (t + h) + η (t - h) - 2 * η t| + |2 * (1 - cos (q * h)) * η t| := abs_add_le _ _
      _ ≤ 2 * M2 * h ^ 2 + q ^ 2 * M0 * h ^ 2 := add_le_add hk hB
      _ = (2 * M2 + q ^ 2 * M0) * h ^ 2 := by ring
  have hh2 : 0 < h ^ 2 := pow_pos hh 2
  rw [abs_div, abs_of_pos hh2, div_le_iff₀ hh2]
  exact hnum

/-- Pairing the centered inequality with `η ≥ 0` and moving the shifts onto `η`. -/
theorem shifted_pairing_nonneg {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (hc : Continuous φ) (htc : TrigConvex q φ)
    {η : ℝ → ℝ} (hη : Continuous η) (hcs : HasCompactSupport η) (hpos : ∀ x, 0 ≤ η x) {h : ℝ} (hh : 0 < h)
    (hqh : q * h < π / 2) :
    0 ≤ ∫ x, φ x * ((η (x + h) + η (x - h) - 2 * cos (q * h) * η x) / h ^ 2) := by
  have hcsA : HasCompactSupport (fun x => η (x + h)) := hcs.comp_homeomorph (Homeomorph.addRight h)
  have hcsB : HasCompactSupport (fun x => η (x - h)) := hcs.comp_homeomorph (Homeomorph.subRight h)
  have int_of : ∀ ψ κ : ℝ → ℝ, Continuous ψ → Continuous κ → HasCompactSupport κ →
      MeasureTheory.Integrable (fun x => ψ x * κ x) := fun ψ κ hψ hκ hκs =>
    (hψ.mul hκ).integrable_of_hasCompactSupport hκs.mul_left
  have iA := int_of φ _ hc (by fun_prop) hcsA
  have iB := int_of φ _ hc (by fun_prop) hcsB
  have iC := int_of φ η hc hη hcs
  have iD := int_of (fun x => φ (x - h)) η (by fun_prop) hη hcs
  have iE := int_of (fun x => φ (x + h)) η (by fun_prop) hη hcs
  have t1 : ∫ x, φ x * η (x + h) = ∫ x, φ (x - h) * η x := by
    rw [← MeasureTheory.integral_sub_right_eq_self (fun x => φ x * η (x + h)) h]
    simp only [sub_add_cancel]
  have t2 : ∫ x, φ x * η (x - h) = ∫ x, φ (x + h) * η x := by
    rw [← MeasureTheory.integral_add_right_eq_self (fun x => φ x * η (x - h)) h]
    simp only [add_sub_cancel_right]
  have e : ∀ x, φ x * ((η (x + h) + η (x - h) - 2 * cos (q * h) * η x) / h ^ 2) =
      (φ x * η (x + h) + φ x * η (x - h) - 2 * cos (q * h) * (φ x * η x)) / h ^ 2 := fun x => by ring
  have e' : ∀ x, (φ (x - h) + φ (x + h) - 2 * cos (q * h) * φ x) * η x =
      φ (x - h) * η x + φ (x + h) * η x - 2 * cos (q * h) * (φ x * η x) := fun x => by ring
  have hnn : 0 ≤ ∫ x, (φ (x - h) + φ (x + h) - 2 * cos (q * h) * φ x) * η x := by
    refine MeasureTheory.integral_nonneg fun x => mul_nonneg ?_ (hpos x)
    have := centered_of_trigConvex htc (t := x) hq hh hqh
    linarith
  simp_rw [e]
  simp_rw [e'] at hnn
  have L1 : ∫ x, (φ x * η (x + h) + φ x * η (x - h) - 2 * cos (q * h) * (φ x * η x)) =
      (∫ x, φ x * η (x + h)) + (∫ x, φ x * η (x - h)) - 2 * cos (q * h) * ∫ x, φ x * η x := by
    rw [MeasureTheory.integral_sub, MeasureTheory.integral_add iA iB, MeasureTheory.integral_const_mul]
    · exact iA.add iB
    · exact iC.const_mul _
  have L2 : ∫ x, (φ (x - h) * η x + φ (x + h) * η x - 2 * cos (q * h) * (φ x * η x)) =
      (∫ x, φ (x - h) * η x) + (∫ x, φ (x + h) * η x) - 2 * cos (q * h) * ∫ x, φ x * η x := by
    rw [MeasureTheory.integral_sub, MeasureTheory.integral_add iD iE, MeasureTheory.integral_const_mul]
    · exact iD.add iE
    · exact iC.const_mul _
  rw [MeasureTheory.integral_div, L1, t1, t2]
  rw [L2] at hnn
  exact div_nonneg hnn (sq_nonneg h)

/-- **Trigonometric convexity ⇒ weak positivity of `φ'' + q² φ`** (every `q > 0`, `φ` continuous). -/
theorem positiveAngularDistribution_of_trigConvex {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (hc : Continuous φ)
    (htc : TrigConvex q φ) : PositiveAngularDistribution q φ := by
  intro η hη hcs hpos
  have hη' : ContDiff ℝ ∞ (deriv η) := (contDiff_infty_iff_deriv.mp hη).2
  have hc2 : Continuous (deriv (deriv η)) := (contDiff_infty_iff_deriv.mp hη').2.continuous
  obtain ⟨M0, hM0⟩ := hcs.exists_bound_of_continuous hη.continuous
  obtain ⟨M2, hM2⟩ := hcs.deriv.deriv.exists_bound_of_continuous hc2
  set C := 2 * M2 + q ^ 2 * M0 with hC
  set K := Metric.cthickening 1 (tsupport η) with hK
  have hKc : IsCompact K := hcs.isCompact.cthickening
  have hzero : ∀ x, x ∉ K → η x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (Metric.mem_cthickening_of_dist_le x x 1 _ hx' (by simp))
  have hzero' : ∀ x h : ℝ, x ∉ K → |h| ≤ 1 → η (x + h) = 0 := fun x h hx hh1 =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (Metric.mem_cthickening_of_dist_le x (x + h) 1 _ hx'
      (by rw [Real.dist_eq, show x - (x + h) = -h by ring, abs_neg]; exact hh1))
  set bound : ℝ → ℝ := K.indicator (fun x => ‖φ x‖ * C) with hbound
  have hbound_int : MeasureTheory.Integrable bound :=
    ((by fun_prop : Continuous (fun x => ‖φ x‖ * C)).continuousOn.integrableOn_compact hKc).integrable_indicator
      hKc.measurableSet
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := MeasureTheory.volume)
    (l := 𝓝[>] (0 : ℝ)) (F := fun h x => φ x * ((η (x + h) + η (x - h) - 2 * cos (q * h) * η x) / h ^ 2))
    (f := fun x => φ x * (deriv (deriv η) x + q ^ 2 * η x)) bound
    (Eventually.of_forall fun h => (by fun_prop : Continuous fun x =>
      φ x * ((η (x + h) + η (x - h) - 2 * cos (q * h) * η x) / h ^ 2)).aestronglyMeasurable)
    (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
      refine MeasureTheory.ae_of_all _ fun x => ?_
      by_cases hx : x ∈ K
      · have hb0 : ∀ y, |η y| ≤ M0 := fun y => by rw [← Real.norm_eq_abs]; exact hM0 y
        have hb2 : ∀ y, |deriv (deriv η) y| ≤ M2 := fun y => by rw [← Real.norm_eq_abs]; exact hM2 y
        have hb := second_diff_bound hη hb0 hb2 q x hh.1
        calc ‖φ x * ((η (x + h) + η (x - h) - 2 * cos (q * h) * η x) / h ^ 2)‖
            = ‖φ x‖ * |(η (x + h) + η (x - h) - 2 * cos (q * h) * η x) / h ^ 2| := by
              rw [norm_mul, Real.norm_eq_abs (_ / h ^ 2)]
          _ ≤ ‖φ x‖ * C := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
          _ = bound x := by rw [hbound, indicator_of_mem hx]
      · rw [hbound, indicator_of_notMem hx, hzero x hx, hzero' x h hx (by rw [abs_of_pos hh.1]; exact hh.2.le),
          show x - h = x + -h by ring, hzero' x (-h) hx (by rw [abs_neg, abs_of_pos hh.1]; exact hh.2.le)]
        simp)
    hbound_int
    (MeasureTheory.ae_of_all _ fun x => (second_diff_tendsto hη q x).const_mul (φ x))
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      0 ≤ ∫ x, φ x * ((η (x + h) + η (x - h) - 2 * cos (q * h) * η x) / h ^ 2) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 / q by positivity)] with h hh
    have hqh : q * h < π / 2 := by
      have := hh.2
      rw [lt_div_iff₀ hq] at this
      linarith
    exact shifted_pairing_nonneg hq hc htc hη.continuous hcs hpos hh.1 hqh
  exact ge_of_tendsto hlim hev

/-! ### The weak inequality gives trigonometric convexity -/

/-- `t ↦ F (x - t)` has second derivative `F'' (x - t)`. -/
theorem deriv_deriv_reflect {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (x : ℝ) :
    deriv (deriv (fun t => F (x - t))) = fun t => deriv (deriv F) (x - t) := by
  have hF' : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  have hd1 : ∀ y, HasDerivAt F (deriv F y) y := fun y => ((hF.differentiable (by simp)) y).hasDerivAt
  have hd2 : ∀ y, HasDerivAt (deriv F) (deriv (deriv F) y) y := fun y =>
    ((hF'.differentiable (by simp)) y).hasDerivAt
  have e1 : deriv (fun t => F (x - t)) = fun t => -deriv F (x - t) :=
    funext fun t => (hasDerivAt_shift_sub hd1 x t).deriv
  rw [e1]
  funext t
  have := (hasDerivAt_shift_sub hd2 x t).neg
  rw [neg_neg] at this
  exact this.deriv

/-- A nonnegative mollification `ρ ⋆ φ` satisfies `(ρ ⋆ φ)'' + q² (ρ ⋆ φ) ≥ 0` pointwise: at `x` this is the weak
inequality tested with `t ↦ ρ (x - t)`. -/
theorem mollified_nonneg {q : ℝ} {φ : ℝ → ℝ} (hc : Continuous φ) (hpad : PositiveAngularDistribution q φ)
    (b : ContDiffBump (0 : ℝ)) (x : ℝ) :
    0 ≤ deriv (deriv (convolution (b.normed volume) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume)) x +
      q ^ 2 * convolution (b.normed volume) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  have hρs : ContDiff ℝ ∞ (b.normed volume) := b.contDiff_normed
  have hρcs : HasCompactSupport (b.normed volume) := b.hasCompactSupport_normed
  have hρ' : ContDiff ℝ ∞ (deriv (b.normed volume)) := (contDiff_infty_iff_deriv.mp hρs).2
  have hli : LocallyIntegrable φ volume := hc.locallyIntegrable
  have hD1 : deriv (convolution (b.normed volume) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume) =
      convolution (deriv (b.normed volume)) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    funext fun y => (hρcs.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρs.of_le (by simp)) hli
      y).deriv
  have hD2 : deriv (convolution (deriv (b.normed volume)) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume) =
      convolution (deriv (deriv (b.normed volume))) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    funext fun y => (hρcs.deriv.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (hρ'.of_le (by simp)) hli y).deriv
  rw [hD1, hD2, convolution_eq_swap, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hη : ContDiff ℝ ∞ (fun t => b.normed volume (x - t)) := hρs.comp (contDiff_const.sub contDiff_id)
  have hηcs : HasCompactSupport (fun t => b.normed volume (x - t)) :=
    hρcs.comp_homeomorph (Homeomorph.subLeft x)
  have hAcs : HasCompactSupport (fun t => deriv (deriv (b.normed volume)) (x - t)) :=
    hρcs.deriv.deriv.comp_homeomorph (Homeomorph.subLeft x)
  have hρ''c : Continuous (deriv (deriv (b.normed volume))) :=
    (contDiff_infty_iff_deriv.mp hρ').2.continuous
  have iA : Integrable (fun t => deriv (deriv (b.normed volume)) (x - t) * φ t) :=
    ((by fun_prop : Continuous fun t => deriv (deriv (b.normed volume)) (x - t)).mul hc).integrable_of_hasCompactSupport
      hAcs.mul_right
  have iB : Integrable (fun t => b.normed volume (x - t) * φ t) :=
    ((by fun_prop : Continuous fun t => b.normed volume (x - t)).mul hc).integrable_of_hasCompactSupport
      hηcs.mul_right
  have hp := hpad _ hη hηcs (fun t => b.nonneg_normed _)
  rw [deriv_deriv_reflect hρs x] at hp
  have e : (∫ t, φ t * (deriv (deriv (b.normed volume)) (x - t) + q ^ 2 * b.normed volume (x - t))) =
      (∫ t, deriv (deriv (b.normed volume)) (x - t) * φ t) + q ^ 2 * ∫ t, b.normed volume (x - t) * φ t := by
    rw [← integral_const_mul, ← integral_add iA (iB.const_mul _)]
    congr 1
    funext t
    ring
  rw [e] at hp
  exact hp

/-- The weak inequality gives the centered chord inequality on every chord with `q d ≤ π`: pair the mollified
profile with the chord tent, then let the mollifier shrink. -/
theorem centered_of_positiveAngularDistribution {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hpad : PositiveAngularDistribution q φ) {t d : ℝ} (hd : 0 < d) (hdq : d ≤ π / q) :
    2 * cos (q * d) * φ t ≤ φ (t - d) + φ (t + d) := by
  let bump : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    ⟨1 / ((n : ℝ) + 1), 2 * (1 / ((n : ℝ) + 1)), by positivity, by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith⟩
  have hr : Tendsto (fun n => (bump n).rOut) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
    rw [mul_zero] at this
    exact this
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℝ → ℝ,
      Φ = fun n => convolution ((bump n).normed volume) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume := ⟨_, rfl⟩
  have hsmooth : ∀ n, ContDiff ℝ ∞ (Φ n) := fun n => by
    rw [hΦ]
    exact (bump n).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (bump n).contDiff_normed hc.locallyIntegrable
  have hcen : ∀ n, 2 * cos (q * d) * Φ n t ≤ Φ n (t - d) + Φ n (t + d) := by
    intro n
    have hid := ChordTent.tent_distribution q t d hq hd (Φ n) (hsmooth n)
    have hnn : 0 ≤ ∫ u, chordTent q t d u * (deriv (deriv (Φ n)) u + q ^ 2 * Φ n u) := by
      refine integral_nonneg fun u => mul_nonneg (ChordTent.tent_nonneg q t d hq ⟨hd, hdq⟩ u) ?_
      rw [hΦ]
      exact mollified_nonneg hc hpad (bump n) u
    rw [hid] at hnn
    have hq' : 0 ≤ q * ((Φ n (t - d) + Φ n (t + d)) - 2 * cos (q * d) * Φ n t) := by linarith
    have := (mul_nonneg_iff_of_pos_left hq).mp hq'
    linarith
  have hlim : ∀ y, Tendsto (fun n => Φ n y) atTop (𝓝 (φ y)) := fun y => by
    rw [hΦ]
    exact ContDiffBump.convolution_tendsto_right_of_continuous hr hc y
  exact le_of_tendsto_of_tendsto' ((hlim t).const_mul (2 * cos (q * d))) ((hlim (t - d)).add (hlim (t + d))) hcen

/-- **The weak inequality ⇒ trigonometric convexity** (every `q > 0`, `φ` continuous). -/
theorem trigConvex_of_positiveAngularDistribution {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hpad : PositiveAngularDistribution q φ) : TrigConvex q φ :=
  trigConvex_of_centered hq hc (L := π / q) (by positivity) fun _ _ hd hdL =>
    centered_of_positiveAngularDistribution hq hc hpad hd hdL.le

/-- **One-variable bridge** (sec2_obstacle.tex l.58-60): for continuous `φ` and every `q > 0`, trigonometric
`q`-convexity is equivalent to `φ'' + q² φ ≥ 0` against every nonnegative smooth compactly supported test. -/
theorem trigConvex_iff_positiveAngularDistribution {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (hc : Continuous φ) :
    TrigConvex q φ ↔ PositiveAngularDistribution q φ :=
  ⟨positiveAngularDistribution_of_trigConvex hq hc, trigConvex_of_positiveAngularDistribution hq hc⟩

end GKSharp.Proofs.TrigDistribution

