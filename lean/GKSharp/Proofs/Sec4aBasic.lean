/- GKSharp/Proofs/Sec4aBasic.lean - slice (b), sec4a_criterion / sec4b_failure basics (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v0.70, each as `<row>_proved` with the row's exact type.
- reQPow_continuous (A:11-12): `Re z^q` is continuous; across the cut `cos(q arg z)` is even in `arg z`, so it equals
  `cos(q arccos(Re z/|z|))` off `0`, and `|Re z^q| ≤ |z|^q` at `0`.
- reQPow_inv (A:20-21): `arg z⁻¹ = ±arg z` and `cos` is even.
- quadratic_identities (A:46): eq:GK factors as `(s C² - sλ - (1-λ)C)(s C² - sλ + (1-λ)C) = 0`; the second factor is
  positive because `C > 1 > λ`.
- strict_jordan_pp (B:89-90): with `w = π/p - π/2 ∈ (0, π/2)`, `sin(π/p) = cos w` and Jordan's `sin w > 2w/π`.
-/
import GKSharp.Defs.Threshold
import GKSharp.Proofs.GKRoot

namespace GKSharp

open Set GKSharp.Threshold

/-- `Re z^q = |z|^q cos(q arccos(Re z/|z|))` off `0`: `cos(q arg z)` depends only on `|arg z| = arccos(Re z/|z|)`. -/
lemma sec4a_reQPow_eq_arccos (qq : ℝ) {w : ℂ} (hw : w ≠ 0) :
    reQPow w qq = ‖w‖ ^ qq * Real.cos (qq * Real.arccos (w.re / ‖w‖)) := by
  rw [reQPow, ← Complex.cos_arg hw]
  rcases le_total 0 (Complex.arg w) with h | h
  · rw [Real.arccos_cos h (Complex.arg_le_pi w)]
  · rw [← Real.cos_neg (Complex.arg w),
      Real.arccos_cos (neg_nonneg.2 h) (by linarith [Complex.neg_pi_lt_arg w]), mul_neg, Real.cos_neg]

/-- A:11-12, row `reQPow_continuous`. -/
theorem reQPow_continuous_proved (qq : ℝ) (hqq : 0 < qq) : Continuous (fun z : ℂ => reQPow z qq) := by
  have hpow : Continuous fun w : ℂ => ‖w‖ ^ qq := continuous_norm.rpow_const fun _ => Or.inr hqq.le
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have h0 : reQPow 0 qq = 0 := by simp [reQPow, Real.zero_rpow hqq.ne']
    show Filter.Tendsto (fun w : ℂ => reQPow w qq) (nhds 0) (nhds (reQPow 0 qq))
    rw [h0]
    refine squeeze_zero_norm (a := fun w : ℂ => ‖w‖ ^ qq) (fun w => ?_) ?_
    · rw [reQPow, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg w) qq)]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (norm_nonneg w) qq) (Real.abs_cos_le_one _)
    · simpa [Real.zero_rpow hqq.ne'] using hpow.tendsto 0
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    have h1 : ContinuousAt (fun w : ℂ => w.re / ‖w‖) z :=
      Complex.continuous_re.continuousAt.div continuous_norm.continuousAt hn
    have h2 : ContinuousAt (fun w : ℂ => qq * Real.arccos (w.re / ‖w‖)) z :=
      continuousAt_const.mul (Real.continuous_arccos.continuousAt.comp h1)
    have hF : ContinuousAt (fun w : ℂ => ‖w‖ ^ qq * Real.cos (qq * Real.arccos (w.re / ‖w‖))) z :=
      hpow.continuousAt.mul (Real.continuous_cos.continuousAt.comp h2)
    refine hF.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact (sec4a_reQPow_eq_arccos qq hw).symm

/-- A:20-21, row `reQPow_inv`. -/
theorem reQPow_inv_proved (p : ℝ) (z : ℂ) (hz : z ≠ 0) :
    reQPow z⁻¹ (q p) = ‖z‖ ^ (-p) * reQPow z (q p) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hcos : Real.cos (q p * Complex.arg z⁻¹) = Real.cos (q p * Complex.arg z) := by
    rw [Complex.arg_inv]
    split_ifs with h
    · rw [h]
    · rw [mul_neg, Real.cos_neg]
  rw [reQPow, reQPow, hcos, norm_inv, Real.inv_rpow hn.le, ← mul_assoc, ← Real.rpow_neg hn.le, ← Real.rpow_add hn]
  congr 2
  unfold q
  ring

/-- `sin(π/p) > 0` for `1 < p`. -/
lemma sec4a_sn_pos {p : ℝ} (hp : 1 < p) : 0 < sn p :=
  Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hp)

/-- A:46, row `quadratic_identities`. -/
theorem quadratic_identities_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) :
    sn p * (gk p lam ^ 2 - 1) = (1 - lam) * (gk p lam - sn p) ∧
    gk p lam ^ 2 - lam = (1 - lam) * gk p lam / sn p := by
  obtain ⟨-, hl2⟩ := hlam
  have hs := sec4a_sn_pos hp
  set C := gk p (lam : ℂ) with hC
  have hgt : max 1 ‖(lam : ℂ)‖ < C :=
    gk_gt_max hp (ne_of_lt hp2) (fun h => hl2.ne (by exact_mod_cast h))
  have hC1 : 1 < C := lt_of_le_of_lt (le_max_left _ _) hgt
  have hn1 : ‖(lam : ℂ)‖ ^ 2 = lam ^ 2 := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hn2 : ‖(1 : ℂ) - (lam : ℂ)‖ ^ 2 = (1 - lam) ^ 2 := by
    rw [show (1 : ℂ) - (lam : ℂ) = ((1 - lam : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  have hq : (C ^ 2) ^ 2 - (1 + lam ^ 2 + (1 - lam) ^ 2 *
      (Real.cos (Real.pi / p) / Real.sin (Real.pi / p)) ^ 2) * C ^ 2 + lam ^ 2 = 0 := by
    have h := (gk_sq_larger_root p (lam : ℂ)).1
    simp only [gkQuad, gkMid] at h
    rw [hn1, hn2, Real.cot_eq_cos_div_sin] at h
    exact h
  have hsc := Real.sin_sq_add_cos_sq (Real.pi / p)
  have hcs : (Real.cos (Real.pi / p) / Real.sin (Real.pi / p)) ^ 2 * Real.sin (Real.pi / p) ^ 2 =
      Real.cos (Real.pi / p) ^ 2 := by
    have : Real.sin (Real.pi / p) ≠ 0 := hs.ne'
    field_simp
  have hkey : (sn p * C ^ 2 - sn p * lam - (1 - lam) * C) * (sn p * C ^ 2 - sn p * lam + (1 - lam) * C) = 0 := by
    unfold sn
    linear_combination Real.sin (Real.pi / p) ^ 2 * hq + C ^ 2 * (1 - lam) ^ 2 * hsc + C ^ 2 * (1 - lam) ^ 2 * hcs
  have hpos : 0 < sn p * C ^ 2 - sn p * lam + (1 - lam) * C := by
    have h1 : 0 < sn p * (C ^ 2 - lam) := mul_pos hs (by nlinarith)
    have h2 : 0 < (1 - lam) * C := mul_pos (by linarith) (by linarith)
    linarith
  have hmain : sn p * C ^ 2 - sn p * lam - (1 - lam) * C = 0 :=
    (mul_eq_zero.1 hkey).resolve_right hpos.ne'
  refine ⟨by linear_combination hmain, ?_⟩
  rw [eq_div_iff hs.ne']
  linear_combination hmain

/-- B:89-90, row `strict_jordan_pp`. -/
theorem strict_jordan_pp_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    p * dual p / 4 * sn p ^ 2 < 1 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  set w := Real.pi / p - Real.pi / 2 with hw
  have hw0 : 0 < w := by
    rw [hw, sub_pos]
    exact div_lt_div_of_pos_left Real.pi_pos hp0 hp2
  have hw1 : w < Real.pi / 2 := by
    have : Real.pi / p < Real.pi := div_lt_self Real.pi_pos hp
    rw [hw]
    linarith
  have hsin : 2 / Real.pi * w < Real.sin w := Real.mul_lt_sin hw0 hw1
  have h2w : 2 / Real.pi * w = (2 - p) / p := by
    rw [hw]
    field_simp
  have hsn : sn p = Real.cos w := by
    rw [hw, Real.cos_sub_pi_div_two]
    rfl
  have hpos : 0 < (2 - p) / p := div_pos (by linarith) hp0
  have hsin2 : ((2 - p) / p) ^ 2 < Real.sin w ^ 2 := by
    rw [h2w] at hsin
    nlinarith
  have hsq : sn p ^ 2 = 1 - Real.sin w ^ 2 := by
    rw [hsn]
    linarith [Real.sin_sq_add_cos_sq w]
  have hid : 1 - ((2 - p) / p) ^ 2 = 4 * (p - 1) / p ^ 2 := by
    field_simp
    ring
  have key : sn p ^ 2 < 4 * (p - 1) / p ^ 2 := by
    rw [hsq]
    linarith
  have hcoef : 0 < p * dual p / 4 := by
    unfold dual
    positivity
  calc p * dual p / 4 * sn p ^ 2 < p * dual p / 4 * (4 * (p - 1) / p ^ 2) := mul_lt_mul_of_pos_left key hcoef
    _ = 1 := by
      unfold dual
      field_simp

end GKSharp
