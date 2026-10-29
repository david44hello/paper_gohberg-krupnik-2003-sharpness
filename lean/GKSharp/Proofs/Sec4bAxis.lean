/- GKSharp/Proofs/Sec4bAxis.lean - slice (b): the axis upper bound (4.7) and its rescaling (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v0.80, each as `<row>_proved` with the row's exact type.
- h_le_axisUpper (A:44-45, B:116-118): at `e^y = θ/(1-θ)`, `2cosh y + 2 = 1/(θ(1-θ))` and
  `e^y + λ²e^{-y} + 2λ = (λ + θ(1-λ))²/(θ(1-θ))`, so `Γ(y, 0)` is the bound; `Γ(·, 0) ≥ 0` (`C ≥ 1`, `0 ≤ λ < 1`)
  makes the infimum `≤` it.
- h_le_delta_g (B:128-133): `λ = 1 - δ`, `θ = 1 - s`; `δ T₁ = C^p - 1` (eq:GK: `sn(C² - 1) = δ(C - sn)`),
  `δ s φ(sδ) = 1 - (1 - sδ)^p`, `δ κ = K`. Premise row: cDelta_eq_gk (`CDeltaEqGkHyp`, its exact type).
-/
import GKSharp.Defs.ThresholdAnalysis
import GKSharp.Proofs.Sec4aBasic

namespace GKSharp

open Set GKSharp.Threshold

/-- The type of row `cDelta_eq_gk`. -/
abbrev CDeltaEqGkHyp : Prop :=
  ∀ (p delta : ℝ) (_hp : 1 < p) (_hp2 : p < 2) (_hd : delta ∈ Ico (0 : ℝ) 1),
    cDelta p delta = gk p ((1 - delta : ℝ) : ℂ)

/-- `Γ(y, 0)` for a real ratio `λ`. -/
lemma sec4b_gamma_axis (p C lam y : ℝ) :
    GKSharp.gamma p C (lam : ℂ) y 0 =
      C ^ p * (2 * Real.cosh y + 2) ^ (p / 2) - (Real.exp y + lam ^ 2 * Real.exp (-y) + 2 * lam) ^ (p / 2) := by
  have hre : (star (lam : ℂ) * unitPoint 0).re = lam := by simp [unitPoint]
  have hnorm : ‖(lam : ℂ)‖ ^ 2 = lam ^ 2 := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [GKSharp.gamma, Real.cos_zero, mul_one, hre, hnorm]

/-- `(u²/v)^{p/2} = u^p / v^{p/2}` for `u ≥ 0`, `v ≥ 0`. -/
lemma sec4b_sq_div_rpow {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (p : ℝ) :
    (u ^ 2 / v) ^ (p / 2) = u ^ p / v ^ (p / 2) := by
  rw [Real.div_rpow (sq_nonneg u) hv, ← Real.rpow_natCast u 2, ← Real.rpow_mul hu]
  norm_num
  ring_nf

/-- A:44-45, B:116-118, row `h_le_axisUpper`. -/
theorem h_le_axisUpper_proved (p lam theta : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (0 : ℝ) 1) (htheta : theta ∈ Ioo (0 : ℝ) 1) :
    Threshold.h p lam ≤ axisUpper p lam theta := by
  obtain ⟨hl0, hl1⟩ := hlam
  obtain ⟨ht0, ht1⟩ := htheta
  have hp0 : 0 < p := by linarith
  unfold Threshold.h axisUpper GKSharp.axisGap GKSharp.obstacle
  set C := gk p (lam : ℂ) with hC
  have hC1 : 1 ≤ C :=
    (lt_of_le_of_lt (le_max_left _ _) (gk_gt_max hp (ne_of_lt hp2) (ρ := (lam : ℂ))
      (fun h => hl1.ne (by exact_mod_cast h)))).le
  -- `Γ(·, 0) ≥ 0`
  have hlow : ∀ y : ℝ, 0 ≤ GKSharp.gamma p C (lam : ℂ) y 0 := by
    intro y
    rw [sec4b_gamma_axis]
    have hemy := Real.exp_pos (-y)
    have hcosh := Real.cosh_pos y
    have hB0 : 0 ≤ Real.exp y + lam ^ 2 * Real.exp (-y) + 2 * lam := by positivity
    have hBA : Real.exp y + lam ^ 2 * Real.exp (-y) + 2 * lam ≤ 2 * Real.cosh y + 2 := by
      rw [Real.cosh_eq]
      nlinarith [mul_nonneg (show 0 ≤ 1 - lam ^ 2 by nlinarith) hemy.le]
    have h1 : (Real.exp y + lam ^ 2 * Real.exp (-y) + 2 * lam) ^ (p / 2) ≤ (2 * Real.cosh y + 2) ^ (p / 2) :=
      Real.rpow_le_rpow hB0 hBA (by linarith)
    have h2 : (2 * Real.cosh y + 2) ^ (p / 2) ≤ C ^ p * (2 * Real.cosh y + 2) ^ (p / 2) :=
      le_mul_of_one_le_left (Real.rpow_nonneg (by linarith) _) (Real.one_le_rpow hC1 hp0.le)
    linarith
  -- the value at `e^y = θ/(1-θ)`
  have hr : 0 < theta / (1 - theta) := div_pos ht0 (by linarith)
  set y0 := Real.log (theta / (1 - theta)) with hy0
  have hey0 : Real.exp y0 = theta / (1 - theta) := Real.exp_log hr
  have hemy0 : Real.exp (-y0) = (1 - theta) / theta := by rw [Real.exp_neg, hey0, inv_div]
  have hv : 0 < theta * (1 - theta) := mul_pos ht0 (by linarith)
  have hu : 0 < lam + theta * (1 - lam) := by nlinarith
  have hA : 2 * Real.cosh y0 + 2 = 1 ^ 2 / (theta * (1 - theta)) := by
    rw [Real.cosh_eq, hey0, hemy0]
    field_simp
    ring
  have hB : Real.exp y0 + lam ^ 2 * Real.exp (-y0) + 2 * lam =
      (lam + theta * (1 - lam)) ^ 2 / (theta * (1 - theta)) := by
    rw [hey0, hemy0]
    field_simp
    ring
  have hval : GKSharp.gamma p C (lam : ℂ) y0 0 =
      (C ^ p - (lam + theta * (1 - lam)) ^ p) / (theta * (1 - theta)) ^ q p := by
    rw [sec4b_gamma_axis, hA, hB, sec4b_sq_div_rpow zero_le_one hv.le, sec4b_sq_div_rpow hu.le hv.le,
      Real.one_rpow]
    unfold q
    ring
  have hle : sInf (Set.range fun y : ℝ => GKSharp.gamma p C (lam : ℂ) y 0) ≤ GKSharp.gamma p C (lam : ℂ) y0 0 :=
    csInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact hlow y⟩ ⟨y0, rfl⟩
  linarith

/-- B:128-133, row `h_le_delta_g` (premise row `cDelta_eq_gk`). -/
theorem h_le_delta_g_proved (hcd : CDeltaEqGkHyp) (p delta s : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hd : delta ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    Threshold.h p (1 - delta) ≤ delta * g p delta s := by
  obtain ⟨hd0, hd1⟩ := hd
  obtain ⟨hs0, hs1⟩ := hs
  have hax := h_le_axisUpper_proved p (1 - delta) (1 - s) hp hp2 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  have hsn := sec4a_sn_pos hp
  have hcD : cDelta p delta = gk p ((1 - delta : ℝ) : ℂ) := hcd p delta hp hp2 ⟨hd0.le, hd1⟩
  -- eq:GK at `λ = 1 - δ`: `sn(C² - 1) = δ(C - sn)`
  have hq := (quadratic_identities_proved p (1 - delta) hp hp2 ⟨by linarith, by linarith⟩).1
  rw [show (1 : ℝ) - (1 - delta) = delta by ring] at hq
  set C := gk p ((1 - delta : ℝ) : ℂ) with hC
  have hC1 : 1 < C :=
    lt_of_le_of_lt (le_max_left _ _) (gk_gt_max hp (ne_of_lt hp2) (ρ := ((1 - delta : ℝ) : ℂ))
      (fun h => by
        have : (1 - delta : ℝ) = 1 := by exact_mod_cast h
        linarith))
  -- `δ T₁ = C^p - 1`
  have hT : delta * tOne p delta = C ^ p - 1 := by
    have hC1' : C ≠ 1 := hC1.ne'
    have hCm : C - 1 ≠ 0 := sub_ne_zero.2 hC1'
    have hCp : C + 1 ≠ 0 := by linarith
    have hsn' : sn p ≠ 0 := hsn.ne'
    have hkey : delta * (C - sn p) = sn p * (C - 1) * (C + 1) := by linear_combination -hq
    calc delta * tOne p delta = (C ^ p - 1) / (C - 1) * (delta * (C - sn p)) / (sn p * (C + 1)) := by
          unfold tOne powSlope
          rw [hcD, ite_eq_right hC1']
          ring
      _ = C ^ p - 1 := by
          rw [hkey]
          field_simp
  -- `δ s φ(sδ) = 1 - (1 - sδ)^p`
  have hP : delta * (s * phi p (s * delta)) = 1 - (1 - s * delta) ^ p := by
    have hne : (1 - s * delta) ≠ 1 := by nlinarith
    unfold phi powSlope
    rw [ite_eq_right hne]
    have hsd : (1 - s * delta) - 1 ≠ 0 := sub_ne_zero.2 hne
    field_simp
    ring
  -- `δ κ = K(1 - δ)`
  have hK : delta * kap p delta = kConst p (1 - delta) := by
    unfold kap kConst
    rw [hcD, ← hC]
    simp only [sn, cs, q]
    ring_nf
  -- the bound at `θ = 1 - s` is `δ g`
  have hbase : (1 - s) * (1 - (1 - s)) = s * (1 - s) := by ring
  have hrho : (1 - delta) + (1 - s) * (1 - (1 - delta)) = 1 - s * delta := by ring
  have hsum : delta * (tOne p delta + s * phi p (s * delta)) = C ^ p - (1 - s * delta) ^ p := by
    rw [mul_add, hT, hP]
    ring
  have hg : axisUpper p (1 - delta) (1 - s) = delta * g p delta s := by
    unfold axisUpper g
    rw [hbase, hrho, ← hC, ← hK, ← hsum]
    ring
  linarith

end GKSharp
