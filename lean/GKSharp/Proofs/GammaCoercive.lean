/- uniform coercivity for the actual asymmetric complex-ratio Gamma.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.Gamma
open Real Filter Topology
namespace GKSharp.Coercive

noncomputable def lowerPositive (p C a s : ℝ) : ℝ :=
  C ^ p * (1 - s) ^ p - (1 + a * s) ^ p

noncomputable def lowerNegative (p C a s : ℝ) : ℝ :=
  C ^ p * (1 - s) ^ p - (a + s) ^ p

theorem gamma_normalized_positive (p C : ℝ) (rho : ℂ) (y t : ℝ) :
    gamma p C rho y t = Real.exp (p / 2 * y) *
      (C ^ p * ‖unitPoint t + (Real.exp (-y) : ℂ)‖ ^ p -
        ‖unitPoint t + (Real.exp (-y) : ℂ) * rho‖ ^ p) := by
  have hex : (Real.exp y : ℂ) * (Real.exp (-y) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have hn (a : ℂ) : ‖(Real.exp y : ℂ) * unitPoint t + a‖ =
      Real.exp y * ‖unitPoint t + (Real.exp (-y) : ℂ) * a‖ := by
    calc
      _ = ‖(Real.exp y : ℂ) * (unitPoint t + (Real.exp (-y) : ℂ) * a)‖ := by
        congr 1
        calc
          _ = (Real.exp y : ℂ) * unitPoint t +
              ((Real.exp y : ℂ) * (Real.exp (-y) : ℂ)) * a := by rw [hex, one_mul]
          _ = _ := by ring
      _ = _ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]
  have hf : (Real.exp y) ^ (-(p / 2)) * (Real.exp y) ^ p = Real.exp (p / 2 * y) := by
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  rw [gamma_radial]
  unfold obstacleG
  rw [add_comm (1 : ℂ) ((Real.exp y : ℂ) * unitPoint t),
    add_comm rho ((Real.exp y : ℂ) * unitPoint t), hn 1, hn rho, mul_one,
    Real.mul_rpow (Real.exp_pos y).le (norm_nonneg _),
    Real.mul_rpow (Real.exp_pos y).le (norm_nonneg _)]
  calc
    _ = ((Real.exp y) ^ (-(p / 2)) * (Real.exp y) ^ p) *
        (C ^ p * ‖unitPoint t + (Real.exp (-y) : ℂ)‖ ^ p -
          ‖unitPoint t + (Real.exp (-y) : ℂ) * rho‖ ^ p) := by ring
    _ = _ := by rw [hf]

theorem gamma_normalized_negative (p C : ℝ) (rho : ℂ) (y t : ℝ) :
    gamma p C rho (-y) t = Real.exp (p / 2 * y) *
      (C ^ p * ‖(Real.exp (-y) : ℂ) * unitPoint t + 1‖ ^ p -
        ‖(Real.exp (-y) : ℂ) * unitPoint t + rho‖ ^ p) := by
  rw [gamma_radial]
  unfold obstacleG
  have hf : (Real.exp (-y)) ^ (-(p / 2)) = Real.exp (p / 2 * y) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hf]
  simp only [add_comm]

theorem gamma_lower_positive {p : ℝ} (hp : 0 < p) (C : ℝ) (hC0 : 0 ≤ C) (rho : ℂ)
    (y t : ℝ) (hy : 0 ≤ y) :
    Real.exp (p / 2 * y) * lowerPositive p C ‖rho‖ (Real.exp (-y)) ≤ gamma p C rho y t := by
  let s := Real.exp (-y)
  have hs0 : 0 < s := Real.exp_pos _
  have hs1 : s ≤ 1 := by
    dsimp [s]
    simpa using Real.exp_le_exp.mpr (show -y ≤ 0 by linarith)
  have ha : 1 - s ≤ ‖unitPoint t + (s : ℂ)‖ := by
    have hh := norm_sub_norm_le (unitPoint t) (-(s : ℂ))
    simpa only [norm_unitPoint, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs0, sub_neg_eq_add] using hh
  have hb : ‖unitPoint t + (s : ℂ) * rho‖ ≤ 1 + ‖rho‖ * s := by
    have hh := norm_add_le (unitPoint t) ((s : ℂ) * rho)
    simpa [norm_unitPoint, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0, mul_comm] using hh
  have hpa := Real.rpow_le_rpow (show 0 ≤ 1 - s by linarith) ha hp.le
  have hpb := Real.rpow_le_rpow (norm_nonneg _) hb hp.le
  rw [gamma_normalized_positive]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  change C ^ p * (1 - s) ^ p - (1 + ‖rho‖ * s) ^ p ≤
    C ^ p * ‖unitPoint t + (s : ℂ)‖ ^ p - ‖unitPoint t + (s : ℂ) * rho‖ ^ p
  linarith [mul_le_mul_of_nonneg_left hpa (Real.rpow_nonneg hC0 p)]

theorem gamma_lower_negative {p : ℝ} (hp : 0 < p) (C : ℝ) (hC0 : 0 ≤ C) (rho : ℂ)
    (y t : ℝ) (hy : 0 ≤ y) :
    Real.exp (p / 2 * y) * lowerNegative p C ‖rho‖ (Real.exp (-y)) ≤ gamma p C rho (-y) t := by
  let s := Real.exp (-y)
  have hs0 : 0 < s := Real.exp_pos _
  have hs1 : s ≤ 1 := by
    dsimp [s]
    simpa using Real.exp_le_exp.mpr (show -y ≤ 0 by linarith)
  have hn : ‖(s : ℂ) * unitPoint t‖ = s := by
    rw [norm_mul, norm_unitPoint, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  have ha : 1 - s ≤ ‖(s : ℂ) * unitPoint t + 1‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (-((s : ℂ) * unitPoint t))
    simpa only [norm_one, norm_neg, hn, sub_neg_eq_add, add_comm] using hh
  have hb : ‖(s : ℂ) * unitPoint t + rho‖ ≤ ‖rho‖ + s := by
    have hh := norm_add_le ((s : ℂ) * unitPoint t) rho
    simpa only [hn, add_comm] using hh
  have hpa := Real.rpow_le_rpow (show 0 ≤ 1 - s by linarith) ha hp.le
  have hpb := Real.rpow_le_rpow (norm_nonneg _) hb hp.le
  rw [gamma_normalized_negative]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  change C ^ p * (1 - s) ^ p - (‖rho‖ + s) ^ p ≤
    C ^ p * ‖(s : ℂ) * unitPoint t + 1‖ ^ p - ‖(s : ℂ) * unitPoint t + rho‖ ^ p
  linarith [mul_le_mul_of_nonneg_left hpa (Real.rpow_nonneg hC0 p)]

theorem lowerPositive_continuousAt {p : ℝ} (hp : 0 < p) (C a : ℝ) :
    ContinuousAt (lowerPositive p C a) 0 := by
  unfold lowerPositive
  apply ContinuousAt.sub
  · exact continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inr hp.le))
  · exact (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).rpow_const (Or.inr hp.le)

theorem lowerNegative_continuousAt {p : ℝ} (hp : 0 < p) (C a : ℝ) :
    ContinuousAt (lowerNegative p C a) 0 := by
  unfold lowerNegative
  apply ContinuousAt.sub
  · exact continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inr hp.le))
  · exact (continuousAt_const.add continuousAt_id).rpow_const (Or.inr hp.le)

theorem positive_lower_tendsto {p C : ℝ} (hp : 0 < p) (hC : 1 < C) (rho : ℂ) :
    Tendsto (fun y => Real.exp (p / 2 * y) * lowerPositive p C ‖rho‖ (Real.exp (-y))) atTop atTop := by
  have hB : Tendsto (fun y => lowerPositive p C ‖rho‖ (Real.exp (-y))) atTop
      (𝓝 (lowerPositive p C ‖rho‖ 0)) :=
    (lowerPositive_continuousAt hp C ‖rho‖).tendsto.comp tendsto_exp_neg_atTop_nhds_zero
  have hk : 0 < lowerPositive p C ‖rho‖ 0 := by
    have hh := Real.rpow_lt_rpow (show (0 : ℝ) ≤ 1 by norm_num) hC hp
    simpa [lowerPositive] using sub_pos.mpr (show (1 : ℝ) < C ^ p by simpa using hh)
  exact (tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith : (0 : ℝ) < p / 2))).atTop_mul_pos hk hB

theorem negative_lower_tendsto {p C : ℝ} (hp : 0 < p) (rho : ℂ) (hC : ‖rho‖ < C) :
    Tendsto (fun y => Real.exp (p / 2 * y) * lowerNegative p C ‖rho‖ (Real.exp (-y))) atTop atTop := by
  have hB : Tendsto (fun y => lowerNegative p C ‖rho‖ (Real.exp (-y))) atTop
      (𝓝 (lowerNegative p C ‖rho‖ 0)) :=
    (lowerNegative_continuousAt hp C ‖rho‖).tendsto.comp tendsto_exp_neg_atTop_nhds_zero
  have hk : 0 < lowerNegative p C ‖rho‖ 0 := by
    have hh := Real.rpow_lt_rpow (norm_nonneg rho) hC hp
    simpa [lowerNegative] using sub_pos.mpr hh
  exact (tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith : (0 : ℝ) < p / 2))).atTop_mul_pos hk hB

/-- sec2_obstacle.tex (short v0.40):58–59. Uniform coercivity in the angle,
for every complex ratio, using separate positive/negative radial estimates. -/
theorem gamma_uniform_coercive {p C : ℝ} (hp : 0 < p) (rho : ℂ) (hC : max 1 ‖rho‖ < C) :
    UniformCoercive p C rho := by
  intro M
  have hC0 : 0 ≤ C := (zero_le_one.trans (le_max_left 1 ‖rho‖)).trans hC.le
  obtain ⟨Rp, hRp⟩ := tendsto_atTop_atTop.mp
    (positive_lower_tendsto hp (lt_of_le_of_lt (le_max_left _ _) hC) rho) M
  obtain ⟨Rm, hRm⟩ := tendsto_atTop_atTop.mp
    (negative_lower_tendsto hp rho (lt_of_le_of_lt (le_max_right _ _) hC)) M
  let Y := max 1 (max Rp Rm)
  have hY : 0 < Y := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hYp : Rp ≤ Y := (le_max_left _ _).trans (le_max_right _ _)
  have hYm : Rm ≤ Y := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Y, hY, ?_⟩
  intro y t hy
  by_cases hy0 : 0 ≤ y
  · rw [abs_of_nonneg hy0] at hy
    exact (hRp y (hYp.trans hy)).trans (gamma_lower_positive hp C hC0 rho y t hy0)
  · have hyn : y < 0 := lt_of_not_ge hy0
    rw [abs_of_neg hyn] at hy
    have hh := (hRm (-y) (hYm.trans hy)).trans
      (gamma_lower_negative hp C hC0 rho (-y) t (by linarith))
    simpa only [neg_neg] using hh

end GKSharp.Coercive

#print axioms GKSharp.Coercive.gamma_uniform_coercive
