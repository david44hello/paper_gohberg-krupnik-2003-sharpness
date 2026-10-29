/- strict axis-origin gap from the actual C1 equality classification.
Frozen source: short_v0.70/sec4b_failure.tex:103–105.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.TheoremC1
import GKSharp.Proofs.CosineCriterion
import GKSharp.Proofs.Contact

namespace GKSharp
open Set Threshold ComplexConjugate

theorem curveZ_contact_im_negative {p lam : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl1 : lam < 1) :
    (curveZ p lam (Real.pi / p)).im < 0 := by
  obtain ⟨ht0, htpi, hs, -⟩ := theta0_bounds hp hp2
  obtain ⟨-, -, hr, -, -⟩ := curve_root_formula hp hp2 ht0 htpi hl hl1
  change ((curveR p lam (Real.pi / p) : ℂ) *
    Complex.exp (-((Real.pi / p : ℝ) : ℂ) * Complex.I)).im < 0
  rw [(polar_re_im (curveR p lam (Real.pi / p)) (Real.pi / p)).2]
  linarith [mul_pos hr hs]

/-- The C1 contacts have nonzero imaginary part, hence no positive real point is a zero. -/
theorem critD_positive_real_at_zero {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (r : ℝ) : 0 < critD p (gk p 0) (kConst p 0) 0 (r : ℂ) := by
  obtain ⟨hnonneg, hzeros⟩ := Proofs.TheoremC1.thm_C1_equality_proved hp hp2
    (show (-1 : ℝ) ≤ 0 by norm_num) le_rfl
  have him := curveZ_contact_im_negative hp hp2 (lam := 0) (by norm_num) (by norm_num)
  refine lt_of_le_of_ne (hnonneg _) ?_
  intro heq
  rcases hzeros (r : ℂ) heq.symm with hz | hz
  · have hh := congrArg Complex.im hz
    simp only [Complex.ofReal_im] at hh
    linarith
  · have hh := congrArg Complex.im hz
    simp only [Complex.ofReal_im, Complex.conj_im] at hh
    linarith

/-- Strict positivity at λ=0, with no numerical or analytic premise. -/
theorem axis_zero_positive_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    0 < Threshold.h p 0 := by
  have hC : max 1 ‖((0 : ℝ) : ℂ)‖ < gk p 0 :=
    gk_gt_max hp (ne_of_lt hp2) (by norm_num)
  obtain ⟨y, -, hmin⟩ := obstacle_eq_min (by linarith : 0 < p) (0 : ℂ) hC 0
  have hminor := (obstacle_cos_iff_critD_proved p 0 hp hp2 (by norm_num)).mpr
    (Proofs.TheoremC1.thm_C1_equality_proved hp hp2 (by norm_num) le_rfl).1
  have hnonneg := hminor 0 (by constructor <;> linarith [Real.pi_pos])
  simp only [abs_zero, mul_zero, Real.cos_zero, mul_one] at hnonneg
  change 0 < Threshold.obstacle p 0 0 - kConst p 0
  apply lt_of_le_of_ne (sub_nonneg.mpr hnonneg)
  intro heq
  have hgam : GKSharp.gamma p (gk p 0) (0 : ℂ) y 0 = kConst p 0 := by
    have heq' : GKSharp.obstacle p (gk p 0) (0 : ℂ) 0 - kConst p 0 = 0 := heq.symm
    rw [hmin] at heq'
    linarith
  have hy := Real.exp_pos y
  have hscale : (Real.exp y) ^ (-(p / 2)) * (Real.exp y) ^ (p / 2) = 1 := by
    rw [← Real.rpow_add hy, neg_add_cancel, Real.rpow_zero]
  have hg : (Real.exp y) ^ (-(p / 2)) *
      obstacleG p (gk p 0) (0 : ℂ) (Real.exp y : ℂ) = kConst p 0 := by
    simpa only [gamma_radial, unitPoint, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, mul_one] using hgam
  have hbracket : obstacleG p (gk p 0) (0 : ℂ) (Real.exp y : ℂ) -
      kConst p 0 * (Real.exp y) ^ (p / 2) = 0 := by
    have hs : (Real.exp y) ^ (-(p / 2)) ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
    apply (mul_eq_zero.mp (show (Real.exp y) ^ (-(p / 2)) *
      (obstacleG p (gk p 0) (0 : ℂ) (Real.exp y : ℂ) -
        kConst p 0 * (Real.exp y) ^ (p / 2)) = 0 by
          linear_combination hg - kConst p 0 * hscale)).resolve_left hs
  have hD := critD_positive_real_at_zero hp hp2 ((Real.exp y)⁻¹)
  have hz : ((Real.exp y : ℝ) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')
  have hid := critD_inv_factor p (gk p 0) (kConst p 0) 0 hz
  simp only [inv_inv] at hid
  have hre : reQPow (Real.exp y : ℂ) (p / 2) = (Real.exp y) ^ (p / 2) := by
    unfold reQPow
    rw [Complex.arg_ofReal_of_nonneg hy.le, mul_zero, Real.cos_zero, mul_one,
      Complex.norm_real, Real.norm_of_nonneg hy.le]
  simp only [Complex.ofReal_zero] at hid
  rw [hre, hbracket, mul_zero] at hid
  have hDzero : critD p (gk p 0) (kConst p 0) 0 (((Real.exp y)⁻¹ : ℝ) : ℂ) = 0 := by
    simpa only [Complex.ofReal_inv] using hid
  linarith

end GKSharp

#print axioms GKSharp.axis_zero_positive_proved
