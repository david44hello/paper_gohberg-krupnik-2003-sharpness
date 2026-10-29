/- exact complex-ratio obstacle algebra.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential

namespace GKSharp
open Real

theorem gamma_real (p C lam y t : ℝ) :
    gamma p C (lam : ℂ) y t =
      C ^ p * (2 * cosh y + 2 * cos t) ^ (p / 2) -
        (exp y + lam ^ 2 * exp (-y) + 2 * lam * cos t) ^ (p / 2) := by
  simp [gamma, unitPoint, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Complex.mul_re, Complex.exp_ofReal_mul_I_re, mul_assoc]

/-- sec2_obstacle.tex:51. No restriction on the modulus of the real ratio. -/
theorem gamma_even_real (p C lam y t : ℝ) :
    gamma p C (lam : ℂ) y (-t) = gamma p C (lam : ℂ) y t := by
  rw [gamma_real, gamma_real, Real.cos_neg]

/-- sec2_obstacle.tex:51. The true infimum is even for a real ratio. -/
theorem obstacle_even_real (p C lam t : ℝ) :
    obstacle p C (lam : ℂ) (-t) = obstacle p C (lam : ℂ) t := by
  unfold obstacle
  congr 1
  exact congrArg Set.range (funext fun y => gamma_even_real p C lam y t)

theorem unitPoint_periodic : Function.Periodic unitPoint (2 * Real.pi) := by
  intro t
  unfold unitPoint
  rw [show (((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      (t : ℂ) * Complex.I + 2 * Real.pi * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem gamma_periodic (p C : ℝ) (rho : ℂ) (y : ℝ) :
    Function.Periodic (gamma p C rho y) (2 * Real.pi) := by
  intro t
  simp only [gamma, Real.cos_add_two_pi, unitPoint_periodic t]

theorem obstacle_periodic (p C : ℝ) (rho : ℂ) :
    Function.Periodic (obstacle p C rho) (2 * Real.pi) := by
  intro t
  unfold obstacle
  congr 1
  exact congrArg Set.range (funext fun y => gamma_periodic p C rho y t)

theorem continuous_gamma {p : ℝ} (hp : 0 < p) (C : ℝ) (rho : ℂ) :
    Continuous (fun x : ℝ × ℝ => gamma p C rho x.1 x.2) := by
  unfold gamma unitPoint
  fun_prop (disch := positivity)

theorem complex_norm_add_square (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * star w).re := by
  simpa only [Complex.normSq_eq_norm_sq, Complex.star_def] using Complex.normSq_add z w

/-- sec2_obstacle.tex:43. Both exact squared-modulus identities, including complexρ. -/
theorem pair_squared_bases (rho z w : ℂ) (hzw : z * w ≠ 0) :
    let y := log (‖z‖ / ‖w‖)
    let t := Complex.arg (z * w)
    ‖z + star w‖ ^ 2 = ‖z * w‖ * (2 * cosh y + 2 * cos t) ∧
    ‖z + rho * star w‖ ^ 2 = ‖z * w‖ *
      (exp y + ‖rho‖ ^ 2 * exp (-y) + 2 * (star rho * unitPoint t).re) := by
  have hz : z ≠ 0 := left_ne_zero_of_mul hzw
  have hw : w ≠ 0 := right_ne_zero_of_mul hzw
  have ha : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hb : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have he1 : exp (log (‖z‖ / ‖w‖)) = ‖z‖ / ‖w‖ := exp_log (div_pos ha hb)
  have he2 : exp (-log (‖z‖ / ‖w‖)) = ‖w‖ / ‖z‖ := by
    rw [exp_neg, he1, inv_div]
  have hrad : ‖z * w‖ * (2 * cosh (log (‖z‖ / ‖w‖))) = ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [norm_mul, cosh_eq, he1, he2]
    field_simp
  have hcos := Complex.norm_mul_cos_arg (z * w)
  have hrad2 : ‖z * w‖ * (exp (log (‖z‖ / ‖w‖)) + ‖rho‖ ^ 2 * exp (-log (‖z‖ / ‖w‖))) =
      ‖z‖ ^ 2 + (‖rho‖ * ‖w‖) ^ 2 := by
    rw [norm_mul, he1, he2]
    field_simp
  have hunit : (‖z * w‖ : ℂ) * unitPoint (Complex.arg (z * w)) = z * w :=
    Complex.norm_mul_exp_arg_mul_I (z * w)
  have hmul : (‖z * w‖ : ℂ) * (star rho * unitPoint (Complex.arg (z * w))) = star rho * (z * w) := by
    calc _ = star rho * ((‖z * w‖ : ℂ) * unitPoint (Complex.arg (z * w))) := by ring
         _ = _ := by rw [hunit]
  have hre : ‖z * w‖ * (star rho * unitPoint (Complex.arg (z * w))).re = (star rho * (z * w)).re := by
    have h := congrArg Complex.re hmul
    simpa only [Complex.re_ofReal_mul] using h
  constructor
  · rw [complex_norm_add_square, norm_star, star_star]
    nlinarith
  · rw [complex_norm_add_square, norm_mul, norm_star, star_mul, star_star]
    have he : z * (w * star rho) = star rho * (z * w) := by ring
    rw [he]
    nlinarith

/-- sec2_obstacle.tex:45–46. Exact factorization of the actual polynomial-pair integrand. -/
theorem pair_gamma_factor (p C : ℝ) (rho z w : ℂ) (hzw : z * w ≠ 0) :
    pairObstacle p C rho z w = ‖z * w‖ ^ (p / 2) *
      gamma p C rho (log (‖z‖ / ‖w‖)) (Complex.arg (z * w)) := by
  obtain ⟨hA, hB⟩ := pair_squared_bases rho z w hzw
  have hn : 0 < ‖z * w‖ := norm_pos_iff.mpr hzw
  have hAnon : 0 ≤ 2 * cosh (log (‖z‖ / ‖w‖)) + 2 * cos (Complex.arg (z * w)) := by
    have h := sq_nonneg ‖z + star w‖
    rw [hA] at h
    exact nonneg_of_mul_nonneg_right h hn
  have hBnon : 0 ≤ exp (log (‖z‖ / ‖w‖)) + ‖rho‖ ^ 2 * exp (-log (‖z‖ / ‖w‖)) +
      2 * (star rho * unitPoint (Complex.arg (z * w))).re := by
    have h := sq_nonneg ‖z + rho * star w‖
    rw [hB] at h
    exact nonneg_of_mul_nonneg_right h hn
  have hpow : ∀ u : ℂ, ‖u‖ ^ p = (‖u‖ ^ 2) ^ (p / 2) := by
    intro u
    rw [← Real.rpow_natCast_mul (norm_nonneg u)]
    congr 1
    ring
  unfold pairObstacle gamma
  rw [hpow, hpow, hA, hB, Real.mul_rpow hn.le hAnon, Real.mul_rpow hn.le hBnon]
  ring

theorem norm_unitPoint (t : ℝ) : ‖unitPoint t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I t

theorem unitPoint_arg (t : ℝ) : unitPoint (Complex.arg (unitPoint t)) = unitPoint t := by
  have h := Complex.norm_mul_exp_arg_mul_I (unitPoint t)
  rw [norm_unitPoint, Complex.ofReal_one, one_mul] at h
  exact h

/-- sec2_obstacle.tex:51–52. Radial representation for the exact complex-ratioΓ. -/
theorem gamma_radial (p C : ℝ) (rho : ℂ) (y t : ℝ) :
    gamma p C rho y t = (exp y) ^ (-(p / 2)) *
      obstacleG p C rho ((exp y : ℂ) * unitPoint t) := by
  let z : ℂ := (exp y : ℂ) * unitPoint t
  have hn : ‖z‖ = exp y := by
    dsimp only [z]
    rw [norm_mul, norm_unitPoint, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos y)]
  have hz : z ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact exp_pos y)
  have hu : unitPoint (Complex.arg z) = unitPoint t := by
    dsimp only [z]
    rw [Complex.arg_real_mul _ (exp_pos y)]
    exact unitPoint_arg t
  have hc : cos (Complex.arg z) = cos t := by
    have h := congrArg Complex.re hu
    simpa only [unitPoint, Complex.exp_ofReal_mul_I_re] using h
  have hg : gamma p C rho y (Complex.arg z) = gamma p C rho y t := by
    unfold gamma
    rw [hc, hu]
  have hb : obstacleG p C rho z = (exp y) ^ (p / 2) * gamma p C rho y t := by
    calc
      obstacleG p C rho z = pairObstacle p C rho z 1 := by
        simp only [obstacleG, pairObstacle, star_one, mul_one, add_comm]
      _ = _ := by
        have h := pair_gamma_factor p C rho z 1 (by simpa using hz)
        simpa only [mul_one, norm_one, div_one, hn, Real.log_exp, hg] using h
  have hi : (exp y) ^ (-(p / 2)) * (exp y) ^ (p / 2) = 1 := by
    rw [← Real.rpow_add (exp_pos y), neg_add_cancel, Real.rpow_zero]
  change gamma p C rho y t = (exp y) ^ (-(p / 2)) * obstacleG p C rho z
  rw [hb, ← mul_assoc, hi, one_mul]

/-- sec2_obstacle.tex:52. The realinfimum agrees with the positive-radius infimum without a compactness assumption. -/
theorem obstacle_radial (p C : ℝ) (rho : ℂ) (t : ℝ) :
    obstacle p C rho t = sInf {v : ℝ | ∃ r : ℝ, 0 < r ∧
      v = r ^ (-(p / 2)) * obstacleG p C rho ((r : ℂ) * unitPoint t)} := by
  have he : Set.range (fun y : ℝ => gamma p C rho y t) =
      {v : ℝ | ∃ r : ℝ, 0 < r ∧ v = r ^ (-(p / 2)) * obstacleG p C rho ((r : ℂ) * unitPoint t)} := by
    ext v
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨exp y, exp_pos y, gamma_radial p C rho y t⟩
    · rintro ⟨r, hr, hv⟩
      refine ⟨log r, ?_⟩
      change gamma p C rho (log r) t = v
      rw [gamma_radial, exp_log hr]
      exact hv.symm
  exact congrArg sInf he

/-- sec2_obstacle.tex:69–70. The omitted radial coordinates cause no loss whenw=0. -/
theorem pairObstacle_zero_right (p C : ℝ) (rho z : ℂ) :
    pairObstacle p C rho z 0 = (C ^ p - 1) * ‖z‖ ^ p := by
  simp only [pairObstacle, star_zero, add_zero, mul_zero]
  ring

/-- sec2_obstacle.tex:69–70. The second zero-product case, with exact coefficientnorm. -/
theorem pairObstacle_zero_left (p C : ℝ) (rho w : ℂ) :
    pairObstacle p C rho 0 w = (C ^ p - ‖rho‖ ^ p) * ‖w‖ ^ p := by
  simp only [pairObstacle, zero_add, norm_star, norm_mul,
    Real.mul_rpow (norm_nonneg rho) (norm_nonneg w)]
  ring

theorem pairObstacle_nonneg_zero_product {p C : ℝ} (hp : 0 < p) (rho z w : ℂ)
    (hC : max 1 ‖rho‖ < C) (hzw : z * w = 0) : 0 ≤ pairObstacle p C rho z w := by
  rcases mul_eq_zero.mp hzw with hz | hw
  · subst z
    rw [pairObstacle_zero_left]
    exact mul_nonneg (sub_nonneg.mpr
      (Real.rpow_le_rpow (norm_nonneg rho) ((le_max_right _ _).trans hC.le) hp.le))
      (Real.rpow_nonneg (norm_nonneg w) _)
  · subst w
    rw [pairObstacle_zero_right]
    have h : 1 ≤ C ^ p := by
      have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
        ((le_max_left 1 ‖rho‖).trans hC.le) hp.le
      simpa only [Real.one_rpow] using hh
    exact mul_nonneg (sub_nonneg.mpr h) (Real.rpow_nonneg (norm_nonneg z) _)

end GKSharp
