/- continuity and scaling of the actual angular potential.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.Gamma
open Real Metric Set Filter Topology MeasureTheory
namespace GKSharp.PotentialCoordinates

/-- For a `2π`-periodic `φ`: `φ(arg ζ) = φ(arg(-ζ) + π)` (`ζ ≠ 0`). -/
theorem phi_arg_neg {φ : ℝ → ℝ} (hper : Function.Periodic φ (2 * π)) {ζ : ℂ} (hζ : ζ ≠ 0) :
    φ (Complex.arg ζ) = φ (Complex.arg (-ζ) + π) := by
  have h := Complex.arg_neg_coe_angle hζ
  have h2 : ((Complex.arg (-ζ) + π : ℝ) : Real.Angle) = (Complex.arg ζ : Real.Angle) := by
    rw [Real.Angle.coe_add, h, add_assoc, Real.Angle.coe_pi_add_coe_pi, add_zero]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h2
  rw [show Complex.arg (-ζ) + π = Complex.arg ζ + k * (2 * π) by linear_combination hk]
  exact (hper.int_mul k (Complex.arg ζ)).symm

theorem continuousAt_phi_arg {φ : ℝ → ℝ} (hc : Continuous φ) (hper : Function.Periodic φ (2 * π)) {ζ0 : ℂ}
    (hζ0 : ζ0 ≠ 0) : ContinuousAt (fun ζ => φ (Complex.arg ζ)) ζ0 := by
  by_cases hsl : ζ0 ∈ Complex.slitPlane
  · exact hc.continuousAt.comp (Complex.continuousAt_arg hsl)
  · have hneg : -ζ0 ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff] at hsl ⊢
      push Not at hsl
      left
      rw [Complex.neg_re]
      rcases lt_or_eq_of_le hsl.1 with h | h
      · linarith
      · exact absurd (Complex.ext (by simp [h]) (by simp [hsl.2])) hζ0
    have hcont : ContinuousAt (fun ζ => φ (Complex.arg (-ζ) + π)) ζ0 := by
      have hin : ContinuousAt (fun ζ : ℂ => Complex.arg (-ζ) + π) ζ0 :=
        ((Complex.continuousAt_arg hneg).comp continuous_neg.continuousAt).add continuousAt_const
      exact hc.continuousAt.comp hin
    refine hcont.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hζ0] with ζ hζ
    exact (phi_arg_neg hper hζ).symm

/-- `V_φ` is continuous for continuous periodic `φ` (`q > 0`). -/
theorem angularPotential_continuous {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (hc : Continuous φ) (hper : Function.Periodic φ (2 * π)) :
    Continuous (angularPotential q φ) := by
  rw [continuous_iff_continuousAt]
  intro ζ0
  by_cases hζ0 : ζ0 = 0
  · subst hζ0
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := -π) (b := π)).exists_bound_of_continuousOn hc.continuousOn
    have hV0 : angularPotential q φ 0 = 0 := by simp [angularPotential, zero_rpow hq.ne']
    rw [ContinuousAt, hV0]
    have hbound : ∀ ζ : ℂ, ‖angularPotential q φ ζ‖ ≤ ‖ζ‖ ^ q * B := by
      intro ζ
      unfold angularPotential
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (norm_nonneg ζ) _)]
      exact mul_le_mul_of_nonneg_left (hB _ ⟨(Complex.neg_pi_lt_arg ζ).le, Complex.arg_le_pi ζ⟩)
        (rpow_nonneg (norm_nonneg ζ) _)
    have hlim : Tendsto (fun ζ : ℂ => ‖ζ‖ ^ q * B) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun ζ : ℂ => ‖ζ‖ ^ q * B) :=
        (continuous_norm.rpow_const (fun _ => Or.inr hq.le)).mul continuous_const
      simpa [zero_rpow hq.ne'] using this.tendsto 0
    exact squeeze_zero_norm hbound hlim
  · show ContinuousAt (fun ζ => ‖ζ‖ ^ q * φ (Complex.arg ζ)) ζ0
    exact ((continuous_norm.rpow_const (fun _ => Or.inr hq.le)).continuousAt).mul (continuousAt_phi_arg hc hper hζ0)

theorem angularPotential_zero {q : ℝ} (hq : 0 < q) (φ : ℝ → ℝ) : angularPotential q φ 0 = 0 := by simp [angularPotential, zero_rpow hq.ne']

/-- `V_φ` is `q`-homogeneous. -/
theorem angularPotential_homog {q : ℝ} {φ : ℝ → ℝ} (t : ℝ) (ht : 0 < t) (w : ℂ) : angularPotential q φ ((t : ℂ) * w) = t ^ q * angularPotential q φ w := by
  unfold angularPotential
  rw [Complex.arg_real_mul w ht, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
    mul_rpow ht.le (norm_nonneg w)]
  ring


/-- The actual homogeneous obstacle vanishes at the origin for every positive exponent. -/
theorem homogeneousObstacle_zero {p : ℝ} (hp : 0 < p) (C : ℝ) (rho : ℂ) :
    homogeneousObstacle p C rho 0 = 0 := by
  exact angularPotential_zero (by linarith : 0 < p / 2) (obstacle p C rho)

/-- Dilation of the actual homogeneous obstacle, for every real exponent. -/
theorem homogeneousObstacle_homogeneous (p C : ℝ) (rho : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    homogeneousObstacle p C rho ((r : ℂ) * z) = r ^ (p / 2) * homogeneousObstacle p C rho z :=
  angularPotential_homog r hr z

/-- This conditional continuity bridge does not assume or prove obstacle attainment/continuity. -/
theorem homogeneousObstacle_continuous_of_obstacle {p : ℝ} (hp : 0 < p) (C : ℝ) (rho : ℂ)
    (hobs : Continuous (obstacle p C rho)) : Continuous (homogeneousObstacle p C rho) :=
  angularPotential_continuous (by linarith : 0 < p / 2) hobs (obstacle_periodic p C rho)

end GKSharp.PotentialCoordinates

#print axioms GKSharp.PotentialCoordinates.angularPotential_continuous
#print axioms GKSharp.PotentialCoordinates.homogeneousObstacle_homogeneous
#print axioms GKSharp.PotentialCoordinates.homogeneousObstacle_continuous_of_obstacle
