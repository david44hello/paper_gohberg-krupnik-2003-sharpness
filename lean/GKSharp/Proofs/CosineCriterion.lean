/- the inversion and radial-infimum equivalence in Proposition Q.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.Sec4aBasic
import GKSharp.Proofs.Sec4aAngular
import GKSharp.Proofs.ObstacleMinimum

namespace GKSharp
open Set Threshold

lemma cosine_mul_abs (qq t : ℝ) : Real.cos (qq * |t|) = Real.cos (qq * t) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, mul_neg, Real.cos_neg]

lemma critD_inv_factor (p C KK lam : ℝ) {z : ℂ} (hz : z ≠ 0) :
    critD p C KK lam z = ‖z‖ ^ p *
      (obstacleG p C (lam : ℂ) z⁻¹ - KK * reQPow z⁻¹ (p / 2)) := by
  have hn := norm_pos_iff.mpr hz
  have hfirst : ‖1 + z‖ = ‖z‖ * ‖1 + z⁻¹‖ := by
    rw [← norm_mul]
    congr 1
    field_simp
    <;> ring
  have hsecond : ‖1 + (lam : ℂ) * z‖ = ‖z‖ * ‖(lam : ℂ) + z⁻¹‖ := by
    rw [← norm_mul]
    congr 1
    field_simp
    <;> ring
  have hcancel : ‖z‖ ^ p * ‖z‖ ^ (-p) = 1 := by
    rw [← Real.rpow_add hn, add_neg_cancel, Real.rpow_zero]
  have hinv : reQPow z⁻¹ (p / 2) = ‖z‖ ^ (-p) * reQPow z (p / 2) :=
    reQPow_inv_proved p z hz
  unfold critD obstacleG
  rw [hfirst, hsecond, Real.mul_rpow hn.le (norm_nonneg _),
    Real.mul_rpow hn.le (norm_nonneg _), hinv]
  linear_combination KK * reQPow z (p / 2) * hcancel

lemma critD_nonneg_iff_radial {p C : ℝ} (hp : 0 < p) (hC : 1 < C) (KK lam : ℝ) :
    (∀ z : ℂ, 0 ≤ critD p C KK lam z) ↔
      ∀ z : ℂ, z ≠ 0 → KK * reQPow z (p / 2) ≤ obstacleG p C (lam : ℂ) z := by
  constructor
  · intro hh z hz
    have hn : 0 < ‖z⁻¹‖ ^ p := Real.rpow_pos_of_pos (norm_pos_iff.mpr (inv_ne_zero hz)) _
    have he := hh z⁻¹
    rw [critD_inv_factor p C KK lam (inv_ne_zero hz), inv_inv] at he
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he hn)
  · intro hh z
    by_cases hz : z = 0
    · subst z
      have hpq : p / 2 ≠ 0 := by linarith
      simp only [critD, add_zero, norm_one, Real.one_rpow, mul_one, mul_zero,
        reQPow, norm_zero, Real.zero_rpow hpq, zero_mul, sub_zero]
      exact sub_nonneg.mpr (Real.one_le_rpow hC.le hp.le)
    · rw [critD_inv_factor p C KK lam hz]
      exact mul_nonneg (Real.rpow_nonneg (norm_nonneg z) p)
        (sub_nonneg.mpr (hh z⁻¹ (inv_ne_zero hz)))

lemma cosine_obstacle_iff_radial {p C : ℝ} (hp : 1 < p) {lam KK : ℝ}
    (hC : max 1 ‖(lam : ℂ)‖ < C) :
    (∀ t ∈ Icc (-Real.pi) Real.pi,
      KK * Real.cos (p / 2 * |t|) ≤ GKSharp.obstacle p C (lam : ℂ) t) ↔
      ∀ z : ℂ, z ≠ 0 → KK * reQPow z (p / 2) ≤ obstacleG p C (lam : ℂ) z := by
  constructor
  · intro hm z hz
    have hn := norm_pos_iff.mpr hz
    have ht : Complex.arg z ∈ Icc (-Real.pi) Real.pi :=
      ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
    have hle := (hm (Complex.arg z) ht).trans
      (csInf_le (obstacle_bddBelow (by linarith) (lam : ℂ) hC (Complex.arg z))
        (mem_range_self (Real.log ‖z‖)))
    rw [gamma_radial, Real.exp_log hn,
      show (‖z‖ : ℂ) * unitPoint (Complex.arg z) = z from Complex.norm_mul_exp_arg_mul_I z,
      cosine_mul_abs] at hle
    have hh := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hn.le (p / 2))
    have hcancel : ‖z‖ ^ (p / 2) * ‖z‖ ^ (-(p / 2)) = 1 := by
      rw [← Real.rpow_add hn, add_neg_cancel, Real.rpow_zero]
    rw [← mul_assoc _ _ (obstacleG p C (lam : ℂ) z), hcancel, one_mul] at hh
    simpa only [reQPow, mul_assoc, mul_left_comm] using hh
  · intro hh t ht
    apply le_csInf (range_nonempty _)
    rintro _ ⟨y, rfl⟩
    have hr := Real.exp_pos y
    have hz : (Real.exp y : ℂ) * unitPoint t ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Complex.exp_ne_zero _)
    have h := hh ((Real.exp y : ℂ) * unitPoint t) hz
    have hnorm : ‖(Real.exp y : ℂ) * unitPoint t‖ = Real.exp y := by
      rw [norm_mul, norm_unitPoint, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hcos : Real.cos (p / 2 * Complex.arg (unitPoint t)) = Real.cos (p / 2 * |t|) := by
      change Real.cos (p / 2 * Complex.arg (Complex.exp ((t : ℂ) * Complex.I))) = _
      rw [mul_comm (t : ℂ) Complex.I, sec4a_cos_arg_exp, ← Real.cos_abs t,
        Real.arccos_cos (abs_nonneg t) (abs_le.mpr ht)]
    rw [reQPow, hnorm, Complex.arg_real_mul _ hr, hcos] at h
    have hc : (Real.exp y) ^ (-(p / 2)) * (Real.exp y) ^ (p / 2) = 1 := by
      rw [← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero]
    change KK * Real.cos (p / 2 * |t|) ≤ GKSharp.gamma p C (lam : ℂ) y t
    rw [gamma_radial]
    have hmul := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hr.le (-(p / 2)))
    calc KK * Real.cos (p / 2 * |t|) =
        (Real.exp y) ^ (-(p / 2)) * (KK * ((Real.exp y) ^ (p / 2) * Real.cos (p / 2 * |t|))) := by
          linear_combination -KK * Real.cos (p / 2 * |t|) * hc
      _ ≤ _ := hmul

/-- Full approved algebraic equivalence from sec4a_criterion.tex:16–21. -/
theorem obstacle_cos_iff_critD_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) :
    (∀ t ∈ Icc (-Real.pi) Real.pi,
      kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t) ↔
    (∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) := by
  have hC : max 1 ‖(lam : ℂ)‖ < gk p lam := gk_gt_max hp (ne_of_lt hp2) (by
    intro heq
    have : lam = 1 := by exact_mod_cast heq
    linarith [hlam.2])
  exact (cosine_obstacle_iff_radial hp hC).trans
    (critD_nonneg_iff_radial (by linarith) ((le_max_left _ _).trans_lt hC) (kConst p lam) lam).symm

end GKSharp

#print axioms GKSharp.obstacle_cos_iff_critD_proved

