/- contact coefficient: source-exact closed forms and projection endpoint.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.KConst
import GKSharp.Proofs.EndpointBridge

namespace GKSharp
open Real

theorem sin_theta_positive {p : ℝ} (hp : 1 < p) : 0 < sin (Real.pi / p) := by
  have hp0 : 0 < p := by linarith
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  rw [div_lt_iff₀ hp0]
  nlinarith [Real.pi_pos]

theorem cos_theta_negative {p : ℝ} (hp : 1 < p) (hp2 : p < 2) : cos (Real.pi / p) < 0 := by
  have hp0 : 0 < p := by linarith
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · rw [lt_div_iff₀ hp0]
    nlinarith [Real.pi_pos]
  · have h : Real.pi / p < Real.pi := by
      rw [div_lt_iff₀ hp0]
      nlinarith [Real.pi_pos]
    linarith [Real.pi_pos]

/-- sec2_obstacle.tex:135–137. Both exact closed forms ofK agree with the actual matrix GK. -/
theorem contactK_closed_forms {p lam : ℝ} (hp : 1 < p) (hp2 : p < 2) (hlam : lam < 1) :
    contactK p lam =
      2 * (1 - lam) ^ p * gk p lam ^ p * (gk p lam ^ 2 + lam) ^ (p / 2 - 1) /
        (sin (Real.pi / p) * |cos (Real.pi / p)| ^ (p / 2 - 1) * (gk p lam ^ 2 - lam) ^ (p - 1)) := by
  rw [contactK_eq_kConst hp hp2, abs_of_neg (cos_theta_negative hp hp2)]
  exact eq_K_forms hp hp2 hlam

/-- sec2_obstacle.tex:144. The exact projection endpoint ofK (internal algebra, no new cited inequality). -/
theorem contactK_zero {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    contactK p 0 = 2 * |cos (Real.pi / p)| ^ (1 - p / 2) / sin (Real.pi / p) := by
  have hs : 0 < sin (Real.pi / p) := sin_theta_positive hp
  have hC : 0 < 1 / sin (Real.pi / p) := by positivity
  have hpow : ((1 / sin (Real.pi / p)) ^ 2) ^ (p / 2 - 1) =
      (1 / sin (Real.pi / p)) ^ (p - 2) := by
    rw [← Real.rpow_natCast_mul hC.le]
    congr 1
    ring
  have hprod : (1 / sin (Real.pi / p)) ^ (p - 2) * sin (Real.pi / p) ^ (p - 2) = 1 := by
    rw [← Real.mul_rpow hC.le hs.le, one_div_mul_cancel hs.ne', Real.one_rpow]
  simp only [contactK, Complex.ofReal_zero, gk_zero p hp, sub_zero, mul_one, add_zero]
  rw [hpow]
  calc
    _ = (2 * |cos (Real.pi / p)| ^ (1 - p / 2) / sin (Real.pi / p)) *
        ((1 / sin (Real.pi / p)) ^ (p - 2) * sin (Real.pi / p) ^ (p - 2)) := by ring
    _ = _ := by rw [hprod, mul_one]

end GKSharp
