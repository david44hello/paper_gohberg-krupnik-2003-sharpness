/- GKSharp/Proofs/ContactScaling.lean — actual exponential scaling of contact jets.
Frozen source: short_v0.70/sec4b_failure.tex:37; former v0.40:42.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactSpecification
import GKSharp.Proofs.ContactHarmonic
import GKSharp.Proofs.ThresholdGammaLinks

namespace GKSharp
open Threshold Set Filter
open scoped Topology

namespace ContactCalc

lemma mul {S : ℝ → ℝ → Prop} {f fy ft fyy ftt fyt g gy gt gyy gtt gyt : ℝ → ℝ → ℝ}
    (hf : SliceDerivs S f fy ft fyy ftt fyt) (hg : SliceDerivs S g gy gt gyy gtt gyt) :
    SliceDerivs S (fun y t => f y t * g y t)
      (fun y t => fy y t * g y t + f y t * gy y t)
      (fun y t => ft y t * g y t + f y t * gt y t)
      (fun y t => fyy y t * g y t + 2 * fy y t * gy y t + f y t * gyy y t)
      (fun y t => ftt y t * g y t + 2 * ft y t * gt y t + f y t * gtt y t)
      (fun y t => fyt y t * g y t + fy y t * gt y t + ft y t * gy y t + f y t * gyt y t) := by
  intro y t hyt
  obtain ⟨f1, f2, f3, f4, f5⟩ := hf y t hyt
  obtain ⟨g1, g2, g3, g4, g5⟩ := hg y t hyt
  exact ⟨f1.mul g1, f2.mul g2,
    ((f3.mul g1).add (f1.mul g3)).congr_deriv (by ring),
    ((f4.mul g2).add (f2.mul g4)).congr_deriv (by ring),
    ((f5.mul g2).add (f2.mul g5)).congr_deriv (by ring)⟩

def PositiveBases (lam y t : ℝ) : Prop := 0 < Q 1 y t ∧ 0 < Q lam y t

lemma positiveBases_open (lam : ℝ) : SliceOpen (PositiveBases lam) := by
  intro y t h
  obtain ⟨a1, a2⟩ := Q_open 1 y t h.1
  obtain ⟨b1, b2⟩ := Q_open lam y t h.2
  exact ⟨a1.and b1, a2.and b2⟩

lemma bigG_derivs_exist (p lam : ℝ) :
    ∃ fy ft fyy ftt fyt : ℝ → ℝ → ℝ,
      SliceDerivs (PositiveBases lam)
        (fun y t => bigG p (gk p lam) lam (zeta y t)) fy ft fyy ftt fyt := by
  have hc1 := mono (T := PositiveBases lam) (fun _ _ h => h.1) (chi_derivs 1)
  have hcl := mono (T := PositiveBases lam) (fun _ _ h => h.2) (chi_derivs lam)
  have heq : ∀ y t, PositiveBases lam y t →
      bigG p (gk p lam) lam (zeta y t) =
        gk p lam ^ p * Real.exp (p * chi 1 y t) + -1 * Real.exp (p * chi lam y t) := by
    intro y t h
    have h1 := norm_pos_of_Q h.1
    have hl := norm_pos_of_Q h.2
    rw [Complex.ofReal_one] at h1
    simp only [bigG, GKSharp.obstacleG, chi, Complex.ofReal_one]
    rw [add_comm (1 : ℂ), add_comm (lam : ℂ), Real.rpow_def_of_pos h1,
      Real.rpow_def_of_pos hl, mul_comm (Real.log ‖zeta y t + 1‖) p,
      mul_comm (Real.log ‖zeta y t + (lam : ℂ)‖) p]
    ring
  exact ⟨_, _, _, _, _, congr (positiveBases_open lam) heq
    (add (const_mul (gk p lam ^ p) (exp_mul p hc1)) (const_mul (-1) (exp_mul p hcl)))⟩

lemma exp_scale_derivs (qq lam : ℝ) :
    SliceDerivs (PositiveBases lam) (fun y _ => Real.exp (-qq * y))
      (fun y _ => -qq * Real.exp (-qq * y)) (fun _ _ => 0)
      (fun y _ => qq ^ 2 * Real.exp (-qq * y)) (fun _ _ => 0) (fun _ _ => 0) := by
  have hy : SliceDerivs (PositiveBases lam) (fun y _ => y)
      (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) := by
    intro y t _
    exact ⟨hasDerivAt_id y, hasDerivAt_const t y, hasDerivAt_const y 1,
      hasDerivAt_const t 0, hasDerivAt_const t 1⟩
  simpa using exp_mul (-qq) hy

end ContactCalc

open ContactCalc

/-- The three printed scaling identities, using actual canonical derivatives. -/
theorem contact_gamma_scaling_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let t := theta p
    let GG := fun y t => bigG p (gk p lam) lam (zeta y t)
    Real.exp (q p * y) * dtt (gammaGK p lam) y t = dtt GG y t ∧
    Real.exp (q p * y) * dyy (gammaGK p lam) y t = dyy GG y t ∧
    Real.exp (q p * y) * dty (gammaGK p lam) y t = dty GG y t - q p * dt GG y t := by
  dsimp only
  let yy := yContact p lam
  let tt := theta p
  let GG := fun y t => bigG p (gk p lam) lam (zeta y t)
  have hS : PositiveBases lam yy tt := by
    obtain ⟨hr, _, _, _⟩ := contact_root_properties hp hp2 hlam
    have hEy : Real.exp yy = rContact p lam := Real.exp_log (by linarith)
    have hs : 0 < sn p := Real.sin_pos_of_pos_of_lt_pi
      (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hp)
    have hh (cc : ℝ) : 0 < Q cc yy tt := by
      rw [Q_sos, hEy]
      change 0 < (rContact p lam * Real.cos tt + cc) ^ 2 + (rContact p lam * sn p) ^ 2
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (mul_pos (by linarith) hs))
    exact ⟨hh 1, hh lam⟩
  obtain ⟨fy, ft, fyy, ftt, fyt, hG⟩ := bigG_derivs_exist p lam
  have hscale := exp_scale_derivs (q p) lam
  have heq : ∀ y t, PositiveBases lam y t →
      gammaGK p lam y t = Real.exp (-q p * y) * GG y t := by
    intro y t _
    exact threshold_gamma_coordinate_bridge_proved p (gk p lam) lam y t hp
  have hGamma := ContactCalc.congr (positiveBases_open lam) heq (ContactCalc.mul hscale hG)
  obtain ⟨hgy, hgt, hgyy, hgtt, hgyt⟩ := values (positiveBases_open lam) hG hS
  obtain ⟨hy, _, hyy, htt, hyt⟩ := values (positiveBases_open lam) hGamma hS
  obtain ⟨_, _, _, _, hz, hyz, _⟩ := contact_spec_proved p lam hp hp2 hlam
  have hGzero : GG yy tt = 0 := by
    have hh := heq yy tt hS
    rw [hz] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (Real.exp_ne_zero _)
  have hfy : fy yy tt = 0 := by
    rw [hyz, hGzero, mul_zero, zero_add] at hy
    exact (mul_eq_zero.mp hy.symm).resolve_left (Real.exp_ne_zero _)
  have hprod : Real.exp (q p * yy) * Real.exp (-q p * yy) = 1 := by
    rw [← Real.exp_add, show q p * yy + -q p * yy = 0 by ring, Real.exp_zero]
  change Real.exp (q p * yy) * dtt (gammaGK p lam) yy tt = dtt GG yy tt ∧
    Real.exp (q p * yy) * dyy (gammaGK p lam) yy tt = dyy GG yy tt ∧
    Real.exp (q p * yy) * dty (gammaGK p lam) yy tt = dty GG yy tt - q p * dt GG yy tt
  rw [hyy, htt, hyt, hgyy, hgtt, hgyt, hgt, hGzero, hfy]
  constructor
  · linear_combination ftt yy tt * hprod
  constructor
  · linear_combination fyy yy tt * hprod
  · linear_combination (fyt yy tt - q p * ft yy tt) * hprod

end GKSharp

#print axioms GKSharp.contact_gamma_scaling_proved

