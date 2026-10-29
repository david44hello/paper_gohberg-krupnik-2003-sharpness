/- actual polynomial-disc bound from actual polynomial-pair bound.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ExponentialLift

open Real Set Filter Topology
namespace GKSharp.Lift

/-- On a root-free boundary, select the actual attained Gamma minima and lift them by a polynomial exponential. -/
theorem disc_bound_nozero {p C : ℝ} (hp : 0 < p) (rho : ℂ)
    (hC : max 1 ‖rho‖ < C) (hPair : PolynomialPairBound p C rho)
    (g g1 : Polynomial ℂ) (hg : ∀ z, g.eval z = z * g1.eval z)
    (hnz : ∀ t : ℝ, g.eval (unitPoint t) ≠ 0) :
    0 ≤ ∫ t in (0 : ℝ)..(2 * π), homogeneousObstacle p C rho (g.eval (unitPoint t)) := by
  by_contra hnonneg
  have hneg : (∫ t in (0 : ℝ)..(2 * π), homogeneousObstacle p C rho (g.eval (unitPoint t))) < 0 :=
    lt_of_not_ge hnonneg
  have hgc : Continuous fun t => g.eval (unitPoint t) :=
    (Polynomial.continuous g).comp DiscRescale.continuous_unitPoint'
  have hlogc : Continuous fun t => Real.log ‖g.eval (unitPoint t)‖ :=
    hgc.norm.log fun t => norm_ne_zero_iff.mpr (hnz t)
  obtain ⟨Lb, hLb⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hlogc.continuousOn
  obtain ⟨R0, hR0pos, hR0⟩ := exists_obstacle_min_compact hp rho hC
  let F : ℝ → ℝ → ℝ := fun t v => pairObstacle p C rho
    (g1.eval (unitPoint t) * Complex.exp (1 / 2 * (v : ℂ)))
    (unitPoint t * Complex.exp (-1 / 2 * (v : ℂ)))
  have hFc : Continuous (Function.uncurry F) := by
    dsimp [F, Function.uncurry, pairObstacle, unitPoint]
    fun_prop (disch := positivity)
  let mu : ℝ → ℝ := fun t => homogeneousObstacle p C rho (g.eval (unitPoint t))
  have hmuc : Continuous mu := (homogeneousObstacle_continuous hp rho hC).comp hgc
  have hFrep : ∀ t v, F t v = ‖g.eval (unitPoint t)‖ ^ (p / 2) *
      gamma p C rho (v + log ‖g.eval (unitPoint t)‖) (Complex.arg (g.eval (unitPoint t))) := by
    intro t v
    exact pair_lift p C rho hg (v : ℂ) (hnz t)
  have hmin : ∀ t ∈ Icc (0 : ℝ) (2 * π), ∃ v ∈ Icc (-(R0 + Lb)) (R0 + Lb), F t v = mu t := by
    intro t ht
    obtain ⟨y0, hy0, _, heq⟩ := hR0 (Complex.arg (g.eval (unitPoint t)))
    have hL := abs_le.mp (by simpa only [Real.norm_eq_abs] using hLb t ht)
    refine ⟨y0 - log ‖g.eval (unitPoint t)‖, ⟨by linarith [hy0.1], by linarith [hy0.2]⟩, ?_⟩
    rw [hFrep, sub_add_cancel]
    change _ = ‖g.eval (unitPoint t)‖ ^ (p / 2) * obstacle p C rho (Complex.arg (g.eval (unitPoint t)))
    rw [heq]
  have hle : ∀ t ∈ Icc (0 : ℝ) (2 * π), ∀ v : ℝ, mu t ≤ F t v := by
    intro t _ v
    obtain ⟨y0, _, hall, heq⟩ := hR0 (Complex.arg (g.eval (unitPoint t)))
    rw [hFrep]
    change ‖g.eval (unitPoint t)‖ ^ (p / 2) * obstacle p C rho (Complex.arg (g.eval (unitPoint t))) ≤ _
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hall _) (by positivity)
  have hnegmu : (∫ t in (0 : ℝ)..(2 * π), mu t) < 0 := hneg
  obtain ⟨c, hc⟩ := exists_trig_near_min F hFc mu hmuc (R0 + Lb) hmin hle
    (-(∫ t in (0 : ℝ)..(2 * π), mu t) / 2) (by linarith)
  let Y := toZ c + toW c
  have hbound := exponential_pair_bound hp rho hPair g1 Y
  have hlift : ∀ t : ℝ, pairObstacle p C rho
      (g1.eval (unitPoint t) * Complex.exp (1 / 2 * Y.eval (unitPoint t)))
      (unitPoint t * Complex.exp (-1 / 2 * Y.eval (unitPoint t))) = F t (trig c t).re := by
    intro t
    rw [pair_lift p C rho hg _ (hnz t), hFrep]
    rw [show (Y.eval (unitPoint t)).re = (trig c t).re from re_eval_toZ_add_toW c t]
  simp_rw [hlift] at hbound
  linarith

/-- Full polynomial-disc inequality for the actual complex-ratio homogeneous obstacle.
No restriction p<2 and no evenness or real-ratio assumption is used. -/
theorem polynomialDiscBound_of_pairBound {p C : ℝ} (hp : 0 < p) (rho : ℂ)
    (hC : max 1 ‖rho‖ < C) (hPair : PolynomialPairBound p C rho) :
    PolynomialDiscBound (homogeneousObstacle p C rho) := by
  intro g hg0
  by_contra hnonneg
  have hneg : (∫ t in (0 : ℝ)..(2 * π), homogeneousObstacle p C rho (g.eval (unitPoint t))) < 0 :=
    lt_of_not_ge hnonneg
  obtain ⟨r, _, _, hnz, hneg_r⟩ := disc_rescale (homogeneousObstacle p C rho)
    (homogeneousObstacle_continuous hp rho hC) (PotentialCoordinates.homogeneousObstacle_zero hp C rho) g hneg
  let gr := g.comp (Polynomial.C (r : ℂ) * Polynomial.X)
  have hgr : ∀ z, gr.eval z = g.eval ((r : ℂ) * z) := by
    intro z
    simp only [gr, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hgr0 : gr.IsRoot 0 := by
    show gr.eval 0 = 0
    rw [hgr, mul_zero, hg0]
  let g1 := gr /ₘ (Polynomial.X - Polynomial.C 0)
  have hfac : (Polynomial.X - Polynomial.C 0) * g1 = gr :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hgr0
  have hg : ∀ z, gr.eval z = z * g1.eval z := by
    intro z
    rw [← hfac, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_zero]
  have hbound := disc_bound_nozero hp rho hC hPair gr g1 hg (fun t => by rw [hgr]; exact hnz t)
  simp_rw [hgr] at hbound
  linarith

end GKSharp.Lift

#print axioms GKSharp.Lift.disc_bound_nozero
#print axioms GKSharp.Lift.polynomialDiscBound_of_pairBound
