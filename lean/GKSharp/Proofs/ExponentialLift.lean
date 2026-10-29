/- exponential lift and polynomial approximation for the actual complex obstacle.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ObstacleMinimum
import GKSharp.Proofs.PolynomialPairs
import GKSharp.Proofs.Select
import GKSharp.Proofs.DiscRescale

open Real Set Filter Topology
namespace GKSharp.Lift

theorem continuous_pairObstacle {p : ℝ} (hp : 0 < p) (C : ℝ) (rho : ℂ) :
    Continuous (fun x : ℂ × ℂ => pairObstacle p C rho x.1 x.2) := by
  unfold pairObstacle
  fun_prop (disch := positivity)

noncomputable def expPartial (N : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N, x ^ k / (k.factorial : ℂ)

theorem tendsto_expPartial (x : ℂ) :
    Tendsto (fun N => expPartial N x) atTop (𝓝 (Complex.exp x)) := by
  unfold expPartial
  rw [Complex.exp_eq_exp_ℂ]
  exact (NormedSpace.expSeries_div_hasSum_exp x).tendsto_sum_nat

theorem norm_expPartial_le (N : ℕ) (x : ℂ) : ‖expPartial N x‖ ≤ Real.exp ‖x‖ := by
  unfold expPartial
  calc ‖∑ k ∈ Finset.range N, x ^ k / (k.factorial : ℂ)‖
      ≤ ∑ k ∈ Finset.range N, ‖x‖ ^ k / (k.factorial : ℝ) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_div, norm_pow, Complex.norm_natCast]
    _ ≤ Real.exp ‖x‖ := Real.sum_le_exp_of_nonneg (norm_nonneg x) N

noncomputable def expPoly (N : ℕ) (a : ℂ) (Y : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range N, Polynomial.C (1 / (k.factorial : ℂ)) * (Polynomial.C a * Y) ^ k

theorem eval_expPoly (N : ℕ) (a : ℂ) (Y : Polynomial ℂ) (z : ℂ) :
    (expPoly N a Y).eval z = expPartial N (a * Y.eval z) := by
  unfold expPoly expPartial
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem unitPoint_ne_zero (t : ℝ) : unitPoint t ≠ 0 := Complex.exp_ne_zero _

/-- Actual complex-ratio factorization of the exponential pair, with no p<2 or real-ratio assumption. -/
theorem pair_lift (p C : ℝ) (rho : ℂ) {g g1 : Polynomial ℂ}
    (hg : ∀ z, g.eval z = z * g1.eval z) (y : ℂ) {t : ℝ}
    (hne : g.eval (unitPoint t) ≠ 0) :
    pairObstacle p C rho
      (g1.eval (unitPoint t) * Complex.exp (1 / 2 * y))
      (unitPoint t * Complex.exp (-1 / 2 * y)) =
      ‖g.eval (unitPoint t)‖ ^ (p / 2) *
        gamma p C rho (y.re + log ‖g.eval (unitPoint t)‖)
          (Complex.arg (g.eval (unitPoint t))) := by
  set e := unitPoint t with he_def
  have he : ‖e‖ = 1 := norm_unitPoint t
  have hexp : Complex.exp (1 / 2 * y) * Complex.exp (-1 / 2 * y) = 1 := by
    rw [← Complex.exp_add, show 1 / 2 * y + -1 / 2 * y = 0 by ring, Complex.exp_zero]
  have hprod : g1.eval e * Complex.exp (1 / 2 * y) *
      (e * Complex.exp (-1 / 2 * y)) = g.eval e := by
    rw [hg]
    linear_combination (g1.eval e * e) * hexp
  have hng : ‖g.eval e‖ = ‖g1.eval e‖ := by rw [hg, norm_mul, he, one_mul]
  have hre1 : (1 / 2 * y).re = y.re / 2 := by simp [Complex.mul_re]; ring
  have hre2 : (-1 / 2 * y).re = -(y.re / 2) := by simp [Complex.mul_re]; ring
  have hratio : ‖g1.eval e * Complex.exp (1 / 2 * y)‖ /
      ‖e * Complex.exp (-1 / 2 * y)‖ = ‖g.eval e‖ * Real.exp y.re := by
    rw [norm_mul, norm_mul, he, one_mul, Complex.norm_exp, Complex.norm_exp,
      hre1, hre2, hng, mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring
  rw [pair_gamma_factor p C rho _ _ (by rw [hprod]; exact hne), hprod, hratio,
    Real.log_mul (norm_ne_zero_iff.mpr hne) (Real.exp_pos _).ne', Real.log_exp,
    add_comm (log _)]

theorem re_eval_toZ_add_toW (c : ℤ →₀ ℂ) (t : ℝ) :
    ((toZ c + toW c).eval (unitPoint t)).re = (trig c t).re := by
  change ((toZ c + toW c).eval (unitPt t)).re = _
  rw [Polynomial.eval_add, eval_toZ, eval_toW, trig_eq_add,
    Complex.add_re, Complex.add_re, Complex.conj_re]

/-- The actual polynomial-pair inequality passes to every exponential pair by kernel-proved dominated convergence. -/
theorem exponential_pair_bound {p C : ℝ} (hp : 0 < p) (rho : ℂ)
    (hPair : PolynomialPairBound p C rho) (g1 Y : Polynomial ℂ) :
    0 ≤ ∫ t in (0 : ℝ)..(2 * π), pairObstacle p C rho
      (g1.eval (unitPoint t) * Complex.exp (1 / 2 * Y.eval (unitPoint t)))
      (unitPoint t * Complex.exp (-1 / 2 * Y.eval (unitPoint t))) := by
  let zN : ℕ → Polynomial ℂ := fun N => g1 * expPoly N (1 / 2) Y
  let wN : ℕ → Polynomial ℂ := fun N => Polynomial.X * expPoly N (-1 / 2) Y
  let zf : ℝ → ℂ := fun t => g1.eval (unitPoint t) * Complex.exp (1 / 2 * Y.eval (unitPoint t))
  let wf : ℝ → ℂ := fun t => unitPoint t * Complex.exp (-1 / 2 * Y.eval (unitPoint t))
  have hevz : ∀ N t, (zN N).eval (unitPoint t) =
      g1.eval (unitPoint t) * expPartial N (1 / 2 * Y.eval (unitPoint t)) := by
    intro N t
    simp only [zN, Polynomial.eval_mul, eval_expPoly]
  have hevw : ∀ N t, (wN N).eval (unitPoint t) =
      unitPoint t * expPartial N (-1 / 2 * Y.eval (unitPoint t)) := by
    intro N t
    simp only [wN, Polynomial.eval_mul, Polynomial.eval_X, eval_expPoly]
  have hw0 : ∀ N, (wN N).eval 0 = 0 := by
    intro N
    simp [wN]
  have hD : ∀ N, 0 ≤ ∫ t in (0 : ℝ)..(2 * π),
      pairObstacle p C rho ((zN N).eval (unitPoint t)) ((wN N).eval (unitPoint t)) :=
    fun N => hPair (zN N) (wN N) (hw0 N)
  have hYc : Continuous fun t => Y.eval (unitPoint t) :=
    (Polynomial.continuous Y).comp DiscRescale.continuous_unitPoint'
  have hg1c : Continuous fun t => g1.eval (unitPoint t) :=
    (Polynomial.continuous g1).comp DiscRescale.continuous_unitPoint'
  obtain ⟨BY, hBY⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hYc.continuousOn
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hg1c.continuousOn
  let K := (|B1| + 1) * Real.exp |BY|
  obtain ⟨Bd, hBd⟩ := ((isCompact_closedBall (0 : ℂ) K).prod
    (isCompact_closedBall (0 : ℂ) K)).exists_bound_of_continuousOn
      (continuous_pairObstacle hp C rho).continuousOn
  have hhalf : ∀ N : ℕ, ∀ t ∈ Icc (0 : ℝ) (2 * π), ∀ a : ℂ, ‖a‖ ≤ 1 →
      ‖expPartial N (a * Y.eval (unitPoint t))‖ ≤ Real.exp |BY| := by
    intro N t ht a ha
    refine (norm_expPartial_le _ _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul]
    calc ‖a‖ * ‖Y.eval (unitPoint t)‖ ≤ 1 * |BY| :=
        mul_le_mul ha ((hBY t ht).trans (le_abs_self _)) (norm_nonneg _) zero_le_one
      _ = |BY| := one_mul _
  have hn12 : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
  have hn12' : ‖(-1 / 2 : ℂ)‖ ≤ 1 := by norm_num
  have htend : Tendsto (fun N => ∫ t in (0 : ℝ)..(2 * π),
      pairObstacle p C rho ((zN N).eval (unitPoint t)) ((wN N).eval (unitPoint t)))
      atTop (𝓝 (∫ t in (0 : ℝ)..(2 * π), pairObstacle p C rho (zf t) (wf t))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => Bd) ?_ ?_
      intervalIntegrable_const ?_
    · refine Eventually.of_forall fun N => ?_
      exact ((continuous_pairObstacle hp C rho).comp
        (((Polynomial.continuous _).comp DiscRescale.continuous_unitPoint').prodMk
          ((Polynomial.continuous _).comp DiscRescale.continuous_unitPoint'))).aestronglyMeasurable
    · refine Eventually.of_forall fun N => Eventually.of_forall fun t ht => ?_
      have ht' : t ∈ Icc (0 : ℝ) (2 * π) := by
        rw [uIoc_of_le (by positivity)] at ht
        exact ⟨ht.1.le, ht.2⟩
      refine hBd ⟨(zN N).eval (unitPoint t), (wN N).eval (unitPoint t)⟩ ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, hevz, norm_mul]
        exact mul_le_mul ((hB1 t ht').trans (by linarith [le_abs_self B1]))
          (hhalf N t ht' _ hn12) (norm_nonneg _) (by positivity)
      · rw [Metric.mem_closedBall, dist_zero_right, hevw, norm_mul, norm_unitPoint, one_mul]
        exact (hhalf N t ht' _ hn12').trans
          (by dsimp [K]; nlinarith [Real.exp_pos |BY|, abs_nonneg B1])
    · refine Eventually.of_forall fun t _ => ?_
      simp only [hevz, hevw, zf, wf]
      have hzt := (tendsto_expPartial (1 / 2 * Y.eval (unitPoint t))).const_mul (g1.eval (unitPoint t))
      have hwt := (tendsto_expPartial (-1 / 2 * Y.eval (unitPoint t))).const_mul (unitPoint t)
      have hGt := ((continuous_pairObstacle hp C rho).continuousAt
        (x := (g1.eval (unitPoint t) * Complex.exp (1 / 2 * Y.eval (unitPoint t)),
          unitPoint t * Complex.exp (-1 / 2 * Y.eval (unitPoint t))))).tendsto.comp (hzt.prodMk_nhds hwt)
      simpa only [Function.comp_def] using hGt
  exact ge_of_tendsto htend (Eventually.of_forall hD)

end GKSharp.Lift

#print axioms GKSharp.Lift.pair_lift
#print axioms GKSharp.Lift.exponential_pair_bound
