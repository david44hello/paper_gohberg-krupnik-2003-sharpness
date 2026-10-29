/- finite, attained and continuous actual angular obstacle.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GammaCoercive
import GKSharp.Proofs.PotentialCoordinates
open Real Set Filter Topology
namespace GKSharp

theorem gamma_min_attained {p C : ℝ} (hp : 0 < p) (rho : ℂ)
    (hC : max 1 ‖rho‖ < C) (t : ℝ) :
    ∃ y0 : ℝ, ∀ y : ℝ, gamma p C rho y0 t ≤ gamma p C rho y t := by
  have hcont : Continuous (fun y : ℝ => gamma p C rho y t) := by
    unfold gamma unitPoint
    fun_prop (disch := positivity)
  apply hcont.exists_forall_le
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  constructor
  · rw [tendsto_atBot_atTop]
    intro M
    obtain ⟨Y, hY0, hY⟩ := Coercive.gamma_uniform_coercive hp rho hC M
    refine ⟨-Y, fun y hy => hY y t ?_⟩
    linarith [neg_le_abs y]
  · rw [tendsto_atTop_atTop]
    intro M
    obtain ⟨Y, hY0, hY⟩ := Coercive.gamma_uniform_coercive hp rho hC M
    exact ⟨Y, fun y hy => hY y t (hy.trans (le_abs_self y))⟩

theorem gamma_zero_upper {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C) (rho : ℂ) (t : ℝ) :
    gamma p C rho 0 t ≤ C ^ p * (2 : ℝ) ^ p := by
  rw [gamma_radial]
  simp only [Real.exp_zero, Real.one_rpow, Complex.ofReal_one, one_mul]
  unfold obstacleG
  have hn : ‖(1 : ℂ) + unitPoint t‖ ≤ 2 := by
    simpa only [norm_one, norm_unitPoint, one_add_one_eq_two] using norm_add_le (1 : ℂ) (unitPoint t)
  have hpw := Real.rpow_le_rpow (norm_nonneg _) hn hp.le
  have hb := Real.rpow_nonneg (norm_nonneg (rho + unitPoint t)) p
  linarith [mul_le_mul_of_nonneg_left hpw (Real.rpow_nonneg hC p)]

theorem gamma_minimizers_bounded {p C : ℝ} (hp : 0 < p) (rho : ℂ) (hC : max 1 ‖rho‖ < C) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ t y0 : ℝ,
      (∀ y : ℝ, gamma p C rho y0 t ≤ gamma p C rho y t) → |y0| ≤ Y := by
  have hC0 : 0 ≤ C := (zero_le_one.trans (le_max_left 1 ‖rho‖)).trans hC.le
  obtain ⟨Y, hY0, hY⟩ := Coercive.gamma_uniform_coercive hp rho hC (C ^ p * (2 : ℝ) ^ p + 1)
  refine ⟨Y, hY0, ?_⟩
  intro t y0 hmin
  by_contra hy
  have hy' : Y ≤ |y0| := (lt_of_not_ge hy).le
  have hlower := hY y0 t hy'
  have hupper := (hmin 0).trans (gamma_zero_upper hp hC0 rho t)
  linarith

theorem obstacle_eq_min {p C : ℝ} (hp : 0 < p) (rho : ℂ) (hC : max 1 ‖rho‖ < C) (t : ℝ) :
    ∃ y0 : ℝ, (∀ y : ℝ, gamma p C rho y0 t ≤ gamma p C rho y t) ∧
      obstacle p C rho t = gamma p C rho y0 t := by
  obtain ⟨y0, hmin⟩ := gamma_min_attained hp rho hC t
  refine ⟨y0, hmin, ?_⟩
  have hleast : IsLeast (range (fun y : ℝ => gamma p C rho y t)) (gamma p C rho y0 t) := by
    refine ⟨⟨y0, rfl⟩, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hmin y
  exact hleast.csInf_eq

theorem exists_obstacle_min_compact {p C : ℝ} (hp : 0 < p) (rho : ℂ) (hC : max 1 ‖rho‖ < C) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ t : ℝ, ∃ y ∈ Icc (-Y) Y,
      (∀ v : ℝ, gamma p C rho y t ≤ gamma p C rho v t) ∧
        obstacle p C rho t = gamma p C rho y t := by
  obtain ⟨Y, hY0, hY⟩ := gamma_minimizers_bounded hp rho hC
  refine ⟨Y, hY0, fun t => ?_⟩
  obtain ⟨y, hmin, heq⟩ := obstacle_eq_min hp rho hC t
  have hy := hY t y hmin
  exact ⟨y, ⟨by linarith [neg_abs_le y], (le_abs_self y).trans hy⟩, hmin, heq⟩

theorem obstacle_bddBelow {p C : ℝ} (hp : 0 < p) (rho : ℂ) (hC : max 1 ‖rho‖ < C) (t : ℝ) :
    BddBelow (range (fun y : ℝ => gamma p C rho y t)) := by
  obtain ⟨y0, hmin⟩ := gamma_min_attained hp rho hC t
  refine ⟨gamma p C rho y0 t, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact hmin y

theorem obstacle_continuous {p C : ℝ} (hp : 0 < p) (rho : ℂ) (hC : max 1 ‖rho‖ < C) :
    Continuous (obstacle p C rho) := by
  obtain ⟨Y, hY0, hY⟩ := exists_obstacle_min_compact hp rho hC
  have heq : obstacle p C rho = fun t => sInf ((fun y => gamma p C rho y t) '' Icc (-Y) Y) := by
    funext t
    obtain ⟨y0, hy0, hmin, hm⟩ := hY t
    rw [hm]
    have hl : IsLeast ((fun y => gamma p C rho y t) '' Icc (-Y) Y) (gamma p C rho y0 t) := by
      refine ⟨⟨y0, hy0, rfl⟩, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact hmin y
    exact hl.csInf_eq.symm
  rw [heq]
  have hcont : Continuous (fun ty : ℝ × ℝ => gamma p C rho ty.2 ty.1) := by
    unfold gamma unitPoint
    fun_prop (disch := positivity)
  exact isCompact_Icc.continuous_sInf (f := fun t y : ℝ => gamma p C rho y t) hcont

/-- sec2_obstacle.tex (short v0.40):59–60. Entire corrected O12 target. -/
theorem slice_O12_proved {p : ℝ} (hp : 1 < p) (C : ℝ) (rho : ℂ) (hC : max 1 ‖rho‖ < C) :
    (∃ Y : ℝ, 0 < Y ∧ ∀ t : ℝ, ∃ y ∈ Icc (-Y) Y,
      (∀ v : ℝ, gamma p C rho y t ≤ gamma p C rho v t) ∧ obstacle p C rho t = gamma p C rho y t) ∧
    (∀ t : ℝ, BddBelow (range (fun y : ℝ => gamma p C rho y t))) ∧ Continuous (obstacle p C rho) :=
  ⟨exists_obstacle_min_compact (by linarith) rho hC,
    obstacle_bddBelow (by linarith) rho hC, obstacle_continuous (by linarith) rho hC⟩

theorem homogeneousObstacle_continuous {p C : ℝ} (hp : 0 < p) (rho : ℂ) (hC : max 1 ‖rho‖ < C) :
    Continuous (homogeneousObstacle p C rho) :=
  PotentialCoordinates.homogeneousObstacle_continuous_of_obstacle hp C rho (obstacle_continuous hp rho hC)

end GKSharp

#print axioms GKSharp.slice_O12_proved
#print axioms GKSharp.homogeneousObstacle_continuous
