/- GKSharp/Proofs/ThresholdGammaLinks.lean — specialize the existing Gamma proofs.
Frozen source: short_v0.40/sec2_obstacle.tex:60–61, sec4b_failure.tex:14–15,24–26.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.ThresholdAnalysis
import GKSharp.Proofs.Gamma

namespace GKSharp

theorem threshold_gamma_even_proved (p C lam y t : ℝ) :
    Threshold.gamma p C lam y (-t) = Threshold.gamma p C lam y t :=
  gamma_even_real p C lam y t

theorem threshold_obstacle_even_proved (p lam : ℝ) :
    Function.Even (Threshold.obstacle p lam) :=
  fun t => obstacle_even_real p (gk p lam) lam t

/-- Coordinate bridge for the actual exponential parameterization, using the
already proved radial Gamma formula. No new infimum or potential definition. -/
theorem threshold_gamma_coordinate_bridge_proved (p C lam y t : ℝ) (hp : 1 < p) :
    Threshold.gamma p C lam y t = Real.exp (-Threshold.q p * y) *
      Threshold.bigG p C lam (Threshold.zeta y t) := by
  have hzeta : Threshold.zeta y t = (Real.exp y : ℂ) * unitPoint t := by
    simp [Threshold.zeta, unitPoint, Complex.exp_add, mul_comm Complex.I, ← Complex.ofReal_exp]
  unfold Threshold.gamma Threshold.bigG
  rw [hzeta, gamma_radial, ← Real.exp_mul]
  unfold Threshold.q
  congr 2
  ring

end GKSharp

#print axioms GKSharp.threshold_gamma_even_proved
#print axioms GKSharp.threshold_obstacle_even_proved
#print axioms GKSharp.threshold_gamma_coordinate_bridge_proved
