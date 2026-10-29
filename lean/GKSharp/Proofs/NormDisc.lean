/- exact O24, actual norm bound implies the continuous polynomial-disc obstacle bound.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.DiscFromPairs
import GKSharp.Proofs.PencilPairs

namespace GKSharp
variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- short v0.40/sec2_obstacle.tex:80–86; full corrected O24 for all1<p and arbitrary complex ratio. -/
theorem slice_O24_proved (hp : 1 < p) (P : RieszProjection p) (C : ℝ) (rho : ℂ)
    (hC : max 1 ‖rho‖ < C) (hbound : pencilNorm P rho ≤ C) :
    Continuous (homogeneousObstacle p C rho) ∧ homogeneousObstacle p C rho 0 = 0 ∧
      PolynomialDiscBound (homogeneousObstacle p C rho) := by
  have hp0 : 0 < p := by linarith
  have hC0 : 0 ≤ C := (zero_le_one.trans (le_max_left _ _)).trans hC.le
  exact ⟨homogeneousObstacle_continuous hp0 rho hC,
    PotentialCoordinates.homogeneousObstacle_zero hp0 C rho,
    Lift.polynomialDiscBound_of_pairBound hp0 rho hC
      ((norm_iff_polynomial_pairs hp P rho C hC0).mp hbound)⟩

end GKSharp

#print axioms GKSharp.slice_O24_proved
