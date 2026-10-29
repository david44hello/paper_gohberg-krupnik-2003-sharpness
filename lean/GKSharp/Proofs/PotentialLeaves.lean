/- source-facing Gamma/K/endpoint bundles.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GammaDerivative
import GKSharp.Proofs.ContactK
import GKSharp.Proofs.EndpointElementary

namespace GKSharp
open Real

/-- sec2_obstacle.tex (short v0.40):51–55; both squared bases and exact pair factorization. -/
theorem slice_O09_proved {p : ℝ} (hp : 1 < p) (C : ℝ) (ρ z w : ℂ) (hzw : z * w ≠ 0) :
    let y := log (‖z‖ / ‖w‖)
    let t := Complex.arg (z * w)
    ‖z + star w‖ ^ 2 = ‖z * w‖ * (2 * cosh y + 2 * cos t) ∧
    ‖z + ρ * star w‖ ^ 2 = ‖z * w‖ *
      (exp y + ‖ρ‖ ^ 2 * exp (-y) + 2 * (star ρ * unitPoint t).re) ∧
    pairObstacle p C ρ z w = ‖z * w‖ ^ (p / 2) * gamma p C ρ y t := by
  exact ⟨(pair_squared_bases ρ z w hzw).1, (pair_squared_bases ρ z w hzw).2, pair_gamma_factor p C ρ z w hzw⟩

/-- sec2_obstacle.tex (short v0.40):60; real ratio gives an even obstacle. -/
theorem slice_O13_proved (p C lam t : ℝ) : obstacle p C (lam : ℂ) (-t) = obstacle p C (lam : ℂ) t := by
  exact obstacle_even_real p C lam t

/-- sec2_obstacle.tex (short v0.40):60–61; radial expression and actual infimum. -/
theorem slice_O14_proved (p C : ℝ) (ρ : ℂ) (y t : ℝ) :
    gamma p C ρ y t = (exp y) ^ (-(p / 2)) * obstacleG p C ρ ((exp y : ℂ) * unitPoint t) ∧
    obstacle p C ρ t = sInf {v : ℝ | ∃ r : ℝ, 0 < r ∧
      v = r ^ (-(p / 2)) * obstacleG p C ρ ((r : ℂ) * unitPoint t)} := by
  exact ⟨gamma_radial p C ρ y t, obstacle_radial p C ρ t⟩

/-- sec2_obstacle.tex (short v0.40):144–152; K closed form and positive-base derivative. -/
theorem slice_O36_proved {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (lam : ℝ) (hlam : -1 ≤ lam ∧ lam < 1) :
    let C := gk p (lam : ℂ)
    kConst p lam = 2 * (1 - lam) ^ p * C ^ p * (C ^ 2 + lam) ^ (p / 2 - 1) /
      (sin (Real.pi / p) * |cos (Real.pi / p)| ^ (p / 2 - 1) * (C ^ 2 - lam) ^ (p - 1)) ∧
    (∀ y t : ℝ, 0 < 2 * cosh y + 2 * cos t →
      0 < exp y + lam ^ 2 * exp (-y) + 2 * lam * cos t →
      deriv (gamma p C (lam : ℂ) y) t =
        -2 * (p / 2) * sin t *
          (C ^ p * (2 * cosh y + 2 * cos t) ^ (p / 2 - 1) -
            lam * (exp y + lam ^ 2 * exp (-y) + 2 * lam * cos t) ^ (p / 2 - 1))) := by
  have hK := contactK_closed_forms hp hp2 hlam.2
  rw [contactK_eq_kConst hp hp2] at hK
  exact ⟨hK, fun y t hA hB => gamma_derivative_real p (gk p (lam : ℂ)) lam y t hA hB⟩

/-- sec2_obstacle.tex (short v0.40):153; projection endpoint K simplification. -/
theorem slice_O37_proved {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    kConst p 0 = 2 * |cos (Real.pi / p)| ^ (1 - p / 2) / sin (Real.pi / p) := by
  rw [← contactK_eq_kConst hp hp2 0]
  exact contactK_zero hp hp2

/-- endpoint_estimate.tex:8,14; full angular range and inversion. -/
theorem slice_E02_proved {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    0 < endpointA p ∧ endpointA p < 3.2 * 10 ^ (-6 : ℤ) ∧
      p = Real.pi / (Real.pi - endpointA p) := by
  exact endpoint_a_range hp hp1

/-- endpoint_estimate.tex:19–22; four enclosure ingredients. -/
theorem slice_E05_proved {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    a ^ 2 * (1 - a ^ 2 / 3) ≤ sin a ^ 2 ∧
    Real.pi / (4 * a) - 2 ≤ p * Real.pi / (4 * a) - 1 - cos a ^ 2 ∧
    (cos a) ^ (-4 : ℤ) ≤ 1 + 3 * a ^ 2 ∧
    (1 + a / 3) * (1 + 3 * a ^ 2) ≤ 1 + a := by
  exact endpoint_enclosure_ingredients hp hp1

end GKSharp
