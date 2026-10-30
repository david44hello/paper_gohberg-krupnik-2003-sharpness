/- GKSharp/Defs/GK.lean - the Gohberg-Krupnik constant (P019_paper.tex l.55, sec2_obstacle.tex l.18-43).
Copyright (C) Dave Goel 2026--now. -/
import Mathlib

namespace GKSharp

open scoped Matrix.Norms.L2Operator

/-- The matrix `[[α, (β - α) cot(π/p)], [0, β]]` of P019_paper.tex l.55. -/
noncomputable def gkMatrix (p : ℝ) (α β : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![α, (β - α) * (Real.cot (Real.pi / p) : ℂ); 0, β]

/-- `GK_p(α, β)`: the `ℓ² → ℓ²` operator norm of `gkMatrix p α β` (l.16). -/
noncomputable def gkPair (p : ℝ) (α β : ℂ) : ℝ := ‖gkMatrix p α β‖

/-- `GK_p(ρ) := GK_p(1, ρ)` (l.17). -/
noncomputable def gk (p : ℝ) (ρ : ℂ) : ℝ := gkPair p 1 ρ

/-- The middle coefficient `1 + |ρ|² + |1 - ρ|² cot²(π/p)` of eq:GK (l.23). -/
noncomputable def gkMid (p : ℝ) (ρ : ℂ) : ℝ :=
  1 + ‖ρ‖ ^ 2 + ‖1 - ρ‖ ^ 2 * Real.cot (Real.pi / p) ^ 2

/-- The quadratic of eq:GK (l.23): `X² - gkMid p ρ · X + |ρ|²`. -/
noncomputable def gkQuad (p : ℝ) (ρ : ℂ) (X : ℝ) : ℝ := X ^ 2 - gkMid p ρ * X + ‖ρ‖ ^ 2

end GKSharp
