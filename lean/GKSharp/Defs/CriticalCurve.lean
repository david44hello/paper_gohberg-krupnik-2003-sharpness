/- GKSharp/Defs/CriticalCurve.lean - Section 5 objects: the Moebius quantities Q and Phi, the critical-point function
D(theta, r), its root R(theta) and the critical curve z_theta (sec5_sharp_inequality.tex l.18-53).
20261028.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.RealLine

namespace GKSharp

/-- `Q(w) = (w - λ)(1 - w̄)` (sec5_sharp_inequality.tex l.22, display (5.1)). -/
noncomputable def mobQ (lam : ℝ) (w : ℂ) : ℂ := (w - lam) * (1 - starRingEnd ℂ w)

/-- `Φ(w) = (1 - λ)^p (C^p - |w|^p) - K Re Q(w)^q`, `q = p/2` (sec5_sharp_inequality.tex l.25). -/
noncomputable def mobPhi (p C K lam : ℝ) (w : ℂ) : ℝ :=
  (1 - lam) ^ p * (C ^ p - ‖w‖ ^ p) - K * reQPow (mobQ lam w) (p / 2)

/-- `D(θ, r) = (1 + λ) r s₂ - (1 + λ r²) s₁` with `s₁ = sin((1 - q)θ)`, `s₂ = sin(qθ)`, `q = p/2`
(sec5_sharp_inequality.tex l.37, display (5.3)). -/
noncomputable def curveD (p lam θ r : ℝ) : ℝ :=
  (1 + lam) * r * Real.sin (p / 2 * θ) - (1 + lam * r ^ 2) * Real.sin ((1 - p / 2) * θ)

/-- The root formula `2a / ((1 + λ) b + √((1 + λ)² b² - 4 λ a²))` (sec5_sharp_inequality.tex l.48, with `a = s₁`,
`b = s₂`). -/
noncomputable def curveRoot (lam a b : ℝ) : ℝ :=
  2 * a / ((1 + lam) * b + Real.sqrt ((1 + lam) ^ 2 * b ^ 2 - 4 * lam * a ^ 2))

/-- `R(θ) = 2 s₁ / ((1 + λ) s₂ + √((1 + λ)² s₂² - 4 λ s₁²))` (sec5_sharp_inequality.tex l.48). -/
noncomputable def curveR (p lam θ : ℝ) : ℝ :=
  curveRoot lam (Real.sin ((1 - p / 2) * θ)) (Real.sin (p / 2 * θ))

/-- The critical curve `z_θ = R(θ) e^{-iθ}`, `0 < θ < π` (sec5_sharp_inequality.tex l.52). -/
noncomputable def curveZ (p lam θ : ℝ) : ℂ :=
  (curveR p lam θ : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)

/-- `v = e^{iδ} + λ e^{-iδ}`, `δ = (1 - q)θ`, `q = p/2` (sec5_sharp_inequality.tex l.35). -/
noncomputable def curveV (p lam θ : ℝ) : ℂ :=
  Complex.exp ((((1 - p / 2) * θ : ℝ) : ℂ) * Complex.I) +
    (lam : ℂ) * Complex.exp (-((((1 - p / 2) * θ : ℝ) : ℂ)) * Complex.I)

end GKSharp
