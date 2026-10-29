/- GKSharp/Defs/CurveK.lean - the critical-curve function K_f of Section 5 (sec5_sharp_inequality.tex l.99-100,
first form of (5.7)).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.CriticalCurve

namespace GKSharp

/-- `K_f(θ) = 2(1−λ)^p ρ^{p−2} τ |Q|^{1−q} / (2τ cos δ − 1)` on the critical curve, with `w = w(z_θ)`, `ρ = |w|`,
`τ = ρ/|v|`, `Q = Q(w)`, `δ = (1−q)θ`, `q = p/2` (sec5_sharp_inequality.tex l.99-100, (5.7) first form). -/
noncomputable def curveKf (p lam θ : ℝ) : ℝ :=
  2 * (1 - lam) ^ p * ‖mobW lam (curveZ p lam θ)‖ ^ (p - 2) *
      (‖mobW lam (curveZ p lam θ)‖ / ‖curveV p lam θ‖) *
      ‖mobQ lam (mobW lam (curveZ p lam θ))‖ ^ (1 - p / 2) /
    (2 * (‖mobW lam (curveZ p lam θ)‖ / ‖curveV p lam θ‖) * Real.cos ((1 - p / 2) * θ) - 1)

end GKSharp
