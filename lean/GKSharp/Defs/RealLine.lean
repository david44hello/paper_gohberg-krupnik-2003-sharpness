/- GKSharp/Defs/RealLine.lean - objects of the real-ratio sections: Re z^q, the criterion function D_C, the closed
form of K, the Moebius map w (sec4a_criterion.tex l.6-17, sec2_obstacle.tex l.133-138, sec5_sharp_inequality.tex l.20).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.GK

namespace GKSharp

/-- `Re z^q = |z|^q cos(q arg z)` with the principal argument, and `0` at `z = 0` for `q > 0`
(sec4a_criterion.tex l.11-12). -/
noncomputable def reQPow (z : ℂ) (q : ℝ) : ℝ := ‖z‖ ^ q * Real.cos (q * Complex.arg z)

/-- `𝒟_C(z) = C^p |1 + z|^p - |1 + λ z|^p - K Re z^q`, `q = p/2` (sec4a_criterion.tex l.17, display (*)). -/
noncomputable def critD (p C K lam : ℝ) (z : ℂ) : ℝ :=
  C ^ p * ‖1 + z‖ ^ p - ‖1 + (lam : ℂ) * z‖ ^ p - K * reQPow z (p / 2)

/-- The closed form of `K` (sec2_obstacle.tex l.135-137, first form), at `C = GK_p(λ)`:
`K = 2 (1 - λ) C s₀^{p-2} c₀^{1-q} (C² + λ)^{q-1}`, `s₀ = sin(π/p)`, `c₀ = -cos(π/p)`, `q = p/2`. -/
noncomputable def kConst (p lam : ℝ) : ℝ :=
  2 * (1 - lam) * gk p lam * Real.sin (Real.pi / p) ^ (p - 2) * (-Real.cos (Real.pi / p)) ^ (1 - p / 2) *
    (gk p lam ^ 2 + lam) ^ (p / 2 - 1)

/-- The Moebius map `w = (1 + λ z)/(1 + z)` (sec5_sharp_inequality.tex l.20). -/
noncomputable def mobW (lam : ℝ) (z : ℂ) : ℂ := (1 + (lam : ℂ) * z) / (1 + z)

end GKSharp
