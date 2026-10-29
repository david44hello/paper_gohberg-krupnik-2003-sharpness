/- the one canonical Section5 polar-circle profile.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.RealLine
import GKSharp.Defs.CriticalCurve

namespace GKSharp

/-- The actual polar-circle function f_rho, shared by the Section5 derivative and endpoint rows. -/
noncomputable abbrev fRho (p lam rho phi : ℝ) : ℝ :=
  reQPow (mobQ lam ((rho : ℂ) * Complex.exp ((phi : ℂ) * Complex.I))) (p / 2)

end GKSharp
