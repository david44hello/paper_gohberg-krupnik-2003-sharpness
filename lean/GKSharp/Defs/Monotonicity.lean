/- proposed definitions, frozen sec5d_monotone.tex:18-19,41-42.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.CriticalCurve

namespace GKSharp

/-- The polynomial Pi(X), sec5d:18-19. -/
noncomputable def monoPi (eps θ X : ℝ) : ℝ :=
  -(1 - eps) ^ 2 * Real.sin θ * Real.sin (eps * θ) * X ^ 2 +
    2 * eps * Real.sin ((1 - eps) * θ) * (Real.sin θ - Real.sin (eps * θ)) * X +
    (1 + eps ^ 2) * Real.sin θ * Real.sin (eps * θ) -
    2 * eps * Real.sin θ * Real.sin (eps * θ) * Real.cos ((1 - eps) * θ) -
    2 * eps * Real.sin ((1 - eps) * θ) ^ 2

/-- W(theta), sec5d:42. -/
noncomputable def monoW (eps θ : ℝ) : ℝ :=
  (1 - eps) ^ 2 * Real.sin θ * Real.sin (eps * θ) -
    eps * Real.sin ((1 - eps) * θ) ^ 2

/-- Psi_m(alpha), sec5d:41. -/
noncomputable def monoPsi (m α : ℝ) : ℝ :=
  (m ^ 2 * Real.sin α ^ 2 - Real.sin (m * α) ^ 2) / Real.sin α ^ 4

end GKSharp
