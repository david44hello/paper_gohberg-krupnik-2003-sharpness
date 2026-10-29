/- Section 5.4 coordinate and series definitions for exact coverage.
All mathematical properties are separate theorem rows; these definitions assume none.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Monotonicity
import GKSharp.Defs.CurveK

open scoped BigOperators
namespace GKSharp

noncomputable def curveGamma (p lam θ : ℝ) : ℝ :=
  Real.arctan (Real.tan ((p - 1) * (θ / 2)) * (1 + curveR p lam θ) / (1 - curveR p lam θ))

noncomputable def monoLogL (p a g : ℝ) : ℝ :=
  (1 - p / 2) * Real.log (Real.sin (g - (p - 1) * a)) +
    p / 2 * Real.log (Real.sin (g + (p - 1) * a)) +
    (p - 1) * Real.log (Real.sin (2 * a)) -
    (p - 1) * Real.log (Real.sin (g + a)) - Real.log (Real.sin (2 * ((p - 1) * a)))

noncomputable def monoLogM (p a g : ℝ) : ℝ :=
  Real.log |Real.sin (g - a)| + Real.log (Real.sin (g + (p - 1) * a)) -
    Real.log (Real.sin (g + a)) - Real.log (Real.sin (g - (p - 1) * a))

noncomputable def monoS (p a g : ℝ) : ℝ :=
  Real.sin (g - a) * Real.sin (g + a) *
    Real.sin (g - (p - 1) * a) * Real.sin (g + (p - 1) * a)

noncomputable def monoE (p a g : ℝ) : ℝ :=
  deriv (fun x => monoLogL p x g) a * deriv (monoLogM p a) g -
    deriv (monoLogL p a) g * deriv (fun x => monoLogM p x g) a

noncomputable def monoSignDenominator (p θ X : ℝ) : ℝ :=
  2 * Real.sin θ * Real.sin ((p - 1) * θ) * Real.sin ((1 - p / 2) * θ) *
    (Real.cos ((1 - p / 2) * θ) - X * Real.cos (p / 2 * θ))

noncomputable def monoSigma (p θ g : ℝ) : ℝ :=
  Real.sqrt (1 - Real.cos (2 * g) ^ 2) * Real.sin ((1 - p / 2) * θ)

noncomputable def monoNu (p θ g : ℝ) : ℝ :=
  Real.cos (p / 2 * θ) - Real.cos (2 * g) * Real.cos ((1 - p / 2) * θ)

noncomputable def monoPiPrefactor (p θ g : ℝ) : ℝ :=
  monoSigma p θ g ^ 2 * Real.cot ((1 - p / 2) * θ) ^ 2 /
    Real.cos ((1 - p / 2) * θ) ^ 2

noncomputable def monoLogRatio (eps θ : ℝ) : ℝ :=
  Real.log (eps * Real.sin ((1 - eps) * θ) ^ 2 /
    ((1 - eps) ^ 2 * Real.sin θ * Real.sin (eps * θ)))

noncomputable def monoDoubleTerm (eps θ : ℝ) (n k : ℕ) : ℝ :=
  (θ / (((n : ℝ) + 1) * Real.pi)) ^ (2 * (k + 1)) / ((k : ℝ) + 1) *
    (1 + eps ^ (2 * (k + 1)) - 2 * (1 - eps) ^ (2 * (k + 1)))

noncomputable def monoY (m t : ℝ) : ℝ := Real.cos (2 * m * Real.arcsin (Real.sqrt t))

noncomputable def monoCoeffA (m : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ((n : ℝ) ^ 2 - m ^ 2) / (((n : ℝ) + 1) * ((n : ℝ) + 1 / 2)) * monoCoeffA m n

noncomputable def monoSinCoeff (m : ℝ) (n : ℕ) : ℝ :=
  2 ^ (2 * n - 1) * m ^ 2 * (∏ j ∈ Finset.Icc 1 (n - 1), ((j : ℝ) ^ 2 - m ^ 2)) /
    (Nat.factorial (2 * n) : ℝ)

noncomputable def monoBeta (m : ℝ) (n : ℕ) : ℝ :=
  2 ^ (2 * n + 3) * m ^ 2 * (m ^ 2 - 1) *
    (∏ j ∈ Finset.Icc 2 (n + 1), ((j : ℝ) ^ 2 - m ^ 2)) / (Nat.factorial (2 * n + 4) : ℝ)

end GKSharp
