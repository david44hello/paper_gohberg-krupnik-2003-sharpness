/- potential/norm-correspondence/endpoint definitions.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Pencil
import GKSharp.Defs.Window
import GKSharp.Defs.RealLine

namespace GKSharp

open Real MeasureTheory
open scoped ContDiff

noncomputable def unitPoint (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

/-- sec2_obstacle.tex:40. The actual two-polynomial obstacle. -/
noncomputable def pairObstacle (p C : ℝ) (ρ z w : ℂ) : ℝ :=
  C ^ p * ‖z + star w‖ ^ p - ‖z + ρ * star w‖ ^ p

/-- sec2_obstacle.tex:46. Asymmetric complex-ratio angular obstacle. -/
noncomputable def gamma (p C : ℝ) (ρ : ℂ) (y t : ℝ) : ℝ :=
  C ^ p * (2 * cosh y + 2 * cos t) ^ (p / 2) -
    (exp y + ‖ρ‖ ^ 2 * exp (-y) + 2 * (star ρ * unitPoint t).re) ^ (p / 2)

/-- sec2_obstacle.tex:48. A real sInf: all uses require the nonempty/bounded-below theorem. -/
noncomputable def obstacle (p C : ℝ) (ρ : ℂ) (t : ℝ) : ℝ :=
  sInf (Set.range fun y : ℝ => gamma p C ρ y t)

def PolynomialPairBound (p C : ℝ) (ρ : ℂ) : Prop :=
  ∀ z w : Polynomial ℂ, w.eval 0 = 0 →
    0 ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), pairObstacle p C ρ (z.eval (unitPoint t)) (w.eval (unitPoint t))

noncomputable def potentialTrunc (n : ℕ) (x : EReal) : ℝ :=
  (max x (-(n : EReal))).toReal

/-- Textbook extended-real submean definition, exactly as018; includes identically−∞. -/
def IsSubharmonic (u : ℂ → EReal) : Prop :=
  (∀ z, u z ≠ ⊤) ∧ UpperSemicontinuous u ∧
    ∀ (n : ℕ) (c : ℂ) (r : ℝ), 0 < r →
      potentialTrunc n (u c) ≤ circleAverage (fun z => potentialTrunc n (u z)) c r

def IsSubharmonicOn (Ω : Set ℂ) (u : ℂ → EReal) : Prop :=
  (∀ z ∈ Ω, u z ≠ ⊤) ∧ UpperSemicontinuousOn u Ω ∧
    ∀ (n : ℕ) (c : ℂ) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ Ω →
      potentialTrunc n (u c) ≤ circleAverage (fun z => potentialTrunc n (u z)) c r

noncomputable def angularPotential (q : ℝ) (φ : ℝ → ℝ) (z : ℂ) : ℝ :=
  ‖z‖ ^ q * φ (Complex.arg z)

/-- Definition2.1: real-valued finite angular profile, subharmonic OFF0, periodic.
Continuity and removable-origin extension are results, not extra hypotheses. -/
def QSubtrig (q : ℝ) (φ : ℝ → ℝ) : Prop :=
  Function.Periodic φ (2 * Real.pi) ∧
    IsSubharmonicOn ({0}ᶜ : Set ℂ) (fun z => (angularPotential q φ z : EReal))

def IsPSH (u : ℂ × ℂ → EReal) : Prop :=
  (∀ x, u x ≠ ⊤) ∧ UpperSemicontinuous u ∧
    ∀ a b : ℂ × ℂ, IsSubharmonic (fun l : ℂ => u (a + l • b))

/-- Weak positivity of φ″+q²φ, tested against every nonnegative smooth compact test.
Use with locally integrableφ; O17 supplies continuity. This is a mathematical definition, never a computer check. -/
def PositiveAngularDistribution (q : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → (∀ x, 0 ≤ η x) →
    0 ≤ ∫ x : ℝ, φ x * (deriv (deriv η) x + q ^ 2 * η x)

noncomputable def homogeneousObstacle (p C : ℝ) (ρ z : ℂ) : ℝ :=
  ‖z‖ ^ (p / 2) * obstacle p C ρ (Complex.arg z)

def PolynomialDiscBound (M : ℂ → ℝ) : Prop :=
  ∀ g : Polynomial ℂ, g.eval 0 = 0 →
    0 ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), M (g.eval (unitPoint t))

def UniformCoercive (p C : ℝ) (ρ : ℂ) : Prop :=
  ∀ B : ℝ, ∃ Y : ℝ, 0 < Y ∧ ∀ y t : ℝ,
    Y ≤ |y| → B ≤ gamma p C ρ y t

noncomputable def contactKappa (C lam : ℝ) : ℝ := (C ^ 2 - lam) / (C ^ 2 - 1)

noncomputable def contactRadius (p lam : ℝ) : ℝ :=
  contactKappa (gk p (lam : ℂ)) lam * |cos (Real.pi / p)|

/-- The first printed closed form ofK. Its derivative/envelope identification is a separate row. -/
noncomputable def contactK (p lam : ℝ) : ℝ :=
  let C := gk p (lam : ℂ)
  2 * (1 - lam) * C * sin (Real.pi / p) ^ (p - 2) *
    |cos (Real.pi / p)| ^ (1 - p / 2) * (C ^ 2 + lam) ^ (p / 2 - 1)

noncomputable def axisGap (p lam : ℝ) : ℝ :=
  obstacle p (gk p (lam : ℂ)) (lam : ℂ) 0 - kConst p lam

noncomputable def chordTent (q c s t : ℝ) : ℝ :=
  if |t - c| ≤ s then sin (q * (s - |t - c|)) else 0

/-- Only the openp=1 endpoint's explicit threshold formula; not a global threshold definition. -/
noncomputable def endpointA (p : ℝ) : ℝ := Real.pi * (p - 1) / p

noncomputable def endpointD (p : ℝ) : ℝ :=
  let a := endpointA p
  sqrt (sin a ^ 2 / cos a ^ 4 * (p * Real.pi / (4 * a) - 1 - cos a ^ 2))

noncomputable def endpointLambda (p : ℝ) : ℝ := (1 - endpointD p) / (1 + endpointD p)

noncomputable def endpointError (a : ℝ) : ℝ :=
  sqrt a * (2 + 16 / 3 * log (8 / sqrt a) + 1.8 + 2 / 3 * log (1 / a) +
    8 + 4 * sqrt a + 4 * a)

noncomputable abbrev LpR (p : ℝ) := Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)

section Operators
variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The true sign-frequency multiplier on the real line, specified distributionally
by tests supported entirely in one open frequency half-line. Zero-frequency uniqueness
on finiteLp is a separate theorem, not silently imposed. -/
structure RealLinePencil (α β : ℂ) where
  map : LpR p →L[ℂ] LpR p
  positive_test : ∀ (f : LpR p) (φ : SchwartzMap ℝ ℂ),
    Function.support φ ⊆ Set.Ioi 0 →
      (∫ x : ℝ, map f x * (FourierTransform.fourier φ) x) =
        α * ∫ x : ℝ, f x * (FourierTransform.fourier φ) x
  negative_test : ∀ (f : LpR p) (φ : SchwartzMap ℝ ℂ),
    Function.support φ ⊆ Set.Iio 0 →
      (∫ x : ℝ, map f x * (FourierTransform.fourier φ) x) =
        β * ∫ x : ℝ, f x * (FourierTransform.fourier φ) x

noncomputable def constantLp (a : ℂ) : LpT p :=
  ContinuousMap.toLp (E := ℂ) (ENNReal.ofReal p) (volume : Measure Circ) ℂ
    (ContinuousMap.const Circ a)

noncomputable def zeroPart (f : LpT p) : LpT p := constantLp p (fourierCoeff (⇑f) 0)

variable {p}

/-- Actual circle function map with constant-frequency coefficientβ. -/
noncomputable def circleMinus (P : RieszProjection p) (α β : ℂ) (f : LpT p) : LpT p :=
  pencil P α β f + (β - α) • zeroPart p f

noncomputable def circleMid (P : RieszProjection p) (α β : ℂ) (f : LpT p) : LpT p :=
  (1 / 2 : ℂ) • (pencil P α β f + circleMinus P α β f)

/-- Operator norm as a supremum on the ACTUALLp function map. Equality with CLM norm,
boundedness and nonempty nonzero domain are explicit proof obligations. -/
noncomputable def functionNorm (T : LpT p → LpT p) : ℝ :=
  sSup {r : ℝ | ∃ f : LpT p, f ≠ 0 ∧ r = ‖T f‖ / ‖f‖}

end Operators
end GKSharp
