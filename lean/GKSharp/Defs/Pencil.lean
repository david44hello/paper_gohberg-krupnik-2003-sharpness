/- actual complex Lp Fourier projection/pencil definitions.
Copyright (C) Dave Goel 2026--now. -/
import Mathlib

namespace GKSharp

open MeasureTheory

instance fact_two_pi_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- P019_paper.tex:46. The same actual circle as018. -/
abbrev Circ := AddCircle (2 * Real.pi)

/-- P019_paper.tex:46. Actual complex Lp; volume has mass2π. The common
positive measure factor cancels in every pencil norm and norm inequality. -/
noncomputable abbrev LpT (p : ℝ) := Lp ℂ (ENNReal.ofReal p) (volume : Measure Circ)

noncomputable def mode (n : ℤ) (a : ℂ) (θ : ℝ) : ℂ :=
  a * Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * Complex.I)

noncomputable def trig (c : ℤ →₀ ℂ) (θ : ℝ) : ℂ := c.sum fun n a => mode n a θ

noncomputable def Pplus (c : ℤ →₀ ℂ) (θ : ℝ) : ℂ :=
  c.sum fun n a => if 0 ≤ n then mode n a θ else 0

noncomputable def Pminus (c : ℤ →₀ ℂ) (θ : ℝ) : ℂ := trig c θ - Pplus c θ

section Operators

variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- P019_paper.tex:46. An ACTUAL bounded complex-linear Fourier projection.
Existence is a separate theorem/input, never assumed by a structure instance.
The sole field constraint specifies the exact nonnegative-frequency mask. -/
structure RieszProjection where
  plus : LpT p →L[ℂ] LpT p
  coeff_plus : ∀ (f : LpT p) (n : ℤ),
    fourierCoeff (⇑(plus f)) n = if 0 ≤ n then fourierCoeff (⇑f) n else 0

variable {p}

noncomputable def rieszMinus (P : RieszProjection p) : LpT p →L[ℂ] LpT p :=
  ContinuousLinearMap.id ℂ (LpT p) - P.plus

/-- P019_paper.tex:48. The actual projection pencil. -/
noncomputable def pencil (P : RieszProjection p) (α β : ℂ) : LpT p →L[ℂ] LpT p :=
  α • P.plus + β • rieszMinus P

/-- P019_paper.tex:49. Normalized pencil's actual Lp operator norm.
Fourier uniqueness makes this independent of the supplied witness P. -/
noncomputable def pencilNorm (P : RieszProjection p) (ρ : ℂ) : ℝ := ‖pencil P 1 ρ‖

/-- P019_paper.tex:47. Modified Hilbert operator, including H1=−i. -/
noncomputable def shiftedHilbert (P : RieszProjection p) : LpT p →L[ℂ] LpT p :=
  (-Complex.I) • (P.plus - rieszMinus P)

/-- Exact all-Lp inequality underlying sec2_obstacle.tex:38–41. -/
def PencilBound (P : RieszProjection p) (ρ : ℂ) (C : ℝ) : Prop :=
  ∀ f : LpT p, ‖pencil P 1 ρ f‖ ≤ C * ‖f‖

end Operators

end GKSharp
