/- RealLineFinal.lean - project 019, N family: N01_unique, N04 and N04_minus at their frozen types, with the
   density input N10 discharged by its proof (GKSharp.Proofs.N10Density.slice_N10_proved).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.RealLineLocal
import GKSharp.Proofs.N10Density

open MeasureTheory

namespace GKSharp.Proofs.RealLineFinal

open GKSharp.RealLineFourier GKSharp.Proofs.RealLineUnique GKSharp.Proofs.RealLineLocal

/-- N10 (density of separated compact-frequency Schwartz tests), from its proof. -/
theorem n10 : N10Prop := by
  intro q _ hq f ε hε
  exact GKSharp.Proofs.N10Density.slice_N10_proved hq f ε hε

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- norm_correspondence.tex l.6-9: the real-line multiplier is determined by its half-line weak tests. -/
theorem slice_N01_unique_proved (hp : 1 < p) (α β : ℂ) (T S : RealLinePencil p α β) : T = S :=
  slice_N01_unique_of_N10 n10 hp α β T S

/-- norm_correspondence.tex l.22-29: the localization identity. -/
theorem slice_N04_proved (hp : 1 < p) (_P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (η : SchwartzMap ℝ ℂ)
    (hη : HasCompactSupport (paperFourier η)) (c : ℤ →₀ ℂ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∃ Z W : SchwartzMap ℝ ℂ,
        (∀ x, Z x = η (h * x) * Complex.exp (Complex.I * (d : ℂ) * x) * trig c x) ∧
        (∀ x, W x = η (h * x) * Complex.exp (Complex.I * (d : ℂ) * x) *
          (α * Pplus c x + β * Pminus c x)) ∧
        T.map (Z.toLp (ENNReal.ofReal p) volume) = W.toLp (ENNReal.ofReal p) volume :=
  slice_N04_of_N10 n10 hp _P α β T d hd η hη c

/-- norm_correspondence.tex l.37: the negative-modulation twin; the constant frequency goes to β. -/
theorem slice_N04_minus_proved (hp : 1 < p) (α β : ℂ) (T : RealLinePencil p α β)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (η : SchwartzMap ℝ ℂ)
    (hη : HasCompactSupport (paperFourier η)) (c : ℤ →₀ ℂ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∃ Z W : SchwartzMap ℝ ℂ,
        (∀ x, Z x = η (h * x) * Complex.exp (-(Complex.I * (d : ℂ) * x)) * trig c x) ∧
        (∀ x, W x = η (h * x) * Complex.exp (-(Complex.I * (d : ℂ) * x)) *
          (α * Pplus c x + β * Pminus c x + (β - α) * c 0)) ∧
        T.map (Z.toLp (ENNReal.ofReal p) volume) = W.toLp (ENNReal.ofReal p) volume :=
  slice_N04_minus_of_N10 n10 hp α β T d hd η hη c

end GKSharp.Proofs.RealLineFinal
