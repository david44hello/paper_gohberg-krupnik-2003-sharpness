/- Coverage links for the approved targets of slice SliceA_Potential: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 eb4fed10b0defe69fc42fba2af020460; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.GKRoot
import GKSharp.Proofs.Pencil
import GKSharp.Paper.Statements

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_Potential

open Real MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator ContDiff
namespace GKSharp

def FiniteBlaschke (B : ℂ → ℂ) : Prop :=
  ∃ (phase : ℂ) (roots : List ℂ), ‖phase‖ = 1 ∧
    (∀ a ∈ roots, ‖a‖ < 1) ∧
    ∀ z : ℂ, B z = phase * (roots.map fun a => (z - a) / (1 - star a * z)).prod

noncomputable def polarLaplacian (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  deriv (deriv fun x : ℝ => u ((x : ℂ) + (z.im : ℂ) * Complex.I)) z.re +
    deriv (deriv fun y : ℝ => u ((z.re : ℂ) + (y : ℂ) * Complex.I)) z.im

noncomputable def fejerMean (u : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    ((1 - (n.natAbs : ℝ) / (N + 1) : ℝ) : ℂ) *
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      (∫ s in (0 : ℝ)..(2 * Real.pi), (u s : ℂ) * unitPoint (-(n : ℝ) * s)) *
      unitPoint ((n : ℝ) * t)).re

namespace Paper
variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- Coverage link (renamed): the approved target `slice_O01` of slice SliceA_Potential, from installed rows. Paper place: P019_paper.tex:54–55 (short v3.70; the definition, recalled at sec2_obstacle.tex:20). -/
theorem cover_slice_O01 : ∀ (p : ℝ) (α β : ℂ), gkPair p α β = ‖gkMatrix p α β‖ :=
  by intro p α β; rfl

/-- Coverage link (renamed): the approved target `slice_O03` of slice SliceA_Potential, from installed rows. Paper place: sec2_obstacle.tex:31–36 (short v3.70). -/
theorem cover_slice_O03 : ∀ (p : ℝ) (ρ : ℂ),
    gkQuad p ρ (gk p ρ ^ 2) = 0 ∧ ∀ X : ℝ, gkQuad p ρ X = 0 → X ≤ gk p ρ ^ 2 :=
  @GKSharp.Paper.eq_GK

/-- Coverage link (renamed): the approved target `slice_O07` of slice SliceA_Potential, from installed rows. Paper place: sec2_obstacle.tex:46–47 (short v3.70). -/
theorem cover_slice_O07 :
    (∀ c : ℤ →₀ ℂ, ∃ z w : Polynomial ℂ, w.eval 0 = 0 ∧
      ∀ t, Pplus c t = z.eval (unitPoint t) ∧ Pminus c t = star (w.eval (unitPoint t))) ∧
    (∀ z w : Polynomial ℂ, w.eval 0 = 0 → ∃ c : ℤ →₀ ℂ,
      ∀ t, Pplus c t = z.eval (unitPoint t) ∧ Pminus c t = star (w.eval (unitPoint t))) :=
  GKSharp.polynomial_pair_correspondence

/-- Coverage link (renamed): the approved target `slice_O08` of slice SliceA_Potential, from installed rows. Paper place: sec2_obstacle.tex:47–51 (short v3.70). -/
theorem cover_slice_O08 : ∀ (hp : 1 < p) (P : RieszProjection p) (ρ : ℂ) (C : ℝ) (hC : 0 ≤ C),
    pencilNorm P ρ ≤ C ↔ PolynomialPairBound p C ρ :=
  by intro hp P ρ C hC; exact GKSharp.Paper.eq_pairs hp P ρ hC

/-- Coverage link (renamed): the approved target `slice_O10` of slice SliceA_Potential, from installed rows. Paper place: sec2_obstacle.tex:57–58 (short v3.70). -/
theorem cover_slice_O10 : ∀ (P : RieszProjection p) (ρ : ℂ), max 1 ‖ρ‖ ≤ pencilNorm P ρ :=
  GKSharp.Paper.sec2_norm_ge_max (p := p)

/-- Coverage link (renamed): the approved target `slice_O15` of slice SliceA_Potential, from installed rows. Paper place: sec2_obstacle.tex:63–66 (short v3.70). -/
theorem cover_slice_O15 : ∀ (q : ℝ) (φ : ℝ → ℝ), QSubtrig q φ ↔
    Function.Periodic φ (2 * Real.pi) ∧
      IsSubharmonicOn ({0}ᶜ : Set ℂ) (fun z => (angularPotential q φ z : EReal)) :=
  by intro q φ; rfl

end Paper
end GKSharp

end GKSharp.CoverageLinks.SliceA_Potential
