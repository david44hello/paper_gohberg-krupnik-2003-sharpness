/- GKSharp/Cited/HV2000RealLine.lean - cited input from another paper (Hollenbeck-Verbitsky 2000), real line.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential

open MeasureTheory
open scoped FourierTransform

namespace GKSharp.Cited

/-- B. Hollenbeck, I. E. Verbitsky, Best constants for the Riesz projection, J. Funct. Anal. 175 (2000), 370-392
(refereed).
p. 371, (1.2): "The analytic projection on the real line, P₊ = P₊^ℝ, can be defined as the half-line Fourier multiplier
P₊^ℝ f(x) = 𝓕⁻¹(χ_{ℝ₊} 𝓕f)(x), x ∈ ℝ, (1.2) where 𝓕f and 𝓕⁻¹f are respectively the direct and inverse Fourier
transforms of f. Then P₋^ℝ = I − P₊^ℝ is the corresponding co-analytic projection".
p. 386, THEOREM 3.1: "Let 1 < p < ∞ and f ∈ L^p(ℝ) be a complex-valued function. Then
‖P± f‖_{L^p(ℝ)} ≤ (1/sin(π/p)) ‖f‖_{L^p(ℝ)}, (3.1) where 1/sin(π/p) is the best constant."
Form used here: only Schwartz inputs f, where χ_{(0,∞)} 𝓕f is integrable and 𝓕⁻¹(χ_{(0,∞)} 𝓕f) is a genuine
function. Fourier convention: Mathlib's 𝓕 uses exp(-2πixξ); HV leave the convention open, (3.1) bounds both P₊ and P₋,
a sign change of the convention swaps them, and a positive rescaling of ξ does not change χ_{(0,∞)}, so the Mathlib form
is covered. The paper cites this as [HV] (P019_paper.tex l.187, used at l.81) and applies it to its projection
convention at norm_correspondence.tex l.56 ("the classical norms in [HKV,HV,Pich] apply to the projection convention
used here"). -/
axiom hv2000_thm31_schwartz (p : ℝ) (hp : 1 < p) (f : SchwartzMap ℝ ℂ) :
    MemLp (𝓕⁻ (Set.indicator (Set.Ioi (0 : ℝ)) (𝓕 (f : ℝ → ℂ)))) (ENNReal.ofReal p) volume ∧
      eLpNorm (𝓕⁻ (Set.indicator (Set.Ioi (0 : ℝ)) (𝓕 (f : ℝ → ℂ)))) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (1 / Real.sin (Real.pi / p)) * eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) volume

end GKSharp.Cited
