/- external Cole existence input, source/type independently approved.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential

namespace GKSharp.Cited

/-- Hollenbeck, Kalton, Verbitsky, Studia Math.157(2003),237–278, Theorem2.1,p242.
REFEREED. Source: https://kaltonmemorial.missouri.edu/assets/docs/sm2003a.pdf.
VERBATIM: "Suppose F : C → [−∞, ∞) is an upper semicontinuous function and E is a
nonempty subset of C. Then in order that we have the inequality ∫₀^{2π} F∘f(e^{iθ}) dθ/2π ≥ 0 (2.1) whenever f is a polynomial
with f(0) ∈ E, it is necessary and sufficient that there exists a subharmonic function G with G(z) ≤ F(z) for z ∈ C and
G(z) ≥ 0 for z ∈ E."
Only the direction from the disc inequalities to existence is used. The positive normalization factor is omitted;
all lower truncations encode the extended-real integral. No homogeneity, maximality or reduction from this paper is assumed.
Fresh math-lead source/type review: 2026-10-28.
Fresh independent source/type/definition review: 2026-10-28; MATCH, 0 MUST. -/
axiom hkv_thm21 (F : ℂ → EReal) (hF : UpperSemicontinuous F) (htop : ∀ z, F z ≠ ⊤)
    (E : Set ℂ) (hE : E.Nonempty)
    (hdisc : ∀ g : Polynomial ℂ, g.eval 0 ∈ E → ∀ n : ℕ,
      0 ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), potentialTrunc n (F (g.eval (unitPoint t)))) :
    ∃ G : ℂ → EReal, IsSubharmonic G ∧ (∀ z, G z ≤ F z) ∧ ∀ z ∈ E, 0 ≤ G z

end GKSharp.Cited
