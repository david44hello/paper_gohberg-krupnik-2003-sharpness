/-
GKSharp/Proofs/ContactExpanded.lean — paper 019 (sec4b_failure.tex l. 58-78): the scalar algebraic collection of
the contact sign test after the printed derivatives are substituted. Raw scalar identity only: no derivative,
Schur, analytic or computer-check premise. Not the contact_sign_factorization row by itself.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Route: by the proved B12 identities every quantity is rational in the contact root `r`:
`cs = (1+λ) r/(r²+λ)`, `sn² = (r²-1)(r²-λ²)/(r²+λ)²`, `D = (r²-λ)(r²-λ²)/(r²(r²+λ))`, `σ = (r²+λ)/r`,
`v = (r²-λ)/r`; with `r > 1`, `|λ| < r`, `λ > -1` all denominators are nonzero, and the identity is a polynomial
identity in `(p, r, λ)` after clearing them.
-/
import GKSharp.Defs.ThresholdAnalysis
import GKSharp.Proofs.ContactScalar

namespace GKSharp

open Set

/-- B:58–78 scalar collection: the expanded sign expression equals `bZero · signBracket` at the actual contact. -/
theorem contact_expanded_factorization (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let r := Threshold.rContact p lam
    let v := Threshold.vContact p lam
    let D := Threshold.dOne p lam
    2 * p * lam * (1 - lam) / (r * v * D)
      + p * (1 - lam) ^ 2 / (Threshold.sn p ^ 2 * v ^ 2)
      - (1 - lam) * Threshold.cs p / (Threshold.sn p ^ 2 * v)
      - (1 - lam) / (Threshold.cs p * v) *
          (Threshold.sigmaContact p lam / v
            - p * ((1 - lam / r * Threshold.cs p) / D) + p / 2) ^ 2
      = Threshold.bZero p lam * Threshold.signBracket p lam := by
  dsimp only
  obtain ⟨hr1, hrabs, -, hsum⟩ := contact_root_properties hp hp2 hlam
  obtain ⟨hcs, hsn2, hD⟩ := contact_rational_identities_proved p lam hp hp2 hlam
  unfold Threshold.bZero Threshold.signBracket Threshold.vContact
  rw [← hsum, hD, hsn2, hcs]
  generalize Threshold.rContact p lam = R at hr1 hrabs ⊢
  have hR0 : R ≠ 0 := by linarith
  have hl1 : 1 + lam ≠ 0 := by linarith [hlam.1]
  have hRl : R ^ 2 + lam ≠ 0 := by nlinarith [hlam.1]
  have hRm : R ^ 2 - lam ≠ 0 := by nlinarith [hlam.2]
  have hR1 : R ^ 2 - 1 ≠ 0 := by nlinarith
  have hRa : R ^ 2 - lam ^ 2 ≠ 0 := by
    have := abs_lt.1 hrabs
    nlinarith
  have hv : R - lam / R = (R ^ 2 - lam) / R := by field_simp
  have hs : R + lam / R = (R ^ 2 + lam) / R := by field_simp
  rw [hv, hs]
  field_simp
  ring

end GKSharp
