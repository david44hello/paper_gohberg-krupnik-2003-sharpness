/-
GKSharp/Proofs/NegativeContact.lean — paper 019 (sec4b_failure.tex l. 87): row `negative_contact_unique`,
with the exact type of the statement draft.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Route: for `0 < a < b`, `(b + λ/b) - (a + λ/a) = (b - a)(1 - λ/(ab)) > 0` because `λ ≤ 0`.
-/
import Mathlib

namespace GKSharp

open Set

/-- B:87, row `negative_contact_unique`. -/
theorem negative_contact_unique_proved (lam : ℝ) (hlam : lam ∈ Ioc (-1 : ℝ) 0) :
    StrictMonoOn (fun r : ℝ => r + lam / r) (Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := ha
  have hb0 : 0 < b := hb
  have hdiff : (b + lam / b) - (a + lam / a) = (b - a) * (1 - lam / (a * b)) := by
    field_simp
    ring
  have hfac : 0 < 1 - lam / (a * b) := by
    have : lam / (a * b) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hlam.2 (mul_pos ha0 hb0).le
    linarith
  have hpos : 0 < (b - a) * (1 - lam / (a * b)) := mul_pos (by linarith) hfac
  show a + lam / a < b + lam / b
  linarith

end GKSharp
