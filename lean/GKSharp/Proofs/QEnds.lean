/-
QEnds.lean — Re x^q on the real line and the two real ends of the ellipse Q(ρe^{iφ}), Section 5.1.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.RealSegment

namespace GKSharp

open Complex

/-- `Re x^q = |x|^q cos(qπ)` for a negative real `x`. -/
lemma reQPow_ofReal_neg {x : ℝ} (hx : x < 0) (q : ℝ) :
    reQPow (x : ℂ) q = (-x) ^ q * Real.cos (q * Real.pi) := by
  simp [reQPow, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx, Complex.arg_ofReal_of_neg hx]

/-- sec5_sharp_inequality.tex l.16-17: for `1 < p < 2`, `x ↦ Re x^q` (`q = p/2`) is nondecreasing on `ℝ`,
as `cos qπ < 0`. -/
theorem sec5_reQPow_monotone_proved {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    Monotone (fun x : ℝ => reQPow (x : ℂ) (p / 2)) := by
  have hq : 0 ≤ p / 2 := by linarith
  have hcos : Real.cos (p / 2 * Real.pi) < 0 := by
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  intro a b hab
  simp only
  rcases le_or_gt 0 a with ha | ha
  · rw [Proofs.RealSegment.reQPow_ofReal ha, Proofs.RealSegment.reQPow_ofReal (ha.trans hab)]
    exact Real.rpow_le_rpow ha hab hq
  · rw [reQPow_ofReal_neg ha]
    rcases le_or_gt 0 b with hb | hb
    · rw [Proofs.RealSegment.reQPow_ofReal hb]
      have h1 : (-a) ^ (p / 2) * Real.cos (p / 2 * Real.pi) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith) _) hcos.le
      exact h1.trans (Real.rpow_nonneg hb _)
    · rw [reQPow_ofReal_neg hb]
      exact mul_le_mul_of_nonpos_right
        (Real.rpow_le_rpow (by linarith) (by linarith) hq) hcos.le

/-- sec5_sharp_inequality.tex l.90-91 (`Q(φ) = Q(ρe^{iφ})`): "Q(0) − Q(π) = 2(1+λ)ρ ≥ 0 (both real) gives
max f_ρ = f_ρ(0)", here the comparison `f_ρ(π) ≤ f_ρ(0)` of the two ends. -/
theorem sec5_Q_ends_proved {p lam ρ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (_hl1 : lam < 1)
    (hρ : 0 < ρ) :
    let Q : ℝ → ℂ := fun φ => mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
    (Q 0).im = 0 ∧ (Q Real.pi).im = 0 ∧ Q 0 - Q Real.pi = ((2 * (1 + lam) * ρ : ℝ) : ℂ) ∧
    0 ≤ 2 * (1 + lam) * ρ ∧
    reQPow (Q Real.pi) (p / 2) ≤ reQPow (Q 0) (p / 2) := by
  intro Q
  have h0 : Q 0 = (((ρ - lam) * (1 - ρ) : ℝ) : ℂ) := by
    simp only [Q, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    exact Proofs.RealSegment.mobQ_ofReal lam ρ
  have hpi : Q Real.pi = (((-ρ - lam) * (1 + ρ) : ℝ) : ℂ) := by
    simp only [Q, Complex.exp_pi_mul_I, mul_neg, mul_one]
    have := Proofs.RealSegment.mobQ_ofReal lam (-ρ)
    push_cast at this ⊢
    rw [this]
    ring
  have hdiff : (ρ - lam) * (1 - ρ) - (-ρ - lam) * (1 + ρ) = 2 * (1 + lam) * ρ := by ring
  refine ⟨by rw [h0]; exact Complex.ofReal_im _, by rw [hpi]; exact Complex.ofReal_im _, ?_, ?_, ?_⟩
  · rw [h0, hpi, ← hdiff]
    push_cast
    ring
  · have : 0 ≤ 1 + lam := by linarith
    positivity
  · rw [h0, hpi]
    apply sec5_reQPow_monotone_proved hp1 hp2
    nlinarith

end GKSharp
