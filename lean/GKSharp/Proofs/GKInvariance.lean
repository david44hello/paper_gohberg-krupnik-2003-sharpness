/- GKSharp/Proofs/GKInvariance.lean - invariants of the GK matrix: its squared Frobenius norm and |det|^2, and the
invariance of GK_p(alpha, beta) under interchanging alpha, beta and under conjugating both (short v0.40
sec2_obstacle.tex l.21-29).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GKProps
import GKSharp.Proofs.NormReduce

namespace GKSharp

open ComplexConjugate

/-- v0.40 sec2_obstacle.tex l.21-22: the squared Frobenius norm and the squared modulus of the determinant of the GK
matrix are `|α|² + |β|² + |β − α|² cot²(π/p)` and `|αβ|²`. -/
theorem gkMatrix_frobenius_det (p : ℝ) (α β : ℂ) :
    ∑ i, ∑ j, ‖gkMatrix p α β i j‖ ^ 2 = ‖α‖ ^ 2 + ‖β‖ ^ 2 + ‖β - α‖ ^ 2 * Real.cot (Real.pi / p) ^ 2 ∧
    ‖(gkMatrix p α β).det‖ ^ 2 = ‖α * β‖ ^ 2 := by
  constructor
  · simp only [Fin.sum_univ_two, gkMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, norm_zero, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  · rw [gkMatrix, Matrix.det_fin_two_of]
    ring_nf

/-- v0.40 sec2_obstacle.tex l.23: `GK_p(α, β) = GK_p(β, α)` (interchanging `α, β`), for `1 < p`. -/
theorem gkPair_swap {p : ℝ} (hp : 1 < p) (α β : ℂ) : gkPair p α β = gkPair p β α := by
  rcases eq_or_ne α 0 with hα | hα
  · subst hα
    rcases eq_or_ne β 0 with hβ | hβ
    · subst hβ; rfl
    · rw [gkPair_zero_left p hp, gkPair_homog p hβ, zero_div, gk_zero p hp]
      ring
  · rcases eq_or_ne β 0 with hβ | hβ
    · subst hβ
      rw [gkPair_zero_left p hp, gkPair_homog p hα, zero_div, gk_zero p hp]
      ring
    · rw [gkPair_homog p hα, gkPair_homog p hβ, gk_inv p (div_ne_zero hβ hα), norm_div, one_div_div]
      field_simp

/-- v0.40 sec2_obstacle.tex l.23: `GK_p(ᾱ, β̄) = GK_p(α, β)` (conjugating both coefficients), for `1 < p`. -/
theorem gkPair_conj {p : ℝ} (hp : 1 < p) (α β : ℂ) : gkPair p (conj α) (conj β) = gkPair p α β := by
  rcases eq_or_ne α 0 with hα | hα
  · subst hα
    rw [map_zero, gkPair_zero_left p hp, gkPair_zero_left p hp, Complex.norm_conj]
  · have hα' : conj α ≠ 0 := (map_ne_zero _).2 hα
    rw [gkPair_homog p hα', gkPair_homog p hα, Complex.norm_conj, ← map_div₀]
    congr 1
    exact gk_conj p (β / α)

end GKSharp
