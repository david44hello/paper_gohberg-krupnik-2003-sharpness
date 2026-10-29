/- the ℓ² operator norm of a 2×2 complex matrix is determined by its Frobenius sum and |det| (the largest
singular value), hence GK_p(α, β) is determined by the two invariants and is unchanged by p ↦ p′
(sec2_obstacle.tex l.21-23, short v0.40). No cited input.
Copyright (C) Dave Goel 2026--now.

  For M = Aᴴ A: trace M = F := Σ|A_ij|², det M = |det A|², and 4|det A|² ≤ F² (|ad - bc| ≤ |a||d| + |b||c| ≤ F/2).
  The spectrum of M is the root set of X² - F X + |det A|²; M is self-adjoint, so ‖M‖ = spectral radius = the larger
  root, and ‖A‖² = ‖Aᴴ A‖ (C*-identity). The same route as GKRoot.gk_sq_eq, for an arbitrary 2×2 matrix. -/
import GKSharp.Proofs.GKRoot
import GKSharp.Proofs.GKInvariance

namespace GKSharp

namespace GKSingular

open scoped Matrix.Norms.L2Operator ComplexConjugate NNReal ENNReal
open Matrix Polynomial

/-- The Frobenius sum `Σᵢ Σⱼ |A i j|²` of a 2×2 complex matrix. -/
noncomputable def frob2 (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

lemma frob2_expand (A : Matrix (Fin 2) (Fin 2) ℂ) :
    frob2 A = ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2 := by
  simp only [frob2, Fin.sum_univ_two]; ring

lemma frob2_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ frob2 A := by
  rw [frob2_expand]; positivity

/-- `trace (Aᴴ A) = Σ |A i j|²`. -/
lemma trace_gram (A : Matrix (Fin 2) (Fin 2) ℂ) : (Aᴴ * A).trace = ((frob2 A : ℝ) : ℂ) := by
  simp only [trace_fin_two, mul_apply, Fin.sum_univ_two, conjTranspose_apply, Complex.star_def, Complex.conj_mul',
    frob2_expand]
  push_cast; ring

/-- `det (Aᴴ A) = |det A|²`. -/
lemma det_gram (A : Matrix (Fin 2) (Fin 2) ℂ) : (Aᴴ * A).det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_mul, det_conjTranspose, Complex.star_def, Complex.conj_mul']
  push_cast; ring

/-- `4 |det A|² ≤ (Σ |A i j|²)²`. -/
lemma disc_le (A : Matrix (Fin 2) (Fin 2) ℂ) : 4 * ‖A.det‖ ^ 2 ≤ frob2 A ^ 2 := by
  have hdet : ‖A.det‖ ≤ ‖A 0 0‖ * ‖A 1 1‖ + ‖A 0 1‖ * ‖A 1 0‖ := by
    rw [det_fin_two]
    calc ‖A 0 0 * A 1 1 - A 0 1 * A 1 0‖ ≤ ‖A 0 0 * A 1 1‖ + ‖A 0 1 * A 1 0‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  have h2 : 2 * ‖A.det‖ ≤ frob2 A := by
    rw [frob2_expand]
    nlinarith [sq_nonneg (‖A 0 0‖ - ‖A 1 1‖), sq_nonneg (‖A 0 1‖ - ‖A 1 0‖)]
  have h0 := norm_nonneg A.det
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith : 0 ≤ frob2 A + 2 * ‖A.det‖)]

/-- The larger root `(F + √(F² - 4|det A|²))/2`. -/
noncomputable def rootHi (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (frob2 A + Real.sqrt (frob2 A ^ 2 - 4 * ‖A.det‖ ^ 2)) / 2

/-- The smaller root `(F - √(F² - 4|det A|²))/2`. -/
noncomputable def rootLo (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (frob2 A - Real.sqrt (frob2 A ^ 2 - 4 * ‖A.det‖ ^ 2)) / 2

lemma rootLo_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ rootLo A := by
  have hF := frob2_nonneg A
  have hs : Real.sqrt (frob2 A ^ 2 - 4 * ‖A.det‖ ^ 2) ≤ frob2 A := by
    calc Real.sqrt (frob2 A ^ 2 - 4 * ‖A.det‖ ^ 2) ≤ Real.sqrt (frob2 A ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖A.det‖])
      _ = frob2 A := Real.sqrt_sq hF
  unfold rootLo; linarith

lemma rootLo_le_hi (A : Matrix (Fin 2) (Fin 2) ℂ) : rootLo A ≤ rootHi A := by
  unfold rootLo rootHi; linarith [Real.sqrt_nonneg (frob2 A ^ 2 - 4 * ‖A.det‖ ^ 2)]

/-- The spectrum of `Aᴴ A` is the root set of `X² - F X + |det A|²`. -/
lemma gram_spectrum (A : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    z ∈ spectrum ℂ (Aᴴ * A) ↔ z = (rootHi A : ℂ) ∨ z = (rootLo A : ℂ) := by
  rw [mem_spectrum_iff_isRoot_charpoly, charpoly_fin_two, IsRoot.def]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  rw [trace_gram, det_gram, quad_roots_complex _ _ (disc_le A) z]
  rfl

/-- **‖A‖² is the larger root** of `X² - (Σ|A i j|²) X + |det A|²` (ℓ² operator norm). -/
theorem norm_sq_eq (A : Matrix (Fin 2) (Fin 2) ℂ) : ‖A‖ ^ 2 = rootHi A := by
  set M := Aᴴ * A with hMdef
  have hlo := rootLo_nonneg A
  have hlohi := rootLo_le_hi A
  have hhi : 0 ≤ rootHi A := hlo.trans hlohi
  have hnorm_hi : ‖((rootHi A : ℝ) : ℂ)‖ = rootHi A := by
    rw [Complex.norm_real, Real.norm_of_nonneg hhi]
  have hnorm_lo : ‖((rootLo A : ℝ) : ℂ)‖ = rootLo A := by
    rw [Complex.norm_real, Real.norm_of_nonneg hlo]
  have hsa : IsSelfAdjoint M := isHermitian_conjTranspose_mul_self A
  have hsr : spectralRadius ℂ M = ((Real.toNNReal (rootHi A) : ℝ≥0) : ℝ≥0∞) := by
    apply le_antisymm
    · refine iSup₂_le fun z hz => ?_
      rw [quasispectrum_eq_spectrum_union_zero] at hz
      rcases hz with hz | hz
      · rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hhi]
        rcases (gram_spectrum A z).1 hz with rfl | rfl
        · exact hnorm_hi.le
        · exact hnorm_lo.le.trans hlohi
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        simp
    · refine le_trans ?_ (le_iSup₂ (f := fun k (_ : k ∈ quasispectrum ℂ M) => (‖k‖₊ : ℝ≥0∞))
        ((rootHi A : ℝ) : ℂ)
        (spectrum_subset_quasispectrum ℂ M ((gram_spectrum A _).2 (Or.inl rfl))))
      rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hhi]
      exact hnorm_hi.ge
  have hnormM : ‖M‖ = rootHi A := by
    have h := hsa.spectralRadius_eq_nnnorm
    rw [hsr, ENNReal.coe_inj] at h
    rw [← coe_nnnorm, ← h, Real.coe_toNNReal _ hhi]
  rw [← hnormM, hMdef, l2_opNorm_conjTranspose_mul_self, sq]

/-- Two 2×2 matrices with the same Frobenius sum and the same `|det|` have the same ℓ² operator norm. -/
theorem norm_eq_of_invariants {A B : Matrix (Fin 2) (Fin 2) ℂ} (hF : frob2 A = frob2 B) (hD : ‖A.det‖ = ‖B.det‖) :
    ‖A‖ = ‖B‖ := by
  have h : ‖A‖ ^ 2 = ‖B‖ ^ 2 := by rw [norm_sq_eq, norm_sq_eq, rootHi, rootHi, hF, hD]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- sec2_obstacle.tex l.21-23 (v0.40): the two invariants determine `GK_p(α, β)`. -/
theorem sec2_gk_from_invariants_proved (p : ℝ) (α β α' β' : ℂ)
    (hF : ∑ i, ∑ j, ‖gkMatrix p α β i j‖ ^ 2 = ∑ i, ∑ j, ‖gkMatrix p α' β' i j‖ ^ 2)
    (hD : ‖(gkMatrix p α β).det‖ = ‖(gkMatrix p α' β').det‖) : gkPair p α β = gkPair p α' β' :=
  norm_eq_of_invariants (by simp only [frob2]; exact hF) hD

/-- `cot²(π/p′) = cot²(π/p)`, `p′ = p/(p-1)` (`π/p′ = π - π/p`). -/
lemma cot_sq_dual {p : ℝ} (hp : 1 < p) : Real.cot (Real.pi / (p / (p - 1))) ^ 2 = Real.cot (Real.pi / p) ^ 2 := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hangle : Real.pi / (p / (p - 1)) = Real.pi - Real.pi / p := by field_simp
  rw [hangle, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub]
  ring

/-- sec2_obstacle.tex l.23 (v0.40): the invariants "are unchanged by replacing p by p′", so `GK_{p′}(α, β) = GK_p(α, β)`.
The text's route: both invariants (gkMatrix_frobenius_det) agree, then sec2_gk_from_invariants. -/
theorem sec2_gkPair_dual_proved {p : ℝ} (hp : 1 < p) (α β : ℂ) : gkPair (p / (p - 1)) α β = gkPair p α β := by
  obtain ⟨hF1, hD1⟩ := gkMatrix_frobenius_det (p / (p - 1)) α β
  obtain ⟨hF2, hD2⟩ := gkMatrix_frobenius_det p α β
  have hF : frob2 (gkMatrix (p / (p - 1)) α β) = frob2 (gkMatrix p α β) := by
    simp only [frob2]; rw [hF1, hF2, cot_sq_dual hp]
  have hD : ‖(gkMatrix (p / (p - 1)) α β).det‖ = ‖(gkMatrix p α β).det‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by rw [hD1, hD2])
  exact norm_eq_of_invariants hF hD

end GKSingular

end GKSharp
