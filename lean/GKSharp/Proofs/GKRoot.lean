/- GKSharp/Proofs/GKRoot.lean - eq:GK and first properties of the Gohberg-Krupnik constant (sec2_obstacle.tex
l.14-33, sec3_nonreal.tex l.10-11).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.GK

namespace GKSharp

open scoped Matrix.Norms.L2Operator ComplexConjugate NNReal ENNReal
open Matrix Polynomial

/-- `det [[1, (ρ-1) cot], [0, ρ]] = ρ`. -/
lemma gkMatrix_det (p : ℝ) (ρ : ℂ) : (gkMatrix p 1 ρ).det = ρ := by
  simp [gkMatrix, det_fin_two_of]

/-- `det (Aᴴ A) = |ρ|²`. -/
lemma gkGram_det (p : ℝ) (ρ : ℂ) :
    ((gkMatrix p 1 ρ)ᴴ * gkMatrix p 1 ρ).det = ((‖ρ‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_mul, det_conjTranspose, gkMatrix_det, Complex.star_def, Complex.conj_mul']
  push_cast; ring

/-- `trace (Aᴴ A) = 1 + |ρ|² + |1-ρ|² cot²`, the middle coefficient of eq:GK. -/
lemma gkGram_trace (p : ℝ) (ρ : ℂ) :
    ((gkMatrix p 1 ρ)ᴴ * gkMatrix p 1 ρ).trace = ((gkMid p ρ : ℝ) : ℂ) := by
  simp only [trace_fin_two, mul_apply, Fin.sum_univ_two, conjTranspose_apply, gkMatrix, of_apply,
    cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  simp only [star_one, star_zero, one_mul, zero_mul, add_zero, Complex.star_def, Complex.conj_mul', gkMid]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev ρ 1]
  norm_cast
  rw [mul_pow, sq_abs]
  ring

/-- The larger root `(b + √(b² - 4|ρ|²))/2` of the quadratic of eq:GK. -/
noncomputable def gkRootHi (p : ℝ) (ρ : ℂ) : ℝ :=
  (gkMid p ρ + Real.sqrt (gkMid p ρ ^ 2 - 4 * ‖ρ‖ ^ 2)) / 2

/-- The smaller root `(b - √(b² - 4|ρ|²))/2` of the quadratic of eq:GK. -/
noncomputable def gkRootLo (p : ℝ) (ρ : ℂ) : ℝ :=
  (gkMid p ρ - Real.sqrt (gkMid p ρ ^ 2 - 4 * ‖ρ‖ ^ 2)) / 2

lemma one_add_sq_le_gkMid (p : ℝ) (ρ : ℂ) : 1 + ‖ρ‖ ^ 2 ≤ gkMid p ρ := by
  simp only [gkMid]; nlinarith [sq_nonneg (‖1 - ρ‖ * Real.cot (Real.pi / p))]

lemma gkMid_nonneg (p : ℝ) (ρ : ℂ) : 0 ≤ gkMid p ρ := by
  nlinarith [one_add_sq_le_gkMid p ρ, sq_nonneg ‖ρ‖]

lemma gk_disc (p : ℝ) (ρ : ℂ) : 4 * ‖ρ‖ ^ 2 ≤ gkMid p ρ ^ 2 := by
  have h1 := one_add_sq_le_gkMid p ρ
  nlinarith [sq_nonneg (1 - ‖ρ‖ ^ 2), sq_nonneg ‖ρ‖]

lemma gkRootLo_nonneg (p : ℝ) (ρ : ℂ) : 0 ≤ gkRootLo p ρ := by
  have hle : Real.sqrt (gkMid p ρ ^ 2 - 4 * ‖ρ‖ ^ 2) ≤ gkMid p ρ := by
    rw [Real.sqrt_le_left (gkMid_nonneg p ρ)]; nlinarith [sq_nonneg ‖ρ‖]
  simp only [gkRootLo]; linarith

lemma gkRootLo_le_hi (p : ℝ) (ρ : ℂ) : gkRootLo p ρ ≤ gkRootHi p ρ := by
  simp only [gkRootLo, gkRootHi]; linarith [Real.sqrt_nonneg (gkMid p ρ ^ 2 - 4 * ‖ρ‖ ^ 2)]

/-- The quadratic of eq:GK factors through its two roots. -/
lemma gkQuad_factor (p : ℝ) (ρ : ℂ) (X : ℝ) :
    gkQuad p ρ X = (X - gkRootHi p ρ) * (X - gkRootLo p ρ) := by
  have hs := Real.sq_sqrt (by linarith [gk_disc p ρ] : 0 ≤ gkMid p ρ ^ 2 - 4 * ‖ρ‖ ^ 2)
  simp only [gkQuad, gkRootHi, gkRootLo]
  linear_combination (1 / 4 : ℝ) * hs

/-- The two roots of `X² - b X + c` in `ℂ` when `b ≥ 0`, `c ≥ 0`, `b² ≥ 4c`. -/
lemma quad_roots_complex (b c : ℝ) (hdisc : 4 * c ≤ b ^ 2) (z : ℂ) :
    z ^ 2 - (b : ℂ) * z + (c : ℂ) = 0 ↔
      z = (((b + Real.sqrt (b ^ 2 - 4 * c)) / 2 : ℝ) : ℂ) ∨
        z = (((b - Real.sqrt (b ^ 2 - 4 * c)) / 2 : ℝ) : ℂ) := by
  have hs : Real.sqrt (b ^ 2 - 4 * c) ^ 2 = b ^ 2 - 4 * c := Real.sq_sqrt (by linarith)
  have key : z ^ 2 - (b : ℂ) * z + (c : ℂ) =
      (z - (((b + Real.sqrt (b ^ 2 - 4 * c)) / 2 : ℝ) : ℂ)) *
        (z - (((b - Real.sqrt (b ^ 2 - 4 * c)) / 2 : ℝ) : ℂ)) := by
    have hsC : ((Real.sqrt (b ^ 2 - 4 * c) : ℝ) : ℂ) ^ 2 = ((b ^ 2 - 4 * c : ℝ) : ℂ) := by
      exact_mod_cast hs
    push_cast at hsC ⊢
    linear_combination (1 / 4 : ℂ) * hsC
  rw [key, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- The spectrum of `Aᴴ A` is the root set of the quadratic of eq:GK. -/
lemma gkGram_spectrum (p : ℝ) (ρ : ℂ) (z : ℂ) :
    z ∈ spectrum ℂ ((gkMatrix p 1 ρ)ᴴ * gkMatrix p 1 ρ) ↔
      z = (gkRootHi p ρ : ℂ) ∨ z = (gkRootLo p ρ : ℂ) := by
  rw [mem_spectrum_iff_isRoot_charpoly, charpoly_fin_two, IsRoot.def]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  rw [gkGram_trace, gkGram_det, quad_roots_complex _ _ (gk_disc p ρ) z]
  rfl

/-- Closed form: `GK_p(ρ)²` equals the larger root of the quadratic of eq:GK. -/
lemma gk_sq_eq (p : ℝ) (ρ : ℂ) : gk p ρ ^ 2 = gkRootHi p ρ := by
  set M := (gkMatrix p 1 ρ)ᴴ * gkMatrix p 1 ρ with hMdef
  have hlo := gkRootLo_nonneg p ρ
  have hlohi := gkRootLo_le_hi p ρ
  have hhi : 0 ≤ gkRootHi p ρ := hlo.trans hlohi
  have hnorm_hi : ‖((gkRootHi p ρ : ℝ) : ℂ)‖ = gkRootHi p ρ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hhi]
  have hnorm_lo : ‖((gkRootLo p ρ : ℝ) : ℂ)‖ = gkRootLo p ρ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hlo]
  have hsa : IsSelfAdjoint M := isHermitian_conjTranspose_mul_self (gkMatrix p 1 ρ)
  have hsr : spectralRadius ℂ M = ((Real.toNNReal (gkRootHi p ρ) : ℝ≥0) : ℝ≥0∞) := by
    apply le_antisymm
    · refine iSup₂_le fun z hz => ?_
      rw [quasispectrum_eq_spectrum_union_zero] at hz
      rcases hz with hz | hz
      · rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hhi]
        rcases (gkGram_spectrum p ρ z).1 hz with rfl | rfl
        · exact hnorm_hi.le
        · exact hnorm_lo.le.trans hlohi
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        simp
    · refine le_trans ?_ (le_iSup₂ (f := fun k (_ : k ∈ quasispectrum ℂ M) => (‖k‖₊ : ℝ≥0∞))
        ((gkRootHi p ρ : ℝ) : ℂ)
        (spectrum_subset_quasispectrum ℂ M ((gkGram_spectrum p ρ _).2 (Or.inl rfl))))
      rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hhi]
      exact hnorm_hi.ge
  have hnormM : ‖M‖ = gkRootHi p ρ := by
    have h := hsa.spectralRadius_eq_nnnorm
    rw [hsr, ENNReal.coe_inj] at h
    rw [← coe_nnnorm, ← h, Real.coe_toNNReal _ hhi]
  rw [← hnormM, hMdef, l2_opNorm_conjTranspose_mul_self, sq]
  rfl

lemma gk_nonneg (p : ℝ) (ρ : ℂ) : 0 ≤ gk p ρ := norm_nonneg _

/-- eq:GK (l.21-26): `GK_p(ρ)²` is a root of `X² - (1 + |ρ|² + |1-ρ|² cot²(π/p)) X + |ρ|²`, and it is the
larger root. -/
theorem gk_sq_larger_root (p : ℝ) (ρ : ℂ) :
    gkQuad p ρ (gk p ρ ^ 2) = 0 ∧ ∀ X : ℝ, gkQuad p ρ X = 0 → X ≤ gk p ρ ^ 2 := by
  rw [gk_sq_eq]
  refine ⟨by rw [gkQuad_factor]; ring, fun X hX => ?_⟩
  rw [gkQuad_factor, mul_eq_zero, sub_eq_zero, sub_eq_zero] at hX
  rcases hX with rfl | rfl
  · exact le_rfl
  · exact gkRootLo_le_hi p ρ

/-- `cot(π/p) ≠ 0` for `1 < p`, `p ≠ 2`. -/
lemma cot_pi_div_ne_zero {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) : Real.cot (Real.pi / p) ≠ 0 := by
  have hp0 : 0 < p := by linarith
  have hsin : 0 < Real.sin (Real.pi / p) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by rw [div_lt_iff₀ hp0]; nlinarith [Real.pi_pos])
  rw [Real.cot_eq_cos_div_sin, div_ne_zero_iff]
  refine ⟨fun hcos => hp2 ?_, hsin.ne'⟩
  have hmem : Real.pi / p ∈ Set.Icc 0 Real.pi :=
    ⟨by positivity, by rw [div_le_iff₀ hp0]; nlinarith [Real.pi_pos]⟩
  have hhalf : Real.pi / 2 ∈ Set.Icc 0 Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
  have heq : Real.pi / p = Real.pi / 2 :=
    Real.injOn_cos hmem hhalf (by rw [hcos, Real.cos_pi_div_two])
  field_simp at heq
  linarith [Real.pi_pos]

/-- sec3_nonreal.tex l.10-11: for `p ≠ 2` (standing assumption of Section 3) and `ρ ≠ 1`,
`GK_p(ρ) > max(1, |ρ|)`. -/
theorem gk_gt_max {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {ρ : ℂ} (hρ : ρ ≠ 1) :
    max 1 ‖ρ‖ < gk p ρ := by
  set Y := max 1 (‖ρ‖ ^ 2) with hY
  have hcot := cot_pi_div_ne_zero hp hp2
  have hsub : 0 < ‖1 - ρ‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hρ))
  have hY1 : 1 ≤ Y := le_max_left _ _
  have hYr : ‖ρ‖ ^ 2 ≤ Y := le_max_right _ _
  have hprod : (Y - 1) * (Y - ‖ρ‖ ^ 2) = 0 := by
    rcases le_total 1 (‖ρ‖ ^ 2) with h | h
    · rw [hY, max_eq_right h]; ring
    · rw [hY, max_eq_left h]; ring
  have hneg : gkQuad p ρ Y < 0 := by
    have hpos : 0 < ‖1 - ρ‖ ^ 2 * Real.cot (Real.pi / p) ^ 2 * Y := by positivity
    have : gkQuad p ρ Y = (Y - 1) * (Y - ‖ρ‖ ^ 2) - ‖1 - ρ‖ ^ 2 * Real.cot (Real.pi / p) ^ 2 * Y := by
      simp only [gkQuad, gkMid]; ring
    rw [this, hprod]; linarith
  rw [gkQuad_factor] at hneg
  have hlohi := gkRootLo_le_hi p ρ
  have hYhi : Y < gkRootHi p ρ := by
    by_contra hcon
    replace hcon := not_lt.1 hcon
    have h1 : 0 ≤ Y - gkRootHi p ρ := by linarith
    have h2 : 0 ≤ Y - gkRootLo p ρ := by linarith
    nlinarith [mul_nonneg h1 h2]
  have hsq : (max 1 ‖ρ‖) ^ 2 < gk p ρ ^ 2 := by
    rw [gk_sq_eq]
    have : (max 1 ‖ρ‖) ^ 2 = Y := by
      rcases le_total 1 ‖ρ‖ with h | h
      · rw [max_eq_right h, hY, max_eq_right (by nlinarith)]
      · rw [max_eq_left h, hY, max_eq_left (by nlinarith [norm_nonneg ρ])]; norm_num
    rw [this]; exact hYhi
  exact lt_of_pow_lt_pow_left₀ 2 (gk_nonneg p ρ) hsq

/-- sec2_obstacle.tex l.27: `GK` is invariant under `p ↦ p' = p/(p-1)` (because `cot²(π/p)` is). -/
theorem gk_dual (p : ℝ) (hp : 1 < p) (ρ : ℂ) : gk (p / (p - 1)) ρ = gk p ρ := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hangle : Real.pi / (p / (p - 1)) = Real.pi - Real.pi / p := by field_simp
  have hcot : Real.cot (Real.pi / (p / (p - 1))) ^ 2 = Real.cot (Real.pi / p) ^ 2 := by
    rw [hangle, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub]
    ring
  have hmid : gkMid (p / (p - 1)) ρ = gkMid p ρ := by simp only [gkMid, hcot]
  have hsq : gk (p / (p - 1)) ρ ^ 2 = gk p ρ ^ 2 := by
    rw [gk_sq_eq, gk_sq_eq, gkRootHi, gkRootHi, hmid]
  exact (pow_left_inj₀ (gk_nonneg _ _) (gk_nonneg _ _) two_ne_zero).1 hsq

/-- sec2_obstacle.tex l.27-28: `GK_p(0) = 1/sin(π/p)` for `1 < p`. -/
theorem gk_zero (p : ℝ) (hp : 1 < p) : gk p 0 = 1 / Real.sin (Real.pi / p) := by
  have hp0 : 0 < p := by linarith
  have hsin : 0 < Real.sin (Real.pi / p) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by rw [div_lt_iff₀ hp0]; nlinarith [Real.pi_pos])
  have hmid : gkMid p 0 = 1 / Real.sin (Real.pi / p) ^ 2 := by
    simp only [gkMid, norm_zero, sub_zero, norm_one, Real.cot_eq_cos_div_sin]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / p)]
  have hsq : gk p 0 ^ 2 = (1 / Real.sin (Real.pi / p)) ^ 2 := by
    rw [gk_sq_eq, gkRootHi, norm_zero, hmid]
    have hpos : 0 ≤ 1 / Real.sin (Real.pi / p) ^ 2 := by positivity
    rw [show (1 / Real.sin (Real.pi / p) ^ 2) ^ 2 - 4 * (0 : ℝ) ^ 2 = (1 / Real.sin (Real.pi / p) ^ 2) ^ 2 by ring,
      Real.sqrt_sq hpos]
    ring
  exact (pow_left_inj₀ (gk_nonneg _ _) (by positivity) two_ne_zero).1 hsq

end GKSharp
