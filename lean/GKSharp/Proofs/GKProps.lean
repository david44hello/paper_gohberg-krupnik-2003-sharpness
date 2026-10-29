/- GKSharp/Proofs/GKProps.lean - two-coefficient GK and the real form eq:GKreal (sec2_obstacle.tex l.19-33).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GKRoot

namespace GKSharp

open scoped Matrix.Norms.L2Operator ComplexConjugate
open Matrix

/-- Scaling: `gkMatrix p α β = α • gkMatrix p 1 (β/α)` for `α ≠ 0`. -/
lemma gkMatrix_smul (p : ℝ) {α : ℂ} (hα : α ≠ 0) (β : ℂ) :
    gkMatrix p α β = α • gkMatrix p 1 (β / α) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gkMatrix] <;> field_simp

/-- sec2_obstacle.tex l.19: `GK_p(α, β) = |α| GK_p(β/α)` when `α ≠ 0`. -/
theorem gkPair_homog (p : ℝ) {α : ℂ} (hα : α ≠ 0) (β : ℂ) : gkPair p α β = ‖α‖ * gk p (β / α) := by
  rw [gkPair, gkMatrix_smul p hα, norm_smul]; rfl

/-- The sup norm of `![0, x]` with `x ≥ 0`. -/
lemma pi_norm_zero_real (x : ℝ) (hx : 0 ≤ x) : ‖(![0, (x : ℂ)] : Fin 2 → ℂ)‖ = x := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg hx).2 fun i => ?_
    fin_cases i <;> simp [Complex.norm_real, abs_of_nonneg hx, hx]
  · have := norm_le_pi_norm (![0, (x : ℂ)] : Fin 2 → ℂ) 1
    simpa [Complex.norm_real, abs_of_nonneg hx] using this

/-- The sup norm of `![α, β]`. -/
lemma pi_norm_two (α β : ℂ) : ‖(![α, β] : Fin 2 → ℂ)‖ = max ‖α‖ ‖β‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg α))).2 fun i => ?_
    fin_cases i <;> simp
  · refine max_le ?_ ?_
    · simpa using norm_le_pi_norm (![α, β] : Fin 2 → ℂ) 0
    · simpa using norm_le_pi_norm (![α, β] : Fin 2 → ℂ) 1

/-- sec2_obstacle.tex l.20: `GK_p(0, β) = |β| / sin(π/p)` for `1 < p`. -/
theorem gkPair_zero_left (p : ℝ) (hp : 1 < p) (β : ℂ) :
    gkPair p 0 β = ‖β‖ / Real.sin (Real.pi / p) := by
  have hp0 : 0 < p := by linarith
  have hsin : 0 < Real.sin (Real.pi / p) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by rw [div_lt_iff₀ hp0]; nlinarith [Real.pi_pos])
  set k := Real.cot (Real.pi / p) with hk
  set x : ℝ := ‖β‖ ^ 2 * (k ^ 2 + 1) with hx
  have hx0 : 0 ≤ x := by positivity
  have hgram : (gkMatrix p 0 β)ᴴ * gkMatrix p 0 β = diagonal ![0, (x : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gkMatrix, mul_apply, Fin.sum_univ_two, conjTranspose_apply, diagonal, hx, ← hk]
    have e : (starRingEnd ℂ) β * β = ((‖β‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' β
    linear_combination ((k : ℂ) ^ 2 + 1) * e
  have hsq : gkPair p 0 β ^ 2 = x := by
    rw [gkPair, sq, ← l2_opNorm_conjTranspose_mul_self, hgram, l2_opNorm_diagonal, pi_norm_zero_real x hx0]
  have hx' : x = (‖β‖ / Real.sin (Real.pi / p)) ^ 2 := by
    rw [hx, hk, Real.cot_eq_cos_div_sin]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / p)]
  rw [hx'] at hsq
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- sec2_obstacle.tex l.20: `GK_2(α, β) = max(|α|, |β|)`. -/
theorem gkPair_two (α β : ℂ) : gkPair 2 α β = max ‖α‖ ‖β‖ := by
  have hcot : Real.cot (Real.pi / 2) = 0 := by
    rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two, zero_div]
  have hmat : gkMatrix 2 α β = diagonal ![α, β] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gkMatrix, diagonal, hcot]
  rw [gkPair, hmat, l2_opNorm_diagonal, pi_norm_two]

/-- `GK_p(ρ)² ≥ 1`: the quadratic of eq:GK is `≤ 0` at `X = 1`. -/
lemma one_le_gk_sq (p : ℝ) (ρ : ℂ) : 1 ≤ gk p ρ ^ 2 := by
  rw [gk_sq_eq]
  have hq : gkQuad p ρ 1 ≤ 0 := by
    have : gkQuad p ρ 1 = -(‖1 - ρ‖ ^ 2 * Real.cot (Real.pi / p) ^ 2) := by
      simp only [gkQuad, gkMid]; ring
    rw [this]; nlinarith [sq_nonneg (‖1 - ρ‖ * Real.cot (Real.pi / p))]
  rw [gkQuad_factor] at hq
  by_contra hcon
  replace hcon := not_le.1 hcon
  have hlo := gkRootLo_le_hi p ρ
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - gkRootHi p ρ) (by linarith : (0 : ℝ) < 1 - gkRootLo p ρ)]

/-- `|ρ|² ≤ GK_p(ρ)²`: the quadratic of eq:GK is `≤ 0` at `X = |ρ|²`. -/
lemma norm_sq_le_gk_sq (p : ℝ) (ρ : ℂ) : ‖ρ‖ ^ 2 ≤ gk p ρ ^ 2 := by
  rw [gk_sq_eq]
  have hq : gkQuad p ρ (‖ρ‖ ^ 2) ≤ 0 := by
    have : gkQuad p ρ (‖ρ‖ ^ 2) = -(‖ρ‖ ^ 2 * (‖1 - ρ‖ ^ 2 * Real.cot (Real.pi / p) ^ 2)) := by
      simp only [gkQuad, gkMid]; ring
    rw [this]; nlinarith [sq_nonneg (‖1 - ρ‖ * Real.cot (Real.pi / p)), sq_nonneg ‖ρ‖,
      mul_nonneg (sq_nonneg ‖ρ‖) (sq_nonneg (‖1 - ρ‖ * Real.cot (Real.pi / p)))]
  rw [gkQuad_factor] at hq
  by_contra hcon
  replace hcon := not_le.1 hcon
  have hlo := gkRootLo_le_hi p ρ
  nlinarith [mul_pos (by linarith : (0 : ℝ) < ‖ρ‖ ^ 2 - gkRootHi p ρ)
    (by linarith : (0 : ℝ) < ‖ρ‖ ^ 2 - gkRootLo p ρ)]

lemma one_le_gk (p : ℝ) (ρ : ℂ) : 1 ≤ gk p ρ := by
  have h := one_le_gk_sq p ρ
  nlinarith [gk_nonneg p ρ]

/-- eq:GKreal (sec2_obstacle.tex l.28-33): for real `λ < 1` (the paper states `λ ∈ [-1, 1)`, `1 < p < 2`),
`C = GK_p(λ)` satisfies `(1 - λ) C = sin(π/p) (C² - λ)`, and `C` is the larger root of that quadratic. -/
theorem gk_real_eq {p : ℝ} (hp : 1 < p) {lam : ℝ} (hlam : lam < 1) :
    (1 - lam) * gk p lam = Real.sin (Real.pi / p) * (gk p lam ^ 2 - lam) ∧
      ∀ y : ℝ, (1 - lam) * y = Real.sin (Real.pi / p) * (y ^ 2 - lam) → y ≤ gk p lam := by
  have hp0 : 0 < p := by linarith
  set s := Real.sin (Real.pi / p) with hs
  set c := Real.cos (Real.pi / p) with hc
  have hsin : 0 < s :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by rw [div_lt_iff₀ hp0]; nlinarith [Real.pi_pos])
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  set C := gk p lam with hC
  have hC1 : 1 ≤ C := one_le_gk p lam
  have hquad : gkQuad p lam (C ^ 2) = 0 := (gk_sq_larger_root p lam).1
  have hnorm : ‖(lam : ℂ)‖ = |lam| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hnorm1 : ‖1 - (lam : ℂ)‖ = |1 - lam| := by
    rw [show (1 : ℂ) - lam = ((1 - lam : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  -- `s² (C² - λ)² = (1 - λ)² C²`
  set k := Real.cot (Real.pi / p) with hk
  have hk2 : k ^ 2 * s ^ 2 = c ^ 2 := by
    rw [hk, Real.cot_eq_cos_div_sin, ← hs, ← hc]; field_simp
  have hquad' : (C ^ 2) ^ 2 - (1 + lam ^ 2 + (1 - lam) ^ 2 * k ^ 2) * C ^ 2 + lam ^ 2 = 0 := by
    have h := hquad
    simp only [gkQuad, gkMid, hnorm, hnorm1, sq_abs, ← hk] at h
    exact h
  have hsq : (s * (C ^ 2 - lam)) ^ 2 = ((1 - lam) * C) ^ 2 := by
    linear_combination s ^ 2 * hquad' + (1 - lam) ^ 2 * C ^ 2 * hk2 + (1 - lam) ^ 2 * C ^ 2 * hsc
  have hC2 : 1 ≤ C ^ 2 := one_le_gk_sq p lam
  have hL : 0 ≤ (1 - lam) * C := mul_nonneg (by linarith) (by linarith)
  have hR : 0 ≤ s * (C ^ 2 - lam) := mul_nonneg hsin.le (by linarith)
  have heq : (1 - lam) * C = s * (C ^ 2 - lam) :=
    ((pow_left_inj₀ hR hL two_ne_zero).1 hsq).symm
  refine ⟨heq, fun y hy => ?_⟩
  -- `C (s (y² - λ) - (1 - λ) y) = s (y - C)(y C + λ)`, and `C² + λ ≥ 0` as `C² ≥ max(1, λ²)`
  have hfac : C * (s * (y ^ 2 - lam) - (1 - lam) * y) = s * (y - C) * (y * C + lam) := by
    linear_combination (-y) * heq
  have hlam2 : lam ^ 2 ≤ C ^ 2 := by
    have h := norm_sq_le_gk_sq p lam
    rwa [hnorm, sq_abs] at h
  by_contra hcon
  replace hcon := not_le.1 hcon
  have h1 : 0 < y - C := by linarith
  have h3 : 0 ≤ C ^ 2 + lam := by
    rcases le_or_gt (-1) lam with h | h
    · linarith
    · nlinarith
  have h2 : 0 < y * C + lam := by nlinarith [mul_pos h1 (by linarith : (0 : ℝ) < C)]
  have hpos : 0 < s * (y - C) * (y * C + lam) := mul_pos (mul_pos hsin h1) h2
  rw [← hfac, ← hy, sub_self, mul_zero] at hpos
  exact lt_irrefl 0 hpos

end GKSharp
