/- GKSharp/Proofs/NormReduce.lean - the reduction P019_paper.tex:55-57, exactly: N_p(ρ) = s·N_q(r) AND GK_p(ρ) = s·GK_q(r)
with q ∈ {p, p'}, r ∈ {ρ, ρ̄, 1/ρ, 1/ρ̄}, |r| ≤ 1, s = max(1, |ρ|); and the two GK symmetries it needs (review M3/S13/T1).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.PencilDual
import GKSharp.Proofs.GKRoot
import GKSharp.Cited.HV2000

namespace GKSharp

/-- `GK_p(ρ̄) = GK_p(ρ)`: both coefficients of eq:GK are conjugation invariant. -/
theorem gk_conj (p : ℝ) (ρ : ℂ) : gk p (star ρ) = gk p ρ := by
  have hmid : gkMid p (star ρ) = gkMid p ρ := by
    rw [gkMid, gkMid, norm_star, show (1 : ℂ) - star ρ = star (1 - ρ) by simp, norm_star]
  have hroot : gkRootHi p (star ρ) = gkRootHi p ρ := by
    rw [gkRootHi, gkRootHi, hmid, norm_star]
  have hsq : gk p (star ρ) ^ 2 = gk p ρ ^ 2 := by rw [gk_sq_eq, gk_sq_eq, hroot]
  exact (pow_left_inj₀ (gk_nonneg _ _) (gk_nonneg _ _) two_ne_zero).1 hsq

/-- `GK_p(ρ) = |ρ| GK_p(1/ρ)` for `ρ ≠ 0`: under `ρ ↦ 1/ρ` the quadratic of eq:GK scales by `|ρ|²`. -/
theorem gk_inv (p : ℝ) {ρ : ℂ} (hρ : ρ ≠ 0) : gk p ρ = ‖ρ‖ * gk p (1 / ρ) := by
  have hr : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hmid : gkMid p (1 / ρ) = gkMid p ρ / ‖ρ‖ ^ 2 := by
    have h1 : (1 : ℂ) - 1 / ρ = -((1 - ρ) / ρ) := by field_simp; ring
    rw [gkMid, gkMid, h1, norm_neg, norm_div, norm_div, norm_one]
    field_simp
    ring
  have hroot : gkRootHi p (1 / ρ) = gkRootHi p ρ / ‖ρ‖ ^ 2 := by
    have hd : gkMid p (1 / ρ) ^ 2 - 4 * ‖1 / ρ‖ ^ 2 = (gkMid p ρ ^ 2 - 4 * ‖ρ‖ ^ 2) / (‖ρ‖ ^ 2) ^ 2 := by
      rw [hmid, norm_div, norm_one]
      field_simp
    rw [gkRootHi, gkRootHi, hd, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity), hmid]
    field_simp
  have hsq : gk p ρ ^ 2 = (‖ρ‖ * gk p (1 / ρ)) ^ 2 := by
    rw [mul_pow, gk_sq_eq, gk_sq_eq, hroot]
    field_simp
  exact (pow_left_inj₀ (gk_nonneg _ _) (mul_nonneg hr.le (gk_nonneg _ _)) two_ne_zero).1 hsq

/-- I11, P019_paper.tex:55-57 (review M3 type): the identities reduce `(p, ρ)` to an exponent `q ∈ {p, p'}` in
`(1, 2]` and a ratio `r ∈ {ρ, ρ̄, 1/ρ, 1/ρ̄}` with `|r| ≤ 1`; both the pencil norm and `GK` scale by the same
`s = max(1, |ρ|)`, so the sharpness question `N = GK` is the same at `(p, ρ)` and at `(q, r)`. For `p > 2` the projection
on `L^{p'}` is the cited Hollenbeck-Verbitsky one. -/
theorem pencil_and_gk_reduce {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) (ρ : ℂ) :
    ∃ (q : ℝ) (hq : Fact (1 ≤ ENNReal.ofReal q)) (Q : @RieszProjection q hq) (r : ℂ) (s : ℝ),
      (q = p ∨ q = p / (p - 1)) ∧ 1 < q ∧ q ≤ 2 ∧
      (r = ρ ∨ r = star ρ ∨ r = 1 / ρ ∨ r = 1 / star ρ) ∧ ‖r‖ ≤ 1 ∧
      s = max 1 ‖ρ‖ ∧
      pencilNorm P ρ = s * @pencilNorm q hq Q r ∧ gk p ρ = s * gk q r := by
  -- one exponent: `σ` with `|σ| = |ρ|` goes to `σ` (if `|σ| ≤ 1`) or to `1/σ` (I09 and `gk_inv`)
  have hred : ∀ (q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)] (Q : RieszProjection q) (σ : ℂ), ‖σ‖ = ‖ρ‖ →
      ∃ r : ℂ, (r = σ ∨ r = 1 / σ) ∧ ‖r‖ ≤ 1 ∧ pencilNorm Q σ = max 1 ‖ρ‖ * pencilNorm Q r ∧
        gk q σ = max 1 ‖ρ‖ * gk q r := by
    intro q _ Q σ hσρ
    by_cases h1 : ‖σ‖ ≤ 1
    · have hmax : max 1 ‖ρ‖ = 1 := max_eq_left (hσρ ▸ h1)
      exact ⟨σ, Or.inl rfl, h1, by rw [hmax, one_mul], by rw [hmax, one_mul]⟩
    · have hσ : σ ≠ 0 := by
        rintro rfl
        simp at h1
      have hmax : max 1 ‖ρ‖ = ‖σ‖ := by rw [hσρ]; exact max_eq_right (hσρ ▸ (le_of_not_ge h1))
      refine ⟨1 / σ, Or.inr rfl, ?_, by rw [hmax]; exact pencilNorm_inv Q σ hσ, by rw [hmax]; exact gk_inv q hσ⟩
      rw [norm_div, norm_one]
      exact (div_le_one (norm_pos_iff.mpr hσ)).mpr (le_of_not_ge h1)
  rcases le_or_gt p 2 with hle | hgt
  · obtain ⟨r, hr, hr1, hN, hG⟩ := hred p P ρ rfl
    refine ⟨p, inferInstance, P, r, max 1 ‖ρ‖, Or.inl rfl, hp, hle, ?_, hr1, rfl, hN, hG⟩
    rcases hr with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
  · have hq := fact_conjExp hp
    obtain ⟨Q, -⟩ := Cited.hv2000_riesz_norm (p / (p - 1)) (one_lt_conjExp hp)
    obtain ⟨r, hr, hr1, hN, hG⟩ := hred (p / (p - 1)) Q (star ρ) (norm_star ρ)
    refine ⟨p / (p - 1), hq, Q, r, max 1 ‖ρ‖, Or.inr rfl, one_lt_conjExp hp, (conjExp_lt_two hgt).le, ?_, hr1,
      rfl, (pencilNorm_dual hp P Q ρ).trans hN, ?_⟩
    · rcases hr with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rw [← hG, gk_conj, gk_dual p hp]

end GKSharp
