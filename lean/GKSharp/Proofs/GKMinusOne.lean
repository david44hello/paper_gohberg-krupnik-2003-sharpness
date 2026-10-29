/- GKSharp/Proofs/GKMinusOne.lean - GK_p(-1) = tan(pi/(2p)) for 1 < p < 2 (sec2_obstacle.tex l.28).
20261028.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GKRoot

namespace GKSharp

/-- sec2_obstacle.tex l.28: for `1 < p < 2`, `GK_p(-1) = tan(π/(2p))` (the norm of `H` [Pich]). -/
theorem gk_minus_one {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : gk p (-1) = Real.tan (Real.pi / (2 * p)) := by
  have hp0 : 0 < p := by linarith
  set a := Real.pi / (2 * p) with ha
  have ha1 : Real.pi / 4 < a := by
    rw [ha, div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith [Real.pi_pos]
  have ha2 : a < Real.pi / 2 := by
    rw [ha, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_pos]
  have hθ : Real.pi / p = 2 * a := by rw [ha]; field_simp
  set s := Real.sin a with hs
  set c := Real.cos a with hc
  have hspos : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hcpos : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha2⟩
  have hsc : s ^ 2 = 1 - c ^ 2 := by rw [hs, hc]; linarith [Real.sin_sq_add_cos_sq a]
  have hcot : Real.cot (Real.pi / p) = (2 * c ^ 2 - 1) / (2 * s * c) := by
    rw [hθ, Real.cot_eq_cos_div_sin, Real.cos_two_mul, Real.sin_two_mul]
  have htan : Real.tan a = s / c := Real.tan_eq_sin_div_cos a
  have hn1 : ‖(-1 : ℂ)‖ = 1 := by simp
  have hn2 : ‖1 - (-1 : ℂ)‖ = 2 := by norm_num
  -- `t² = (s/c)²` is a root of the quadratic of eq:GK for `ρ = -1`
  have hroot : gkQuad p (-1) ((s / c) ^ 2) = 0 := by
    rw [gkQuad, gkMid, hn1, hn2, hcot]
    simp only [div_pow, mul_pow]
    rw [hsc]
    have h1 : 1 - c ^ 2 ≠ 0 := by rw [← hsc]; positivity
    field_simp
    ring
  -- the two roots multiply to `|ρ|² = 1`
  have hprod : gkRootHi p (-1) * gkRootLo p (-1) = 1 := by
    have h := gkQuad_factor p (-1) 0
    rw [gkQuad, hn1] at h
    linarith
  have ht1 : 1 < (s / c) ^ 2 := by
    have hlt : c < s := by
      rw [hs, hc, ← Real.sin_pi_div_two_sub]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith)
    rw [div_pow, one_lt_div (by positivity)]
    nlinarith
  have hlohi := gkRootLo_le_hi p (-1)
  have hhi : (s / c) ^ 2 = gkRootHi p (-1) := by
    rw [gkQuad_factor, mul_eq_zero, sub_eq_zero, sub_eq_zero] at hroot
    rcases hroot with h | h
    · exact h
    · exfalso
      rw [← h] at hprod hlohi
      nlinarith
  have hsq : gk p (-1) ^ 2 = Real.tan a ^ 2 := by rw [gk_sq_eq, htan, hhi]
  have htpos : 0 ≤ Real.tan a := by rw [htan]; positivity
  exact (pow_left_inj₀ (gk_nonneg _ _) htpos two_ne_zero).1 hsq

end GKSharp
