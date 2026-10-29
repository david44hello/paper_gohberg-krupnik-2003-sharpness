/- GKSharp/Proofs/KConst.lean - the two closed forms of K agree (sec2_obstacle.tex l.135-137, eq:K).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GKProps
import GKSharp.Defs.RealLine

namespace GKSharp

/-- eq:K, sec2_obstacle.tex l.135-137 (1 < p < 2, λ ∈ [-1, 1), C = GK_p(λ), q = p/2, s₀ = sin(π/p), c₀ = -cos(π/p)):
`2(1-λ) C s₀^{p-2} c₀^{1-q} (C²+λ)^{q-1} = 2(1-λ)^p C^p (C²+λ)^{q-1} / (s₀ c₀^{q-1} (C²-λ)^{p-1})`. -/
theorem eq_K_forms {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hlam1 : lam < 1) :
    kConst p lam =
      2 * (1 - lam) ^ p * gk p lam ^ p * (gk p lam ^ 2 + lam) ^ (p / 2 - 1) /
        (Real.sin (Real.pi / p) * (-Real.cos (Real.pi / p)) ^ (p / 2 - 1) * (gk p lam ^ 2 - lam) ^ (p - 1)) := by
  have hp0 : 0 < p := by linarith
  set s := Real.sin (Real.pi / p) with hs
  set c := -Real.cos (Real.pi / p) with hc
  set C := gk p lam with hC
  have hsin : 0 < s :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by rw [div_lt_iff₀ hp0]; nlinarith [Real.pi_pos])
  have hcos : 0 < c := by
    rw [hc, neg_pos]
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · rw [lt_div_iff₀ hp0]; nlinarith [Real.pi_pos]
    · have : Real.pi / p < Real.pi := by rw [div_lt_iff₀ hp0]; nlinarith [Real.pi_pos]
      linarith [Real.pi_pos]
  have hC1 : 1 ≤ C := one_le_gk p lam
  have hC0 : 0 < C := by linarith
  have hl : 0 < 1 - lam := by linarith
  have heq : (1 - lam) * C = s * (C ^ 2 - lam) := (gk_real_eq hp1 hlam1).1
  have hCl : C ^ 2 - lam = (1 - lam) * C / s := by field_simp; linarith
  -- rewrite the second form
  rw [hCl, Real.div_rpow (by positivity) hsin.le, Real.mul_rpow hl.le hC0.le]
  have e1 : (1 - lam) ^ p = (1 - lam) * (1 - lam) ^ (p - 1) := by
    rw [← Real.rpow_one_add' hl.le (by linarith)]; ring_nf
  have e2 : C ^ p = C * C ^ (p - 1) := by
    rw [← Real.rpow_one_add' hC0.le (by linarith)]; ring_nf
  have e3 : s ^ (p - 1) = s * s ^ (p - 2) := by
    rw [← Real.rpow_one_add' hsin.le (by linarith)]; ring_nf
  have e4 : c ^ (1 - p / 2) = (c ^ (p / 2 - 1))⁻¹ := by
    rw [← Real.rpow_neg hcos.le]; ring_nf
  have h1 : 0 < (1 - lam) ^ (p - 1) := Real.rpow_pos_of_pos hl _
  have h2 : 0 < C ^ (p - 1) := Real.rpow_pos_of_pos hC0 _
  have h3 : 0 < s ^ (p - 2) := Real.rpow_pos_of_pos hsin _
  have h4 : 0 < c ^ (p / 2 - 1) := Real.rpow_pos_of_pos hcos _
  rw [kConst, ← hs, ← hc, ← hC, e1, e2, e3, e4]
  field_simp

end GKSharp
