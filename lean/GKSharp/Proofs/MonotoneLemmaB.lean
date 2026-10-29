/- Lemma B assembly, frozen sec5d_monotone.tex:61-66 (row lemma_B; type verbatim from the proposal
v020). CONDITIONAL: premise-style on the open row lemma_onevar (premise type OnevarHyp = its exact type).
Route = the text: the derivative has the sign of 4(m²-1)λ/(1+λ)² - Ψ_m(α), α = (1-p/2)θ < π/(m+1); the first term
is ≤ 0 for λ ≤ 0 and Ψ_m(α) > 0 (sec5d:67-68, proved in MonotoneSine), so K_f' < 0 on (0,π).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneBplusB
import GKSharp.Proofs.MonotoneSine

namespace GKSharp

open BplusB

/-- Row `lemma_B`, premise-style on the open row `lemma_onevar` (its exact type `OnevarHyp`). -/
theorem lemma_B_proved (onevar : OnevarHyp) {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl0 : lam ≤ 0) : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) := by
  have hl1 : lam < 1 := by linarith
  have h2p : 0 < 2 - p := by linarith
  have hm : 1 < p / (2 - p) := by
    rw [lt_div_iff₀ h2p]
    linarith
  have hm1 : 0 < p / (2 - p) + 1 := by linarith
  have hhalf : (1 - p / 2) * (p / (2 - p)) = p / 2 := by
    rw [show 1 - p / 2 = (2 - p) / 2 by ring, div_mul_div_comm, mul_comm (2 - p) p,
      mul_div_mul_right _ _ h2p.ne']
  have key : (1 - p / 2) * (p / (2 - p) + 1) = 1 := by
    rw [mul_add, hhalf]
    ring
  have hthr : 4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by nlinarith) hl0) (sq_nonneg _)
  have hderiv : ∀ θ ∈ Set.Ioo 0 Real.pi, deriv (curveKf p lam) θ < 0 := by
    rintro θ ⟨hθ0, hθ⟩
    have hsign := (onevar hp1 hp2 hl hl1 hθ0 hθ).2
    have hα : 0 < (1 - p / 2) * θ ∧ (1 - p / 2) * θ < Real.pi / (p / (2 - p) + 1) := by
      refine ⟨mul_pos (by linarith) hθ0, ?_⟩
      rw [lt_div_iff₀ hm1]
      calc (1 - p / 2) * θ * (p / (2 - p) + 1) = θ * ((1 - p / 2) * (p / (2 - p) + 1)) := by ring
        _ = θ := by rw [key, mul_one]
        _ < Real.pi := hθ
    have hPsi : 0 < monoPsi (p / (2 - p)) ((1 - p / 2) * θ) :=
      sec5d_Psi_pos_expr_proved (p / (2 - p)) ((1 - p / 2) * θ) hm hα
    have hneg : 4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 -
        monoPsi (p / (2 - p)) ((1 - p / 2) * θ) < 0 := by linarith
    exact sign_eq_neg_one_iff.mp (hsign.trans (sign_eq_neg_one_iff.mpr hneg))
  have hcont : ContinuousOn (curveKf p lam) (Set.Ioo 0 Real.pi) := fun θ hθ =>
    (onevar hp1 hp2 hl hl1 hθ.1 hθ.2).1.continuousAt.continuousWithinAt
  exact strictAntiOn_of_deriv_neg (convex_Ioo 0 Real.pi) hcont (by rwa [interior_Ioo])

end GKSharp

