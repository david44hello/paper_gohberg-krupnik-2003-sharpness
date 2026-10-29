/- final Pi factorization, frozen short v0.70 sec5d:55.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneFactorization

namespace GKSharp

private theorem factor_aux (C D X N S W A e t s : ℝ) (hD : D ≠ 0) (hs : s ≠ 0)
    (hblock : C ^ 2 + D ^ 2 - 2 * C * D * X = N ^ 2 + S ^ 2 * (D / s) ^ 2)
    (hdiff : C / D - X = N / D) (hN : N = t * S) (hA : A - W = e * (2 * s * D) ^ 2) :
    W / D ^ 2 * (C ^ 2 + D ^ 2 - 2 * C * D * X) - A * (X - C / D) ^ 2 =
      S ^ 2 * (D / s) ^ 2 / D ^ 2 * (W - 4 * e * t ^ 2 * s ^ 4) := by
  rw [hblock,show X - C / D = -(N / D) by linarith [hdiff],neg_sq,hN]
  rw [show A = W + e * (2 * s * D) ^ 2 by linarith [hA]]
  field_simp [hD,hs]
  <;> ring

theorem sec5d_Pi_factorization_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ)) =
      monoPiPrefactor p θ (curveGamma p lam θ) *
        (monoW (p - 1) θ - 4 * (p - 1) * ((1 - lam) / (1 + lam)) ^ 2 * Real.sin ((1 - p / 2) * θ) ^ 4) ∧
    0 < monoPiPrefactor p θ (curveGamma p lam θ) := by
  let g := curveGamma p lam θ
  obtain ⟨hgb,hgpi,-,-⟩ := sec5d_gamma_spec_proved hp1 hp2 hl hl1 hθ0 hθ
  have hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2 := ⟨hgb,hgpi⟩
  have hg0 : 0 < g := lt_trans (mul_pos (by linarith) (half_pos hθ0)) hg.1
  have hs : 0 < Real.sin ((1 - p / 2) * θ) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos (by linarith) hθ0) (by nlinarith [Real.pi_pos])
  have hc := (sec5d_trig_dictionary_proved p θ ⟨hp1,hp2⟩ ⟨hθ0,hθ⟩).1
  obtain ⟨hblock,hdiff,hA⟩ := sec5d_factorization_dictionary_proved hp1 hp2 hθ0 hθ hg
  have hN := (sec5d_nu_sigma_relation_proved hp1 hp2 hl hl1 hθ0 hθ).2.1
  have heq := sec5d_eq_5_11_proved p θ (Real.cos (2 * g)) ⟨hp1,hp2⟩ ⟨hθ0,hθ⟩
  constructor
  · change monoPi (p - 1) θ (Real.cos (2 * g)) = _
    rw [heq]
    unfold monoPiPrefactor
    rw [Real.cot_eq_cos_div_sin] at hblock ⊢
    rw [Real.sin_two_mul] at hA
    exact factor_aux _ _ _ _ _ _ _ _ _ _ hc.ne' hs.ne' hblock hdiff hN hA
  · have hsg : 0 < Real.sin (2 * g) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hg.2])
    have hroot : 0 < Real.sqrt (1 - Real.cos (2 * g) ^ 2) := by
      apply Real.sqrt_pos.mpr
      nlinarith [Real.sin_sq_add_cos_sq (2 * g),sq_pos_of_pos hsg]
    have hsig : 0 < monoSigma p θ g := mul_pos hroot hs
    have hcot : 0 < Real.cot ((1 - p / 2) * θ) := by
      rw [Real.cot_eq_cos_div_sin]
      exact div_pos hc hs
    exact div_pos (mul_pos (sq_pos_of_pos hsig) (sq_pos_of_pos hcot)) (sq_pos_of_pos hc)

end GKSharp

