/- Pi factorization on the actual gamma curve, frozen sec5d:51-55.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneGamma
import GKSharp.Proofs.MonotoneCurveAlgebra

namespace GKSharp

private theorem nu_sigma_products {p θ g : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2) :
    monoNu p θ g + monoSigma p θ g =
      2 * Real.sin (g + θ / 2) * Real.sin (g - (p - 1) * (θ / 2)) ∧
    monoNu p θ g - monoSigma p θ g =
      2 * Real.sin (g - θ / 2) * Real.sin (g + (p - 1) * (θ / 2)) := by
  obtain ⟨hminus,hplus⟩ := sec5d_sigma_cosine_proved hp1 hp2 hθ0 hθ hg
  have ht1 : (g + θ / 2) - (g - (p - 1) * (θ / 2)) = p / 2 * θ := by ring
  have ht2 : (g + θ / 2) + (g - (p - 1) * (θ / 2)) = 2 * g + (1 - p / 2) * θ := by ring
  have ht3 : (g - θ / 2) - (g + (p - 1) * (θ / 2)) = -(p / 2 * θ) := by ring
  have ht4 : (g - θ / 2) + (g + (p - 1) * (θ / 2)) = 2 * g - (1 - p / 2) * θ := by ring
  constructor
  · rw [Real.two_mul_sin_mul_sin,ht1,ht2,hplus]
    unfold monoNu
    ring
  · rw [Real.two_mul_sin_mul_sin,ht3,ht4,Real.cos_neg,hminus]
    unfold monoNu
    ring

theorem sec5d_nu_sigma_relation_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    -lam = (monoNu p θ (curveGamma p lam θ) - monoSigma p θ (curveGamma p lam θ)) /
      (monoNu p θ (curveGamma p lam θ) + monoSigma p θ (curveGamma p lam θ)) ∧
    monoNu p θ (curveGamma p lam θ) = (1 - lam) / (1 + lam) * monoSigma p θ (curveGamma p lam θ) ∧
    monoNu p θ (curveGamma p lam θ) + monoSigma p θ (curveGamma p lam θ) =
      2 * Real.sin (curveGamma p lam θ + θ / 2) * Real.sin (curveGamma p lam θ - (p - 1) * (θ / 2)) ∧
    0 < monoNu p θ (curveGamma p lam θ) + monoSigma p θ (curveGamma p lam θ) := by
  let g := curveGamma p lam θ
  obtain ⟨hgb,hgpi,hr,-⟩ := sec5d_gamma_spec_proved hp1 hp2 hl hl1 hθ0 hθ
  have hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2 := ⟨hgb,hgpi⟩
  have hab : 0 < (p - 1) * (θ / 2) ∧ (p - 1) * (θ / 2) < θ / 2 ∧ θ / 2 < Real.pi / 2 := by
    refine ⟨mul_pos (by linarith) (half_pos hθ0), ?_, by linarith⟩
    nlinarith
  obtain ⟨hpb,hpa,hmb,-,-⟩ := sec5d_gamma_denominators_proved (θ / 2) ((p - 1) * (θ / 2)) g hab hg
  obtain ⟨hplus,hminus⟩ := nu_sigma_products hp1 hp2 hθ0 hθ hg
  have hden : 0 < Real.sin (g + θ / 2) * Real.sin (g - (p - 1) * (θ / 2)) := mul_pos hpa hmb
  have hpositive : 0 < monoNu p θ g + monoSigma p θ g := by rw [hplus]; positivity
  obtain ⟨-,-,-,-,-,-,-,hroot,-⟩ := curve_root_unique hp1 hp2 hθ0 hθ hl hl1
  rw [hr] at hroot
  have hmu := (sec5d_eq_5_10_proved p lam θ g ⟨hp1,hp2⟩ ⟨hl,hl1⟩ ⟨hθ0,hθ⟩ hg).mp hroot
  have hratio : -lam = (monoNu p θ g - monoSigma p θ g) / (monoNu p θ g + monoSigma p θ g) := by
    rw [hplus,hminus,hmu]
    field_simp [hpa.ne',hmb.ne']
  have hlinear := (eq_div_iff hpositive.ne').mp hratio
  refine ⟨hratio,?_,hplus,hpositive⟩
  have hlam : 1 + lam ≠ 0 := by linarith
  field_simp [hlam]
  nlinarith [hlinear]

theorem sec5d_factorization_dictionary_proved {p θ g : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2) :
    Real.cos (p / 2 * θ) ^ 2 + Real.cos ((1 - p / 2) * θ) ^ 2 -
        2 * Real.cos (p / 2 * θ) * Real.cos ((1 - p / 2) * θ) * Real.cos (2 * g) =
      monoNu p θ g ^ 2 + monoSigma p θ g ^ 2 * Real.cot ((1 - p / 2) * θ) ^ 2 ∧
    Real.cos (p / 2 * θ) / Real.cos ((1 - p / 2) * θ) - Real.cos (2 * g) =
      monoNu p θ g / Real.cos ((1 - p / 2) * θ) ∧
    (1 - (p - 1)) ^ 2 * Real.sin θ * Real.sin ((p - 1) * θ) - monoW (p - 1) θ =
      (p - 1) * Real.sin (2 * ((1 - p / 2) * θ)) ^ 2 := by
  have hs : 0 < Real.sin ((1 - p / 2) * θ) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos (by linarith) hθ0) (by nlinarith [Real.pi_pos])
  have hc := (sec5d_trig_dictionary_proved p θ ⟨hp1,hp2⟩ ⟨hθ0,hθ⟩).1
  have hx : 0 ≤ 1 - Real.cos (2 * g) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * g),sq_nonneg (Real.sin (2 * g))]
  have hsig : monoSigma p θ g ^ 2 * Real.cot ((1 - p / 2) * θ) ^ 2 =
      (1 - Real.cos (2 * g) ^ 2) * Real.cos ((1 - p / 2) * θ) ^ 2 := by
    unfold monoSigma
    rw [mul_pow,Real.sq_sqrt hx,Real.cot_eq_cos_div_sin]
    generalize Real.sin ((1 - p / 2) * θ) = sval at *
    generalize Real.cos ((1 - p / 2) * θ) = dval at *
    field_simp [hs.ne']
  refine ⟨?_,?_,?_⟩
  · rw [hsig]
    unfold monoNu
    ring
  · unfold monoNu
    generalize Real.cos ((1 - p / 2) * θ) = dval at *
    field_simp [hc.ne']
  · unfold monoW
    rw [show (1 - (p - 1)) * θ = 2 * ((1 - p / 2) * θ) by ring]
    ring

end GKSharp

