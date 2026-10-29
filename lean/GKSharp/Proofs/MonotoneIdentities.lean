/- exact identities (5.10), (5.11) and W/Psi; frozen sec5d:13-59.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Monotonicity
import GKSharp.Proofs.MonotoneElementary

namespace GKSharp

private theorem sine_product_aux (x y : ℝ) :
    Real.sin (x + y) * Real.sin (x - y) = Real.sin x ^ 2 - Real.sin y ^ 2 := by
  rw [Real.sin_add, Real.sin_sub]
  linear_combination Real.sin x ^ 2 * Real.sin_sq_add_cos_sq y -
    Real.sin y ^ 2 * Real.sin_sq_add_cos_sq x

theorem sec5d_trig_dictionary_proved (p θ : ℝ) (hp : 1 < p ∧ p < 2)
    (hθ : 0 < θ ∧ θ < Real.pi) :
    0 < Real.cos ((1 - p / 2) * θ) ∧
    Real.cos ((1 - p / 2) * θ) ^ 2 - Real.cos (p / 2 * θ) ^ 2 =
      Real.sin θ * Real.sin ((p - 1) * θ) ∧
    Real.sin ((1 - (p - 1)) * θ) * Real.cos (p / 2 * θ) /
      Real.cos ((1 - p / 2) * θ) = Real.sin θ - Real.sin ((p - 1) * θ) := by
  let a := (1 - p / 2) * θ
  let b := p / 2 * θ
  have ha0 : 0 < a := mul_pos (by linarith [hp.2]) hθ.1
  have halt : a < Real.pi / 2 := by dsimp [a]; nlinarith [hp.1, hθ.1, hθ.2]
  have hc : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], halt⟩
  have ht : θ = b + a := by dsimp [a,b]; ring
  have he : (p - 1) * θ = b - a := by dsimp [a,b]; ring
  have hu : (1 - (p - 1)) * θ = 2 * a := by dsimp [a]; ring
  change 0 < Real.cos a ∧ Real.cos a ^ 2 - Real.cos b ^ 2 = _ ∧ _
  refine ⟨hc, ?_, ?_⟩
  · rw [he, ht, sine_product_aux]
    nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]
  · change Real.sin ((1 - (p - 1)) * θ) * Real.cos b / Real.cos a = _
    rw [hu, he, ht, Real.sin_two_mul, Real.sin_add, Real.sin_sub]
    field_simp [hc.ne']
    <;> ring

theorem sec5d_eq_5_10_proved (p lam θ γ : ℝ) (hp : 1 < p ∧ p < 2)
    (hlam : -1 < lam ∧ lam < 1) (hθ : 0 < θ ∧ θ < Real.pi)
    (hγ : (p - 1) * (θ / 2) < γ ∧ γ < Real.pi / 2) :
    curveD p lam θ
      (Real.sin (γ - (p - 1) * (θ / 2)) / Real.sin (γ + (p - 1) * (θ / 2))) = 0 ↔
    -lam = (Real.sin (γ - θ / 2) * Real.sin (γ + (p - 1) * (θ / 2))) /
      (Real.sin (γ + θ / 2) * Real.sin (γ - (p - 1) * (θ / 2))) := by
  let a := θ / 2
  let b := (p - 1) * (θ / 2)
  have hab : 0 < b ∧ b < a ∧ a < Real.pi / 2 := by
    dsimp [a,b]; constructor
    · exact mul_pos (by linarith [hp.1]) (half_pos hθ.1)
    · constructor <;> nlinarith [hp.1, hp.2, hθ.1, hθ.2]
  obtain ⟨hplus, hga, hminus, -, -⟩ := sec5d_gamma_denominators_proved a b γ hab hγ
  have hsin2 : 0 < Real.sin (2 * b) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hab.1]) (by linarith [hab.2.1,hab.2.2])
  have h1 : Real.sin (γ - b) * Real.sin (a + b) - Real.sin (γ + b) * Real.sin (a - b) =
      Real.sin (2 * b) * Real.sin (γ - a) := by
    simp only [Real.sin_add, Real.sin_sub, Real.sin_two_mul]; ring
  have h2 : Real.sin (γ + b) * Real.sin (a + b) - Real.sin (γ - b) * Real.sin (a - b) =
      Real.sin (2 * b) * Real.sin (γ + a) := by
    simp only [Real.sin_add, Real.sin_sub, Real.sin_two_mul]; ring
  have ht1 : p / 2 * θ = a + b := by dsimp [a,b]; ring
  have ht2 : (1 - p / 2) * θ = a - b := by dsimp [a,b]; ring
  have hfactor : curveD p lam θ (Real.sin (γ - b) / Real.sin (γ + b)) =
      Real.sin (2 * b) * (lam * Real.sin (γ - b) * Real.sin (γ + a) +
        Real.sin (γ + b) * Real.sin (γ - a)) / Real.sin (γ + b) ^ 2 := by
    unfold curveD
    rw [ht1,ht2]
    field_simp [hplus.ne']
    simp only [mul_comm b (2 : ℝ)]
    linear_combination lam * Real.sin (γ - b) * h2 + Real.sin (γ + b) * h1
  change curveD p lam θ (Real.sin (γ - b) / Real.sin (γ + b)) = 0 ↔
    -lam = Real.sin (γ - a) * Real.sin (γ + b) / (Real.sin (γ + a) * Real.sin (γ - b))
  rw [hfactor, eq_div_iff (mul_ne_zero hga.ne' hminus.ne')]
  constructor
  · intro h
    have hz := congrArg (fun x : ℝ => x * Real.sin (γ + b) ^ 2) h
    field_simp [hplus.ne'] at hz
    simp only [mul_zero] at hz
    have hn := (mul_eq_zero.mp hz).resolve_left hsin2.ne'
    nlinarith [hn]
  · intro h
    have hn : lam * Real.sin (γ - b) * Real.sin (γ + a) +
        Real.sin (γ + b) * Real.sin (γ - a) = 0 := by nlinarith [h]
    rw [hn,mul_zero,zero_div]

private theorem pi_identity_aux (e s1 s2 s3 c d k X : ℝ) (hd : d ≠ 0)
    (hprod : d ^ 2 - c ^ 2 = s1 * s2) (hgap : s3 * c = (s1 - s2) * d)
    (hdouble : s3 ^ 2 = 2 * (1 - k) * d ^ 2) :
    -(1 - e) ^ 2 * s1 * s2 * X ^ 2 + 2 * e * s3 * (s1 - s2) * X +
      (1 + e ^ 2) * s1 * s2 - 2 * e * s1 * s2 * k - 2 * e * s3 ^ 2 =
      ((1 - e) ^ 2 * s1 * s2 - e * s3 ^ 2) / d ^ 2 *
        (c ^ 2 + d ^ 2 - 2 * c * d * X) -
        (1 - e) ^ 2 * s1 * s2 * (X - c / d) ^ 2 := by
  field_simp [hd]
  linear_combination -2 * e * d * s3 * X * hgap - e * s1 * s2 * hdouble - e * s3 ^ 2 * hprod

theorem sec5d_eq_5_11_proved (p θ X : ℝ) (hp : 1 < p ∧ p < 2)
    (hθ : 0 < θ ∧ θ < Real.pi) :
    monoPi (p - 1) θ X =
      monoW (p - 1) θ / Real.cos ((1 - p / 2) * θ) ^ 2 *
        (Real.cos (p / 2 * θ) ^ 2 + Real.cos ((1 - p / 2) * θ) ^ 2 -
          2 * Real.cos (p / 2 * θ) * Real.cos ((1 - p / 2) * θ) * X) -
      (1 - (p - 1)) ^ 2 * Real.sin θ * Real.sin ((p - 1) * θ) *
        (X - Real.cos (p / 2 * θ) / Real.cos ((1 - p / 2) * θ)) ^ 2 := by
  obtain ⟨hd,hprod,hgap⟩ := sec5d_trig_dictionary_proved p θ hp hθ
  have hgap' := (div_eq_iff hd.ne').mp hgap
  have hdouble : Real.sin ((1 - (p - 1)) * θ) ^ 2 =
      2 * (1 - Real.cos ((1 - (p - 1)) * θ)) * Real.cos ((1 - p / 2) * θ) ^ 2 := by
    rw [show (1 - (p - 1)) * θ = 2 * ((1 - p / 2) * θ) by ring,
      Real.sin_two_mul, Real.cos_two_mul]
    linear_combination 4 * Real.cos ((1 - p / 2) * θ) ^ 2 *
      Real.sin_sq_add_cos_sq ((1 - p / 2) * θ)
  exact pi_identity_aux (p - 1) (Real.sin θ) (Real.sin ((p - 1) * θ))
    (Real.sin ((1 - (p - 1)) * θ)) (Real.cos (p / 2 * θ)) (Real.cos ((1 - p / 2) * θ))
    (Real.cos ((1 - (p - 1)) * θ)) X hd.ne' hprod hgap' hdouble

theorem sec5d_W_Psi_identity_proved (m α : ℝ) (hm : 1 < m)
    (hα : 0 < α ∧ α < Real.pi / (m + 1)) :
    monoW ((m - 1) / (m + 1)) ((m + 1) * α) /
      (4 * ((m - 1) / (m + 1)) * Real.sin α ^ 4) =
        1 - monoPsi m α / (m ^ 2 - 1) := by
  have hm1 : m + 1 ≠ 0 := by linarith
  have hm2 : m ^ 2 - 1 ≠ 0 := by nlinarith
  have hm0 : m - 1 ≠ 0 := by linarith
  have hαpi : α < Real.pi := by
    have h := (lt_div_iff₀ (show 0 < m + 1 by linarith)).mp hα.2
    nlinarith [hα.1, mul_pos (sub_pos.mpr hm) hα.1]
  have hs : Real.sin α ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hα.1 hαpi).ne'
  have he : (m - 1) / (m + 1) * ((m + 1) * α) = (m - 1) * α := by field_simp
  have hu : (1 - (m - 1) / (m + 1)) * ((m + 1) * α) = 2 * α := by field_simp; ring
  unfold monoW monoPsi
  rw [he, hu, mul_assoc ((1 - (m - 1) / (m + 1)) ^ 2)
    (Real.sin ((m + 1) * α)) (Real.sin ((m - 1) * α)),
    sec5d_sine_product_proved, Real.sin_two_mul]
  simp only [mul_pow]
  rw [show Real.cos α ^ 2 = 1 - Real.sin α ^ 2 by nlinarith [Real.sin_sq_add_cos_sq α]]
  field_simp [hm1,hm2,hm0,hs]
  <;> ring

end GKSharp
