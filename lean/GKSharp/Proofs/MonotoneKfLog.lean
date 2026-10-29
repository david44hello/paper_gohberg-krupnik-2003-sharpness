/- actual K_f logarithmic form, frozen short v0.70 sec5d:14-15.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotonePiPsi

namespace GKSharp

private theorem gamma_polar_identity (a g : ℝ) (hga : Real.sin (g + a) ≠ 0) :
    (1 : ℂ) - ((Real.sin (g - a) / Real.sin (g + a) : ℝ) : ℂ) *
      Complex.exp (-((2 * a : ℝ) : ℂ) * Complex.I) =
    ((Real.sin (2 * a) / Real.sin (g + a) : ℝ) : ℂ) *
      Complex.exp (((g - a : ℝ) : ℂ) * Complex.I) := by
  have hreal : Real.sin (g + a) - Real.sin (g - a) * Real.cos (2 * a) =
      Real.sin (2 * a) * Real.cos (g - a) := by
    simp only [Real.sin_add,Real.sin_sub,Real.cos_two_mul,Real.sin_two_mul,Real.cos_sub]
    linear_combination -2 * Real.sin g * Real.cos a * Real.sin_sq_add_cos_sq a
  apply Complex.ext <;>
    simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,Complex.exp_re,Complex.exp_im,
      zero_mul,mul_zero,zero_sub,sub_zero,zero_add,add_zero,neg_zero,one_mul,mul_one,
      Real.exp_zero,Real.cos_neg,Real.sin_neg]
  · field_simp [hga]
    convert hreal using 1 <;> ring
  · ring

private theorem gamma_norm_sq (a g : ℝ) (hga : Real.sin (g + a) ≠ 0) :
    ‖(1 : ℂ) - ((Real.sin (g - a) / Real.sin (g + a) : ℝ) : ℂ) *
      Complex.exp (-((2 * a : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
    Real.sin (2 * a) ^ 2 / Real.sin (g + a) ^ 2 := by
  rw [gamma_polar_identity a g hga,norm_mul,Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I,mul_one,Real.norm_eq_abs,sq_abs,div_pow]

theorem sec5d_Kf_log_form_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    curveKf p lam θ = 2 * (1 - lam) * Real.exp (monoLogL p (θ / 2) (curveGamma p lam θ)) ∧
    0 < curveKf p lam θ := by
  let a := θ / 2
  let b := (p - 1) * (θ / 2)
  let g := curveGamma p lam θ
  let r := curveR p lam θ
  let B := ‖1 + (lam : ℂ) * curveZ p lam θ‖ ^ 2
  let Y := 2 * r * Real.sin (p / 2 * θ) - (1 + r ^ 2) * Real.sin ((1 - p / 2) * θ)
  have hlam : 0 < 1 - lam := by linarith
  have h2a : 2 * a = θ := by dsimp [a]; ring
  have h2b : 2 * b = (p - 1) * θ := by dsimp [b]; ring
  have hα : a - b = (1 - p / 2) * θ := by dsimp [a,b]; ring
  have hq : a + b = p / 2 * θ := by dsimp [a,b]; ring
  have hab : 0 < b ∧ b < a ∧ a < Real.pi / 2 := by
    dsimp [a,b]
    refine ⟨mul_pos (by linarith) (half_pos hθ0), ?_, by linarith⟩
    nlinarith
  obtain ⟨hgb,hgpi,hr,-⟩ := sec5d_gamma_spec_proved hp1 hp2 hl hl1 hθ0 hθ
  have hg : b < g ∧ g < Real.pi / 2 := ⟨hgb,hgpi⟩
  change r = Real.sin (g - b) / Real.sin (g + b) at hr
  obtain ⟨hpb,hpa,hmb,-,-⟩ := sec5d_gamma_denominators_proved a b g hab hg
  have hsθ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
  have hs2b : 0 < Real.sin (2 * b) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hab.1]) (by linarith [hab.2.1,hab.2.2])
  obtain ⟨-,-,-,-,-,hr0,hr1,hroot,-⟩ := curve_root_unique hp1 hp2 hθ0 hθ hl hl1
  change 0 < r at hr0
  have hroot' : curveD p lam θ (Real.sin (g - b) / Real.sin (g + b)) = 0 := by
    rw [← hr]
    exact hroot
  have hmu := (sec5d_eq_5_10_proved p lam θ g ⟨hp1,hp2⟩ ⟨hl,hl1⟩ ⟨hθ0,hθ⟩ hg).mp hroot'
  change -lam = Real.sin (g - a) * Real.sin (g + b) /
    (Real.sin (g + a) * Real.sin (g - b)) at hmu
  have hmu' := (eq_div_iff (mul_pos hpa hmb).ne').mp hmu
  have hlamr : lam * r = -(Real.sin (g - a) / Real.sin (g + a)) := by
    rw [hr]
    field_simp [hpb.ne',hpa.ne']
    nlinarith [hmu']
  have hB : B = Real.sin θ ^ 2 / Real.sin (g + a) ^ 2 := by
    dsimp [B,curveZ]
    change ‖1 + (lam : ℂ) * ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I))‖ ^ 2 = _
    rw [← mul_assoc,← Complex.ofReal_mul,hlamr,Complex.ofReal_neg,neg_mul,← sub_eq_add_neg]
    rw [← h2a]
    exact gamma_norm_sq a g hpa.ne'
  have hBpos : 0 < B := by rw [hB]; exact div_pos (sq_pos_of_pos hsθ) (sq_pos_of_pos hpa)
  have hgap : Real.sin (a + b) - r * Real.sin (a - b) =
      Real.sin (2 * b) * Real.sin (g + a) / Real.sin (g + b) := by
    rw [hr]
    field_simp [hpb.ne']
    rw [show b * 2 = 2 * b by ring]
    simp only [Real.sin_add,Real.sin_sub,Real.sin_two_mul]
    ring
  obtain ⟨-,-,-,-,-,hY,hYpos⟩ := dict_identities hp1 hp2 hl.le hl1 hθ0 hθ (rfl : r = curveR p lam θ)
  have hYform : Y = (1 - lam) * Real.sin (g - b) * Real.sin (2 * b) * Real.sin (g + a) /
      Real.sin (g + b) ^ 2 := by
    change Y = (1 - lam) * r * (Real.sin (p / 2 * θ) - r * Real.sin ((1 - p / 2) * θ)) at hY
    rw [hY,← hq,← hα,hgap,hr]
    ring
  change 0 < Y at hYpos
  have hlogr : Real.log r = Real.log (Real.sin (g - b)) - Real.log (Real.sin (g + b)) := by
    rw [hr,Real.log_div hmb.ne' hpb.ne']
  have hlogB : Real.log B = 2 * Real.log (Real.sin θ) - 2 * Real.log (Real.sin (g + a)) := by
    rw [hB,Real.log_div (pow_ne_zero 2 hsθ.ne') (pow_ne_zero 2 hpa.ne'),Real.log_pow,Real.log_pow]
    norm_num
  have hlogY : Real.log Y = Real.log (1 - lam) + Real.log (Real.sin (g - b)) +
      Real.log (Real.sin (2 * b)) + Real.log (Real.sin (g + a)) - 2 * Real.log (Real.sin (g + b)) := by
    rw [hYform,Real.log_div (by positivity) (pow_ne_zero 2 hpb.ne')]
    rw [Real.log_mul (by positivity) hpa.ne',Real.log_mul (by positivity) hs2b.ne',
      Real.log_mul hlam.ne' hmb.ne',Real.log_pow]
    norm_num
  have hKpos := curveKf_positive_proved hp1 hp2 hl hl1 hθ0 hθ
  have hK := curveKf_eq hp1 hp2 hl.le hl1 hθ0 hθ
  change curveKf p lam θ = 2 * (1 - lam) ^ 2 * Real.sin θ * r ^ (2 - p / 2) * B ^ (p / 2 - 1) / Y at hK
  have hlogK : Real.log (curveKf p lam θ) = Real.log 2 + Real.log (1 - lam) + monoLogL p a g := by
    rw [hK,Real.log_div (by positivity) hYpos.ne']
    rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hBpos (p / 2 - 1)).ne',
      Real.log_mul (by positivity) (Real.rpow_pos_of_pos hr0 (2 - p / 2)).ne',
      Real.log_mul (by positivity) hsθ.ne',Real.log_mul (by norm_num) (pow_ne_zero 2 hlam.ne')]
    rw [Real.log_pow,Real.log_rpow hr0,Real.log_rpow hBpos,hlogr,hlogB,hlogY]
    unfold monoLogL
    change _ = Real.log 2 + Real.log (1 - lam) +
      ((1 - p / 2) * Real.log (Real.sin (g - b)) + p / 2 * Real.log (Real.sin (g + b)) +
        (p - 1) * Real.log (Real.sin (2 * a)) - (p - 1) * Real.log (Real.sin (g + a)) - Real.log (Real.sin (2 * b)))
    rw [h2a]
    ring
  have hresult := congrArg Real.exp hlogK
  rw [Real.exp_log hKpos,Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : 0 < (2 : ℝ)),Real.exp_log hlam] at hresult
  exact ⟨hresult,hKpos⟩

end GKSharp

