/- logarithmic level derivative, frozen short v0.70 sec5d:30.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneCurveAlgebra
import GKSharp.Proofs.MonotoneGamma

namespace GKSharp

private theorem logsin_shift (g c : ℝ) (h : Real.sin (g + c) ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log (Real.sin (x + c))) (Real.cot (g + c)) g := by
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (x + c)) (Real.cos (g + c)) g := by
    simpa using ((hasDerivAt_id g).add_const c).sin
  simpa only [Real.cot_eq_cos_div_sin] using hsin.log h

private theorem sine_sum_products (g a b : ℝ) :
    Real.sin (g + a) * Real.sin (g + b) + Real.sin (g - a) * Real.sin (g - b) =
      Real.cos (a - b) - Real.cos (2 * g) * Real.cos (a + b) := by
  have hp := Real.two_mul_sin_mul_sin (g + a) (g + b)
  have hm := Real.two_mul_sin_mul_sin (g - a) (g - b)
  rw [show (g + a) - (g + b) = a - b by ring,
    show (g + a) + (g + b) = 2 * g + (a + b) by ring] at hp
  rw [show (g - a) - (g - b) = -(a - b) by ring,
    show (g - a) + (g - b) = 2 * g - (a + b) by ring,Real.cos_neg] at hm
  simp only [Real.cos_add,Real.cos_sub] at hp hm ⊢
  nlinarith

theorem sec5d_M_level_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hl0 : lam ≠ 0) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    monoLogM p (θ / 2) (curveGamma p lam θ) = Real.log |lam| := by
  let a := θ / 2
  let b := (p - 1) * (θ / 2)
  let g := curveGamma p lam θ
  obtain ⟨hgb,hgpi,hr,-⟩ := sec5d_gamma_spec_proved hp1 hp2 hl hl1 hθ0 hθ
  have hg : b < g ∧ g < Real.pi / 2 := ⟨hgb,hgpi⟩
  have hab : 0 < b ∧ b < a ∧ a < Real.pi / 2 := by
    dsimp [a,b]
    refine ⟨mul_pos (by linarith) (half_pos hθ0), ?_, by linarith⟩
    nlinarith
  obtain ⟨hpb,hpa,hmb,-,-⟩ := sec5d_gamma_denominators_proved a b g hab hg
  obtain ⟨-,-,-,-,-,-,-,hroot,-⟩ := curve_root_unique hp1 hp2 hθ0 hθ hl hl1
  rw [hr] at hroot
  have hmu := (sec5d_eq_5_10_proved p lam θ g ⟨hp1,hp2⟩ ⟨hl,hl1⟩ ⟨hθ0,hθ⟩ hg).mp hroot
  change -lam = Real.sin (g - a) * Real.sin (g + b) /
    (Real.sin (g + a) * Real.sin (g - b)) at hmu
  have hma : Real.sin (g - a) ≠ 0 := by
    intro hh
    rw [hh,zero_mul,zero_div] at hmu
    exact hl0 (neg_eq_zero.mp hmu)
  have hlog := congrArg Real.log hmu
  rw [Real.log_neg_eq_log,Real.log_div (mul_ne_zero hma hpb.ne') (mul_ne_zero hpa.ne' hmb.ne'),
    Real.log_mul hma hpb.ne',Real.log_mul hpa.ne' hmb.ne'] at hlog
  unfold monoLogM
  simp only [Real.log_abs]
  change Real.log (Real.sin (g - a)) + Real.log (Real.sin (g + b)) -
    Real.log (Real.sin (g + a)) - Real.log (Real.sin (g - b)) = Real.log lam
  linarith [hlog]

theorem sec5d_M_gamma_formula_proved {p θ g : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2) (hga : g ≠ θ / 2) :
    HasDerivAt (monoLogM p (θ / 2))
      (Real.sin ((1 - p / 2) * θ) *
        (Real.cos ((1 - p / 2) * θ) - Real.cos (2 * g) * Real.cos (p / 2 * θ)) /
        monoS p (θ / 2) g) g ∧
    deriv (monoLogM p (θ / 2)) g = Real.sin ((1 - p / 2) * θ) *
      (Real.sin (g + θ / 2) * Real.sin (g + (p - 1) * (θ / 2)) +
        Real.sin (g - θ / 2) * Real.sin (g - (p - 1) * (θ / 2))) / monoS p (θ / 2) g := by
  let a := θ / 2
  let b := (p - 1) * (θ / 2)
  have hab : 0 < b ∧ b < a ∧ a < Real.pi / 2 := by
    dsimp [a,b]
    refine ⟨mul_pos (by linarith) (half_pos hθ0), ?_, by linarith⟩
    nlinarith
  obtain ⟨hpb,hpa,hmb,-,-⟩ := sec5d_gamma_denominators_proved a b g hab hg
  have hg0 : 0 < g := lt_trans hab.1 hg.1
  have hma : Real.sin (g - a) ≠ 0 := by
    have he := Real.sin_eq_zero_iff_of_lt_of_lt (x := g - a)
      (by linarith [hab.2.2,Real.pi_pos]) (by linarith [hg.2,hab.1,hab.2.1,Real.pi_pos])
    exact fun hh => hga (sub_eq_zero.mp (he.mp hh))
  have hd1 := logsin_shift g (-a) (by simpa only [← sub_eq_add_neg] using hma)
  have hd2 := logsin_shift g b hpb.ne'
  have hd3 := logsin_shift g a hpa.ne'
  have hd4 := logsin_shift g (-b) (by simpa only [← sub_eq_add_neg] using hmb.ne')
  have hd : HasDerivAt (monoLogM p a)
      (Real.cot (g - a) + Real.cot (g + b) - Real.cot (g + a) - Real.cot (g - b)) g := by
    convert ((hd1.add hd2).sub hd3).sub hd4 using 1
    · funext x
      simp [monoLogM,a,b,Real.log_abs,sub_eq_add_neg]
  have h1 := sec5d_cot_difference_proved (g - a) (g - b) hma hmb.ne'
  have h2 := sec5d_cot_difference_proved (g + b) (g + a) hpb.ne' hpa.ne'
  rw [show (g - b) - (g - a) = a - b by ring] at h1
  rw [show (g + a) - (g + b) = a - b by ring] at h2
  have hcot : Real.cot (g - a) + Real.cot (g + b) - Real.cot (g + a) - Real.cot (g - b) =
      Real.sin (a - b) * (Real.sin (g + a) * Real.sin (g + b) +
        Real.sin (g - a) * Real.sin (g - b)) / monoS p a g := by
    calc
      _ = (Real.cot (g - a) - Real.cot (g - b)) + (Real.cot (g + b) - Real.cot (g + a)) := by ring
      _ = _ := by
        rw [h1,h2]
        unfold monoS
        change _ = Real.sin (a - b) * _ /
          (Real.sin (g - a) * Real.sin (g + a) * Real.sin (g - b) * Real.sin (g + b))
        generalize Real.sin (g - a) = sma at *
        generalize Real.sin (g + a) = spa at *
        generalize Real.sin (g - b) = smb at *
        generalize Real.sin (g + b) = spb at *
        field_simp [hma,hpa.ne',hmb.ne',hpb.ne']
        <;> ring
  have hα : a - b = (1 - p / 2) * θ := by dsimp [a,b]; ring
  have hq : a + b = p / 2 * θ := by dsimp [a,b]; ring
  have hsum := sine_sum_products g a b
  rw [hα,hq] at hsum
  rw [hcot,hα] at hd
  refine ⟨?_,hd.deriv⟩
  rw [hsum] at hd
  exact hd

theorem sec5d_positive_lambda_signs_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : 0 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    monoS p (θ / 2) (curveGamma p lam θ) < 0 ∧
    deriv (monoLogM p (θ / 2)) (curveGamma p lam θ) < 0 := by
  have hlm : -1 < lam := by linarith
  let a := θ / 2
  let b := (p - 1) * (θ / 2)
  let g := curveGamma p lam θ
  obtain ⟨hgb,hgpi,-,-⟩ := sec5d_gamma_spec_proved hp1 hp2 hlm hl1 hθ0 hθ
  have hg : b < g ∧ g < Real.pi / 2 := ⟨hgb,hgpi⟩
  have hga : g < a := (sec5d_lambda_gamma_sign_proved hp1 hp2 hlm hl1 hθ0 hθ).2.2.mp hl
  have hab : 0 < b ∧ b < a ∧ a < Real.pi / 2 := by
    dsimp [a,b]
    refine ⟨mul_pos (by linarith) (half_pos hθ0), ?_, by linarith⟩
    nlinarith
  obtain ⟨hpb,hpa,hmb,-,-⟩ := sec5d_gamma_denominators_proved a b g hab hg
  have hg0 : 0 < g := lt_trans hab.1 hg.1
  have hma : Real.sin (g - a) < 0 := by
    have hh := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hga)
      (show a - g < Real.pi by linarith [hab.2.2,Real.pi_pos])
    rw [show g - a = -(a - g) by ring,Real.sin_neg]
    linarith
  have hS : monoS p a g < 0 := by
    unfold monoS
    change Real.sin (g - a) * Real.sin (g + a) * Real.sin (g - b) * Real.sin (g + b) < 0
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hma hpa) hmb) hpb
  refine ⟨hS,?_⟩
  have hformula := (sec5d_M_gamma_formula_proved hp1 hp2 hθ0 hθ hg hga.ne).1.deriv
  rw [hformula]
  have hs : 0 < Real.sin ((1 - p / 2) * θ) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos (by linarith) hθ0) (by nlinarith [Real.pi_pos])
  have hX : |Real.cos (2 * g)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have hgap := (sec5d_denominator_positive_proved hp1 hp2 hθ0 hθ hX).1
  exact div_neg_of_pos_of_neg (mul_pos hs hgap) hS

end GKSharp

