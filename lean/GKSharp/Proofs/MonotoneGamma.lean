/- canonical gamma coordinate, frozen short v0.70 sec5d:9-13.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.MonotonicityCurve
import GKSharp.Proofs.CriticalCurve
import GKSharp.Proofs.MonotoneElementary
import GKSharp.Proofs.MonotoneIdentities

namespace GKSharp

private theorem ratio_tan_iff {b g r : ℝ} (hcg : Real.cos g ≠ 0)
    (hcb : Real.cos b ≠ 0) (hsgb : Real.sin (g + b) ≠ 0) (hr : 1 - r ≠ 0) :
    r = Real.sin (g - b) / Real.sin (g + b) ↔
      Real.tan g = Real.tan b * (1 + r) / (1 - r) := by
  rw [eq_div_iff hsgb, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos,
    Real.sin_add, Real.sin_sub]
  field_simp [hcg,hcb,hr]
  constructor <;> intro hh <;> nlinarith [hh]

theorem sec5d_gamma_spec_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (p - 1) * (θ / 2) < curveGamma p lam θ ∧ curveGamma p lam θ < Real.pi / 2 ∧
    curveR p lam θ = Real.sin (curveGamma p lam θ - (p - 1) * (θ / 2)) /
      Real.sin (curveGamma p lam θ + (p - 1) * (θ / 2)) ∧
    ∀ g ∈ Set.Ioo ((p - 1) * (θ / 2)) (Real.pi / 2),
      curveR p lam θ = Real.sin (g - (p - 1) * (θ / 2)) / Real.sin (g + (p - 1) * (θ / 2)) →
        g = curveGamma p lam θ := by
  let b := (p - 1) * (θ / 2)
  let r := curveR p lam θ
  have hb : 0 < b := mul_pos (by linarith) (half_pos hθ0)
  have hbpi : b < Real.pi / 2 := by dsimp [b]; nlinarith
  obtain ⟨-, -, -, -, -, hr0, hr1, -, -⟩ := curve_root_unique hp1 hp2 hθ0 hθ hl hl1
  change 0 < r at hr0
  change r < 1 at hr1
  have hc : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hbpi⟩
  have ht : 0 < Real.tan b := Real.tan_pos_of_pos_of_lt_pi_div_two hb hbpi
  have harg : Real.tan b < Real.tan b * (1 + r) / (1 - r) := by
    apply (lt_div_iff₀ (by linarith : 0 < 1 - r)).mpr
    nlinarith [mul_pos ht hr0]
  have hgb : b < curveGamma p lam θ := by
    change b < Real.arctan (Real.tan b * (1 + r) / (1 - r))
    have hh := Real.arctan_strictMono harg
    rwa [Real.arctan_tan (by linarith [Real.pi_pos]) hbpi] at hh
  have hgpi : curveGamma p lam θ < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hgc : Real.cos (curveGamma p lam θ) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hgpi⟩).ne'
  have hsg : Real.sin (curveGamma p lam θ + b) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hrepr : r = Real.sin (curveGamma p lam θ - b) / Real.sin (curveGamma p lam θ + b) := by
    apply (ratio_tan_iff hgc hc.ne' hsg (by linarith)).mpr
    exact Real.tan_arctan _
  refine ⟨hgb,hgpi,hrepr,?_⟩
  intro g hg heq
  change b < g ∧ g < Real.pi / 2 at hg
  have hcg : Real.cos g ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hg.2⟩).ne'
  have hsgb : Real.sin (g + b) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hg.1]) (by linarith [hg.2])).ne'
  have htan := (ratio_tan_iff hcg hc.ne' hsgb (by linarith : 1 - r ≠ 0)).mp heq
  have hatan := congrArg Real.arctan htan
  rw [Real.arctan_tan (by linarith [Real.pi_pos]) hg.2] at hatan
  exact hatan

theorem sec5d_lambda_gamma_sign_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (lam < 0 ↔ θ / 2 < curveGamma p lam θ) ∧
    (lam = 0 ↔ curveGamma p lam θ = θ / 2) ∧
    (0 < lam ↔ curveGamma p lam θ < θ / 2) := by
  let a := θ / 2
  let b := (p - 1) * (θ / 2)
  let g := curveGamma p lam θ
  obtain ⟨hgb,hgpi,hr,-⟩ := sec5d_gamma_spec_proved hp1 hp2 hl hl1 hθ0 hθ
  have hab : 0 < b ∧ b < a ∧ a < Real.pi / 2 := by
    dsimp [a,b]
    refine ⟨mul_pos (by linarith) (half_pos hθ0), ?_, by linarith⟩
    nlinarith
  have hg : b < g ∧ g < Real.pi / 2 := ⟨hgb,hgpi⟩
  obtain ⟨hpb,hpa,hmb,-,-⟩ := sec5d_gamma_denominators_proved a b g hab hg
  obtain ⟨-,-,-,-,-,-,-,hroot,-⟩ := curve_root_unique hp1 hp2 hθ0 hθ hl hl1
  rw [hr] at hroot
  have hmu := (sec5d_eq_5_10_proved p lam θ g ⟨hp1,hp2⟩ ⟨hl,hl1⟩ ⟨hθ0,hθ⟩ hg).mp hroot
  change -lam = Real.sin (g - a) * Real.sin (g + b) /
    (Real.sin (g + a) * Real.sin (g - b)) at hmu
  have hden : 0 < Real.sin (g + a) * Real.sin (g - b) := mul_pos hpa hmb
  have heq := (eq_div_iff hden.ne').mp hmu
  have hg0 : 0 < g := lt_trans hab.1 hg.1
  have ha0 : 0 < a := lt_trans hab.1 hab.2.1
  change (lam < 0 ↔ a < g) ∧ (lam = 0 ↔ g = a) ∧ (0 < lam ↔ g < a)
  rcases lt_trichotomy g a with hlt | he | hgt
  · have hsin : Real.sin (g - a) < 0 := by
      have hh := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hlt)
        (show a - g < Real.pi by linarith [hab.2.2, Real.pi_pos])
      rw [show g - a = -(a - g) by ring, Real.sin_neg]
      linarith
    have hlam_sign : 0 < lam := by nlinarith [mul_neg_of_neg_of_pos hsin hpb]
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> intro hh <;> linarith
  · have hs : Real.sin (g - a) = 0 := by rw [he,sub_self,Real.sin_zero]
    have hlam_sign : lam = 0 := by rw [hs,zero_mul] at heq; nlinarith
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> intro hh <;> linarith
  · have hsin : 0 < Real.sin (g - a) := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hgt)
        (by linarith [hg.2,Real.pi_pos])
    have hlam_sign : lam < 0 := by nlinarith [mul_pos hsin hpb]
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> intro hh <;> linarith

end GKSharp

