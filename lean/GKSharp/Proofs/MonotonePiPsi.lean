/- Pi/Psi sign identity, frozen short v0.70 sec5d:57-58.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotonePi
import GKSharp.Proofs.CurveK

namespace GKSharp

open Filter Topology

theorem curveKf_positive_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    0 < curveKf p lam θ := by
  obtain ⟨-,-,-,-,-,hr0,hr1,-,-⟩ := curve_root_unique hp1 hp2 hθ0 hθ hl hl1
  have hz : ‖curveZ p lam θ‖ = curveR p lam θ := by
    simp [curveZ,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0,
      Complex.norm_exp]
  have hlabs : |lam| < 1 := abs_lt.mpr ⟨hl,hl1⟩
  have hsmall : ‖(lam : ℂ) * curveZ p lam θ‖ < 1 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,hz]
    calc
      |lam| * curveR p lam θ ≤ 1 * curveR p lam θ := mul_le_mul_of_nonneg_right hlabs.le hr0.le
      _ < 1 := by simpa using hr1
  have hne : 1 + (lam : ℂ) * curveZ p lam θ ≠ 0 := by
    intro hh
    have he : (lam : ℂ) * curveZ p lam θ = -1 := by linear_combination hh
    rw [he] at hsmall
    norm_num at hsmall
  have hB : 0 < ‖1 + (lam : ℂ) * curveZ p lam θ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hY := (dict_identities hp1 hp2 hl.le hl1 hθ0 hθ (rfl : curveR p lam θ = curveR p lam θ)).2.2.2.2.2.2
  rw [curveKf_eq hp1 hp2 hl.le hl1 hθ0 hθ]
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
  have hrp := Real.rpow_pos_of_pos hr0 (2 - p / 2)
  have hBp := Real.rpow_pos_of_pos hB (p / 2 - 1)
  exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num)
    (sq_pos_of_pos (by linarith : 0 < 1 - lam))) hs) hrp) hBp) hY

private theorem bracket_factor (W B e s q t v : ℝ) (hq : q ≠ 0) (hes : 4 * e * s ^ 4 ≠ 0)
    (hW : W / (4 * e * s ^ 4) = 1 - B / q) (ht : 1 - t ^ 2 = v) :
    W - 4 * e * t ^ 2 * s ^ 4 = (4 * e * s ^ 4 / q) * (q * v - B) := by
  rw [show W = (1 - B / q) * (4 * e * s ^ 4) from (div_eq_iff hes).mp hW,← ht]
  field_simp [hq]
  <;> ring

theorem sec5d_Pi_Psi_sign_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    1 - (1 - lam) ^ 2 / (1 + lam) ^ 2 = 4 * lam / (1 + lam) ^ 2 ∧
    SignType.sign (monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ))) =
      SignType.sign (4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 -
        monoPsi (p / (2 - p)) ((1 - p / 2) * θ)) := by
  have hlam : 1 + lam ≠ 0 := by linarith
  have hrat : 1 - (1 - lam) ^ 2 / (1 + lam) ^ 2 = 4 * lam / (1 + lam) ^ 2 := by
    field_simp [hlam]
    <;> ring
  refine ⟨hrat,?_⟩
  let m := p / (2 - p)
  let α := (1 - p / 2) * θ
  obtain ⟨hm,hα0,hαpi,hθeq,-,heps⟩ := sec5d_coordinate_dictionary_proved p θ ⟨hp1,hp2⟩ ⟨hθ0,hθ⟩
  change 1 < m at hm
  have hPsi := sec5d_W_Psi_identity_proved m α hm ⟨hα0,hαpi⟩
  change (p - 1) = (m - 1) / (m + 1) at heps
  change (m + 1) * α = θ at hθeq
  rw [← heps,hθeq] at hPsi
  have hαlt : α < Real.pi := by dsimp [α]; nlinarith [Real.pi_pos]
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 hαlt
  have he : 0 < p - 1 := by linarith
  have hq : 0 < m ^ 2 - 1 := by nlinarith
  have hscale : 0 < 4 * (p - 1) * Real.sin α ^ 4 / (m ^ 2 - 1) := by positivity
  have hbr := bracket_factor (monoW (p - 1) θ) (monoPsi m α) (p - 1) (Real.sin α)
    (m ^ 2 - 1) ((1 - lam) / (1 + lam)) (4 * lam / (1 + lam) ^ 2) hq.ne'
    (by positivity) hPsi (by simpa only [div_pow] using hrat)
  have hinside : (m ^ 2 - 1) * (4 * lam / (1 + lam) ^ 2) - monoPsi m α =
      4 * (m ^ 2 - 1) * lam / (1 + lam) ^ 2 - monoPsi m α := by ring
  rw [hinside] at hbr
  obtain ⟨hPi,hpref⟩ := sec5d_Pi_factorization_proved hp1 hp2 hl hl1 hθ0 hθ
  rw [hPi]
  change SignType.sign (monoPiPrefactor p θ (curveGamma p lam θ) *
    (monoW (p - 1) θ - 4 * (p - 1) * ((1 - lam) / (1 + lam)) ^ 2 * Real.sin α ^ 4)) = _
  rw [hbr,sign_mul,sign_eq_one_iff.mpr hpref,one_mul,sign_mul,sign_eq_one_iff.mpr hscale,one_mul]

/-- Assembly only: the missing logarithmic derivative is an explicit premise. This is not yet lemma_onevar. -/
theorem sec5d_onevar_of_log_derivative
    (hlog : ∀ {p lam θ : ℝ}, 1 < p → p < 2 → -1 < lam → lam < 1 →
      0 < θ → θ < Real.pi →
      HasDerivAt (fun a => Real.log (curveKf p lam (2 * a)))
        (monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ)) /
          monoSignDenominator p θ (Real.cos (2 * curveGamma p lam θ))) (θ / 2))
    {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 < lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    DifferentiableAt ℝ (curveKf p lam) θ ∧
    SignType.sign (deriv (curveKf p lam) θ) =
      SignType.sign (4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 -
        monoPsi (p / (2 - p)) ((1 - p / 2) * θ)) := by
  let X := Real.cos (2 * curveGamma p lam θ)
  let P := monoPi (p - 1) θ X
  let D := monoSignDenominator p θ X
  have hd : HasDerivAt (fun x : ℝ => Real.log (curveKf p lam x)) ((P / D) / 2) θ := by
    have hh := (hlog hp1 hp2 hl hl1 hθ0 hθ).comp θ ((hasDerivAt_id θ).div_const 2)
    convert hh using 1
    · funext x
      change Real.log (curveKf p lam x) = Real.log (curveKf p lam (2 * (x / 2)))
      rw [show 2 * (x / 2) = x by ring]
    · simp [P,D,X,div_eq_mul_inv]
  have heq : (fun x : ℝ => Real.exp (Real.log (curveKf p lam x))) =ᶠ[nhds θ] curveKf p lam := by
    filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 Real.pi from ⟨hθ0,hθ⟩)] with x hx
    exact Real.exp_log (curveKf_positive_proved hp1 hp2 hl hl1 hx.1 hx.2)
  have hf : HasDerivAt (curveKf p lam) (curveKf p lam θ * ((P / D) / 2)) θ := by
    have hh := hd.exp
    rw [Real.exp_log (curveKf_positive_proved hp1 hp2 hl hl1 hθ0 hθ)] at hh
    exact hh.congr_of_eventuallyEq heq.symm
  have hX : |X| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have hD : 0 < D := (sec5d_denominator_positive_proved hp1 hp2 hθ0 hθ hX).2
  have hscale : 0 < curveKf p lam θ / (2 * D) := div_pos
    (curveKf_positive_proved hp1 hp2 hl hl1 hθ0 hθ) (mul_pos (by norm_num) hD)
  refine ⟨hf.differentiableAt,?_⟩
  rw [hf.deriv,show curveKf p lam θ * ((P / D) / 2) = (curveKf p lam θ / (2 * D)) * P by ring,
    sign_mul,sign_eq_one_iff.mpr hscale,one_mul]
  exact (sec5d_Pi_Psi_sign_proved hp1 hp2 hl hl1 hθ0 hθ).2

end GKSharp

