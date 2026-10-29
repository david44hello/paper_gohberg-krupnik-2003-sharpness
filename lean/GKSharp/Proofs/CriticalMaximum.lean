/-
CriticalMaximum.lean — second derivative at every interior critical point, project019 equation5.6.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.EllipseSecond
import GKSharp.Proofs.LemmaA

namespace GKSharp.Proofs.CriticalMaximum

open GKSharp ComplexConjugate Filter Topology
open GKSharp.Proofs.EllipseCalculus

lemma parallel_upper {v w : ℂ} (hv : 0 < v.im) (hw : 0 < w.im)
    (hcross : (conj v * w).im = 0) : ∃ τ : ℝ, 0 < τ ∧ w = (τ : ℂ) * v := by
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im] at hcross
  refine ⟨w.im / v.im, div_pos hw hv, ?_⟩
  apply Complex.ext
  · rw [Complex.re_ofReal_mul]
    field_simp
    linarith
  · rw [Complex.im_ofReal_mul]
    field_simp

lemma second_at_parallel {p lam ρ x τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 0 < Complex.arg (ellipse lam ρ (x : ℂ)))
    (hθ : Complex.arg (ellipse lam ρ (x : ℂ)) < Real.pi)
    (hw : (ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I) =
      (τ : ℂ) * curveV p lam (Complex.arg (ellipse lam ρ (x : ℂ)))) :
    (((p / 2 : ℝ) : ℂ) * ((p / 2 - 1 : ℝ) : ℂ) * ellipse lam ρ (x : ℂ) ^ ((p / 2 - 2 : ℝ) : ℂ) *
        (ellipseD lam ρ (x : ℂ)) ^ 2 +
      ((p / 2 : ℝ) : ℂ) * ellipse lam ρ (x : ℂ) ^ ((p / 2 - 1 : ℝ) : ℂ) * ellipseDD lam ρ (x : ℂ)).re =
    p / 2 * ‖ellipse lam ρ (x : ℂ)‖ ^ (p / 2 - 2) * τ ^ 2 * (1 - lam) ^ 2 *
      ((1 - p / 2) * (1 + lam) ^ 2 * Real.cos (p / 2 * Complex.arg (ellipse lam ρ (x : ℂ))) -
        ‖curveV p lam (Complex.arg (ellipse lam ρ (x : ℂ)))‖ ^ 2 *
          (Real.sin ((1 - p / 2) * Complex.arg (ellipse lam ρ (x : ℂ))) /
            Real.sin (Complex.arg (ellipse lam ρ (x : ℂ))))) := by
  let Q := ellipse lam ρ (x : ℂ)
  let θ := Complex.arg Q
  let q := p / 2
  let δ := (1 - p / 2) * θ
  obtain ⟨hv, hvnorm, hqim, hwi, hnorm, hminus, hplus, hsinarg⟩ :=
    GKSharp.curve_identities p lam θ hτ.le
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
  have hQi : Q.im = (1 - lam) ^ 2 * τ * Real.sin δ := by
    change (ellipse lam ρ (x : ℂ)).im = _
    rw [ellipse_real, hw]
    exact hqim.trans hwi
  have hR : ‖Q‖ = (1 - lam) ^ 2 * τ * Real.sin δ / Real.sin θ := by
    apply (eq_div_iff (ne_of_gt hsθ)).mpr
    exact (hsinarg Q).trans hQi
  have hQne : Q ≠ 0 := by
    intro hz
    have hh : Complex.arg Q = 0 := by simp [hz]
    linarith
  have hQnorm : 0 < ‖Q‖ := norm_pos_iff.mpr hQne
  have hD : ellipseD lam ρ (x : ℂ) =
      Complex.I * (((1 - lam ^ 2) * τ : ℝ) : ℂ) * Complex.exp ((δ : ℂ) * Complex.I) := by
    rw [ellipseD_real, hw, hminus]
    ring
  have term1 : (((q : ℂ) * ((q - 1 : ℝ) : ℂ) * Q ^ ((q - 2 : ℝ) : ℂ) *
      (ellipseD lam ρ (x : ℂ)) ^ 2)).re =
      q * (1 - q) * ‖Q‖ ^ (q - 2) * ((1 - lam ^ 2) * τ) ^ 2 * Real.cos (q * θ) := by
    rw [hD]
    exact first_second_term Q q ((1 - lam ^ 2) * τ)
  have he : (q : ℂ) * Q ^ ((q - 1 : ℝ) : ℂ) * ellipseDD lam ρ (x : ℂ) =
      ((-(q * ‖Q‖ ^ (q - 1)) : ℝ) : ℂ) *
        (Complex.exp (-(δ : ℂ) * Complex.I) *
          ((τ : ℂ) * curveV p lam θ + (lam : ℂ) * conj ((τ : ℂ) * curveV p lam θ))) := by
    rw [cpow_polar, ellipseDD_real, hw]
    have hphase : (((q - 1) * Complex.arg Q : ℝ) : ℂ) = -(δ : ℂ) := by
      dsimp [q, δ, θ]
      push_cast
      ring
    rw [hphase]
    push_cast
    ring
  have term2 : ((q : ℂ) * Q ^ ((q - 1 : ℝ) : ℂ) * ellipseDD lam ρ (x : ℂ)).re =
      -q * ‖Q‖ ^ (q - 1) * τ * ‖curveV p lam θ‖ ^ 2 := by
    rw [he, Complex.re_ofReal_mul]
    change -(q * ‖Q‖ ^ (q - 1)) *
      (Complex.exp (-((((1 - p / 2) * θ : ℝ) : ℂ)) * Complex.I) *
        ((τ : ℂ) * curveV p lam θ + lam * conj ((τ : ℂ) * curveV p lam θ))).re = _
    rw [hplus]
    ring
  have hpw : ‖Q‖ ^ (q - 1) = ‖Q‖ ^ (q - 2) * ‖Q‖ := by
    rw [show q - 1 = (q - 2) + 1 by ring, Real.rpow_add hQnorm, Real.rpow_one]
  have hRfactor : ‖Q‖ * τ * ‖curveV p lam θ‖ ^ 2 =
      τ ^ 2 * (1 - lam) ^ 2 * (‖curveV p lam θ‖ ^ 2 * (Real.sin δ / Real.sin θ)) := by
    rw [hR]
    ring
  change ((q : ℂ) * ((q - 1 : ℝ) : ℂ) * Q ^ ((q - 2 : ℝ) : ℂ) * (ellipseD lam ρ (x : ℂ)) ^ 2 +
    (q : ℂ) * Q ^ ((q - 1 : ℝ) : ℂ) * ellipseDD lam ρ (x : ℂ)).re = _
  rw [Complex.add_re, term1, term2, hpw]
  calc
    _ = q * ‖Q‖ ^ (q - 2) *
        ((1 - q) * τ ^ 2 * (1 - lam ^ 2) ^ 2 * Real.cos (q * θ) - ‖Q‖ * τ * ‖curveV p lam θ‖ ^ 2) := by ring
    _ = _ := by rw [hRfactor]; ring

theorem eq_5_6_proved {p lam ρ φ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam)
    (hl1 : lam < 1) (hρ : 0 < ρ) (hφ0 : 0 < φ) (hφ : φ < Real.pi)
    (hcrit : deriv (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ = 0) :
    let Q := mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
    let θ := Complex.arg Q
    let τ := ρ / ‖curveV p lam θ‖
    HasDerivAt (deriv fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2))
      (p / 2 * ‖Q‖ ^ (p / 2 - 2) * τ ^ 2 * (1 - lam) ^ 2 *
        ((1 - p / 2) * (1 + lam) ^ 2 * Real.cos (p / 2 * θ) -
          ‖curveV p lam θ‖ ^ 2 * (Real.sin ((1 - p / 2) * θ) / Real.sin θ))) φ ∧
    p / 2 * ‖Q‖ ^ (p / 2 - 2) * τ ^ 2 * (1 - lam) ^ 2 *
      ((1 - p / 2) * (1 + lam) ^ 2 * Real.cos (p / 2 * θ) -
        ‖curveV p lam θ‖ ^ 2 * (Real.sin ((1 - p / 2) * θ) / Real.sin θ)) < 0 := by
  let w : ℂ := (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
  let Q : ℂ := ellipse lam ρ (φ : ℂ)
  let θ : ℝ := Complex.arg Q
  have hQi : 0 < Q.im := ellipse_upper hl1 hρ hφ0 hφ
  have hθ0 : 0 < θ := by
    have hn : 0 ≤ θ := Complex.arg_nonneg_iff.mpr hQi.le
    by_contra hnpos
    have hz : θ = 0 := le_antisymm (not_lt.mp hnpos) hn
    have hs := Complex.norm_mul_sin_arg Q
    change ‖Q‖ * Real.sin θ = Q.im at hs
    rw [hz, Real.sin_zero, mul_zero] at hs
    linarith
  have hθ : θ < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hQi))
  have hQne : Q ≠ 0 := by intro hz; simpa [hz] using hQi
  have hslit : Q ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hQi))
  have hvi : 0 < (curveV p lam θ).im := by
    rw [(GKSharp.curveV_re_im p lam θ).2]
    apply mul_pos (sub_pos.mpr hl1)
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith
    · nlinarith
  have hvne : curveV p lam θ ≠ 0 := by intro hz; simpa [hz] using hvi
  have hvnorm : 0 < ‖curveV p lam θ‖ := norm_pos_iff.mpr hvne
  have hwi : 0 < w.im := by
    dsimp [w]
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    exact mul_pos hρ (Real.sin_pos_of_pos_of_lt_pi hφ0 hφ)
  have hd := (eq_5_3_proved hp1 hp2 hl hl1 hρ hφ0 hφ).2.2
  have hz := hd.deriv.symm.trans hcrit
  have hcross : (conj (curveV p lam θ) * w).im = 0 := by
    have hc : -(p / 2) * ‖Q‖ ^ (p / 2 - 1) ≠ 0 := by
      apply mul_ne_zero
      · linarith
      · exact ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hQne) _)
    apply (mul_eq_zero.mp ?_).resolve_left hc
    simpa only [Q, ellipse_real, θ, w] using hz
  obtain ⟨τ, hτ, hw⟩ := parallel_upper hvi hwi hcross
  have hnormw : ‖w‖ = ρ := by
    simp [w, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, Complex.norm_exp_ofReal_mul_I]
  have htau : τ = ρ / ‖curveV p lam θ‖ := by
    apply (eq_div_iff (ne_of_gt hvnorm)).mpr
    have hn := congrArg norm hw
    rw [hnormw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] at hn
    exact hn.symm
  have feq : (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) =
      (fun x : ℝ => (ellipse lam ρ (x : ℂ) ^ ((p / 2 : ℝ) : ℂ)).re) := by
    funext x
    rw [← ellipse_real, reQPow_cpow]
  have hsecond := real_power_second (q := p / 2) hslit
  have hformula := second_at_parallel hτ hθ0 hθ hw
  rw [← feq, hformula, htau] at hsecond
  have hbracket := GKSharp.lemmaA_bracket hp1 hp2 hl hl1 hθ0 hθ
  have hτnorm : 0 < ρ / ‖curveV p lam θ‖ := div_pos hρ hvnorm
  have hpref : 0 < p / 2 * ‖Q‖ ^ (p / 2 - 2) * (ρ / ‖curveV p lam θ‖) ^ 2 * (1 - lam) ^ 2 := by
    have hbase : 0 < 1 - lam := sub_pos.mpr hl1
    have hpow := Real.rpow_pos_of_pos (norm_pos_iff.mpr hQne) (p / 2 - 2)
    positivity
  have hnegative := mul_neg_of_pos_of_neg hpref hbracket
  simpa only [Q, θ, ellipse_real] using And.intro hsecond hnegative

end GKSharp.Proofs.CriticalMaximum

#print axioms GKSharp.Proofs.CriticalMaximum.eq_5_6_proved
