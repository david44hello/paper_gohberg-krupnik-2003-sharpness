/-
InverseCritical.lean — inverse Moebius coordinates and the second form of equation5.3, project019.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.CriticalMaximum

namespace GKSharp.Proofs.InverseCritical

open GKSharp ComplexConjugate
open GKSharp.Proofs.EllipseCalculus GKSharp.Proofs.CriticalMaximum

lemma inverse_mobW {lam : ℝ} (hl : lam < 1) {w : ℂ} (hw : w ≠ (lam : ℂ)) :
    (1 - w) / (w - lam) ≠ -1 ∧ mobW lam ((1 - w) / (w - lam)) = w := by
  have hd : w - (lam : ℂ) ≠ 0 := sub_ne_zero.mpr hw
  have hc : (1 : ℂ) - lam ≠ 0 := by
    intro hh
    have hh' := congrArg Complex.re hh
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at hh'
    linarith
  constructor
  · intro hh
    rw [div_eq_iff hd] at hh
    apply hc
    linear_combination hh
  · have hp : (1 : ℂ) + (1 - w) / (w - lam) ≠ 0 := by
      rw [show (1 : ℂ) + (1 - w) / (w - lam) = (1 - lam) / (w - lam) by field_simp; ring]
      exact div_ne_zero hc hd
    unfold mobW
    rw [div_eq_iff hp]
    field_simp
    ring

lemma arg_range {Q : ℂ} (hi : 0 < Q.im) : 0 < Complex.arg Q ∧ Complex.arg Q < Real.pi := by
  constructor
  · have hn : 0 ≤ Complex.arg Q := Complex.arg_nonneg_iff.mpr hi.le
    by_contra h
    have hz : Complex.arg Q = 0 := le_antisymm (not_lt.mp h) hn
    have hs := Complex.norm_mul_sin_arg Q
    rw [hz, Real.sin_zero, mul_zero] at hs
    linarith
  · exact Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hi))

theorem eq_5_3_second_proved {p lam ρ φ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hρ : 0 < ρ) (hφ0 : 0 < φ) (hφ : φ < Real.pi) :
    let f := fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)
    let w : ℂ := (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
    let θ := Complex.arg (mobQ lam w)
    let z : ℂ := (1 - w) / (w - lam)
    z = (‖z‖ : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) ∧
    HasDerivAt f (-(p / 2) * (1 - lam) * ‖mobQ lam w‖ ^ (p / 2 - 1) / ‖1 + z‖ ^ 2 * curveD p lam θ ‖z‖) φ ∧
    (deriv f φ = 0 ↔ w = ((ρ / ‖curveV p lam θ‖ : ℝ) : ℂ) * curveV p lam θ) ∧
    (deriv f φ = 0 ↔ curveD p lam θ ‖z‖ = 0) := by
  let f := fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)
  let w : ℂ := (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
  let θ := Complex.arg (mobQ lam w)
  let z : ℂ := (1 - w) / (w - lam)
  have hwi : 0 < w.im := by
    dsimp [w]
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    exact mul_pos hρ (Real.sin_pos_of_pos_of_lt_pi hφ0 hφ)
  have hwlam : w ≠ (lam : ℂ) := by
    intro hh
    have hi := congrArg Complex.im hh
    simp only [Complex.ofReal_im] at hi
    linarith
  obtain ⟨hz, hmap⟩ := inverse_mobW hl1 hwlam
  change z ≠ -1 at hz
  change mobW lam z = w at hmap
  have hpz : (1 : ℂ) + z ≠ 0 := GKSharp.one_add_ne_zero hz
  have hA : 0 < ‖(1 : ℂ) + z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hpz)
  have hconst : 0 < (1 - lam) ^ 2 / ‖(1 : ℂ) + z‖ ^ 2 :=
    div_pos (sq_pos_of_pos (sub_pos.mpr hl1)) hA
  have hdict := GKSharp.mobQ_mobW lam hz
  rw [hmap] at hdict
  have hQi : 0 < (mobQ lam w).im :=
    (eq_5_3_proved hp1 hp2 hl hl1 hρ hφ0 hφ).1
  obtain ⟨hθ0, hθ⟩ := arg_range hQi
  have harg : Complex.arg (conj z) = θ := by
    dsimp [θ]
    rw [hdict, Complex.arg_real_mul _ hconst]
  have hpolar : z = (‖z‖ : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) := by
    have hh := Complex.norm_mul_exp_arg_mul_I (conj z)
    rw [Complex.norm_conj, harg] at hh
    have hc := congrArg conj hh
    simpa only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I,
      mul_neg, neg_mul, Complex.conj_conj] using hc.symm
  have hcross := GKSharp.cross_curveD p lam θ ‖z‖
  rw [← hpolar, hmap] at hcross
  have hd := (eq_5_3_proved hp1 hp2 hl hl1 hρ hφ0 hφ).2.2
  change HasDerivAt f (-(p / 2) * ‖mobQ lam w‖ ^ (p / 2 - 1) * (conj (curveV p lam θ) * w).im) φ at hd
  have hQne : mobQ lam w ≠ 0 := by intro hh; simpa [hh] using hQi
  have hcoef : -(p / 2) * ‖mobQ lam w‖ ^ (p / 2 - 1) ≠ 0 := by
    apply mul_ne_zero
    · linarith
    · exact ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hQne) _)
  have hzero : deriv f φ = 0 ↔ (conj (curveV p lam θ) * w).im = 0 := by
    rw [hd.deriv, mul_eq_zero]
    simp only [hcoef, false_or]
  have hderiv : HasDerivAt f
      (-(p / 2) * (1 - lam) * ‖mobQ lam w‖ ^ (p / 2 - 1) / ‖1 + z‖ ^ 2 * curveD p lam θ ‖z‖) φ := by
    apply hd.congr_deriv
    rw [hcross]
    ring
  have hvi : 0 < (curveV p lam θ).im := by
    rw [(GKSharp.curveV_re_im p lam θ).2]
    apply mul_pos (sub_pos.mpr hl1)
    apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith
  have hvne : curveV p lam θ ≠ 0 := by intro hh; simpa [hh] using hvi
  have hvnorm : 0 < ‖curveV p lam θ‖ := norm_pos_iff.mpr hvne
  have hnormw : ‖w‖ = ρ := by
    simp [w, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, Complex.norm_exp_ofReal_mul_I]
  have hparallel : deriv f φ = 0 ↔ w = ((ρ / ‖curveV p lam θ‖ : ℝ) : ℂ) * curveV p lam θ := by
    rw [hzero]
    constructor
    · intro hc
      obtain ⟨τ, hτ, hwτ⟩ := parallel_upper hvi hwi hc
      have htau : τ = ρ / ‖curveV p lam θ‖ := by
        apply (eq_div_iff (ne_of_gt hvnorm)).mpr
        have hh := congrArg norm hwτ
        rw [hnormw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] at hh
        exact hh.symm
      rwa [htau] at hwτ
    · intro hc
      rw [hc, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.re_ofReal_mul, Complex.im_ofReal_mul]
      ring
  have hDzero : deriv f φ = 0 ↔ curveD p lam θ ‖z‖ = 0 := by
    rw [hzero, hcross, div_eq_zero_iff, mul_eq_zero]
    simp only [ne_of_gt hA, ne_of_gt (sub_pos.mpr hl1), false_or, or_false]
  exact ⟨hpolar, hderiv, hparallel, hDzero⟩

end GKSharp.Proofs.InverseCritical

#print axioms GKSharp.Proofs.InverseCritical.eq_5_3_second_proved

