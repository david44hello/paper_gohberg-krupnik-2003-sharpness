/-
RealGradients.lean — real gradients of the principal-power obstacle and norm power, project019.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.EllipseCalculus

namespace GKSharp.Proofs.RealGradients

open GKSharp ComplexConjugate
open GKSharp.Proofs.EllipseCalculus
open scoped RealInnerProductSpace

lemma mobQ_im (lam : ℝ) (w : ℂ) : (mobQ lam w).im = (1 - lam) * w.im := by
  simp [mobQ, Complex.mul_im, Complex.mul_re]
  ring

noncomputable def mobQD (lam : ℝ) (w : ℂ) : ℂ →L[ℝ] ℂ :=
  (1 - conj w) • (1 : ℂ →L[ℝ] ℂ) -
    (w - (lam : ℂ)) • (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)

lemma mobQ_hasFDerivAt (lam : ℝ) (w : ℂ) : HasFDerivAt (mobQ lam) (mobQD lam w) w := by
  have hid := hasFDerivAt_id (𝕜 := ℝ) w
  have hconj : HasFDerivAt (conj : ℂ → ℂ)
      (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ) w :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  have hh := (hid.sub_const (lam : ℂ)).mul ((hasFDerivAt_const (1 : ℂ) w).sub hconj)
  convert hh using 1
  · rfl
  · ext h
    simp [mobQD, smul_eq_mul]
    ring

lemma gradient_dictionary (p lam : ℝ) (w h : ℂ) :
    (h * conj ((((p / 2) * ‖mobQ lam w‖ ^ (p / 2 - 1) : ℝ) : ℂ) *
      (curveV p lam (Complex.arg (mobQ lam w)) -
        2 * w * ((Real.cos ((1 - p / 2) * Complex.arg (mobQ lam w)) : ℝ) : ℂ)))).re =
    ((((p / 2 : ℝ) : ℂ) * mobQ lam w ^ ((p / 2 - 1 : ℝ) : ℂ)) *
      ((1 - conj w) * h - (w - lam) * conj h)).re := by
  obtain ⟨hvr, hvi⟩ := GKSharp.curveV_re_im p lam (Complex.arg (mobQ lam w))
  have hc : Real.cos (Complex.arg (mobQ lam w) * (p / 2 - 1)) =
      Real.cos ((1 - p / 2) * Complex.arg (mobQ lam w)) := by
    rw [show Complex.arg (mobQ lam w) * (p / 2 - 1) =
      -((1 - p / 2) * Complex.arg (mobQ lam w)) by ring, Real.cos_neg]
  have hs : Real.sin (Complex.arg (mobQ lam w) * (p / 2 - 1)) =
      -Real.sin ((1 - p / 2) * Complex.arg (mobQ lam w)) := by
    rw [show Complex.arg (mobQ lam w) * (p / 2 - 1) =
      -((1 - p / 2) * Complex.arg (mobQ lam w)) by ring, Real.sin_neg]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im,
    show (2 : ℂ).re = (2 : ℝ) from rfl, show (2 : ℂ).im = (0 : ℝ) from rfl,
    Complex.cpow_ofReal_re, Complex.cpow_ofReal_im, hvr, hvi, hc, hs]
  ring

theorem sec5_grad_parts_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam)
    (hl1 : lam < 1) {w : ℂ} (hw : 0 < w.im) :
    let θ := Complex.arg (mobQ lam w)
    HasFDerivAt (fun u : ℂ => reQPow (mobQ lam u) (p / 2))
      (innerSL ℝ ((((p / 2) * ‖mobQ lam w‖ ^ (p / 2 - 1) : ℝ) : ℂ) *
        (curveV p lam θ - 2 * w * ((Real.cos ((1 - p / 2) * θ) : ℝ) : ℂ))) : ℂ →L[ℝ] ℝ) w ∧
    HasFDerivAt (fun u : ℂ => ‖u‖ ^ p)
      (innerSL ℝ (((p * ‖w‖ ^ (p - 2) : ℝ) : ℂ) * w) : ℂ →L[ℝ] ℝ) w := by
  have hQi : 0 < (mobQ lam w).im := by
    rw [mobQ_im]
    exact mul_pos (sub_pos.mpr hl1) hw
  have hslit : mobQ lam w ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hQi))
  have hp := (Complex.hasStrictDerivAt_cpow_const (c := ((p / 2 : ℝ) : ℂ)) hslit).hasDerivAt.complexToReal_fderiv
  have hcomp := Complex.reCLM.hasFDerivAt.comp w (hp.comp w (mobQ_hasFDerivAt lam w))
  constructor
  · convert hcomp using 1
    · funext u
      simp only [Function.comp_def, Complex.reCLM_apply, reQPow_cpow]
    · ext h
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, Complex.reCLM_apply, innerSL_apply_apply,
        Complex.inner, smul_eq_mul]
      rw [gradient_dictionary]
      simp [mobQD, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_one]
  · convert hasFDerivAt_norm_rpow w hp1 using 1
    ext h
    simp only [innerSL_apply_apply, ContinuousLinearMap.smul_apply]
    change inner ℝ (((p * ‖w‖ ^ (p - 2) : ℝ) : ℂ) * w) h =
      (p * ‖w‖ ^ (p - 2)) * inner ℝ w h
    exact real_inner_smul_left w h (p * ‖w‖ ^ (p - 2))

end GKSharp.Proofs.RealGradients

#print axioms GKSharp.Proofs.RealGradients.sec5_grad_parts_proved

