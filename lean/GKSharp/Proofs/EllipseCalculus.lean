/-
EllipseCalculus.lean — holomorphic ellipse extension and principal-power calculus, project019.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.MobiusDict

namespace GKSharp.Proofs.EllipseCalculus

open GKSharp ComplexConjugate Filter Topology
open scoped ContDiff

noncomputable def ellipse (lam ρ : ℝ) (z : ℂ) : ℂ :=
  -((ρ ^ 2 + lam : ℝ) : ℂ) + ((1 + lam) * ρ : ℝ) * Complex.cos z +
    Complex.I * (((1 - lam) * ρ : ℝ) : ℂ) * Complex.sin z

noncomputable def ellipseD (lam ρ : ℝ) (z : ℂ) : ℂ :=
  -(((1 + lam) * ρ : ℝ) : ℂ) * Complex.sin z +
    Complex.I * (((1 - lam) * ρ : ℝ) : ℂ) * Complex.cos z

lemma ellipse_real (lam ρ x : ℝ) :
    ellipse lam ρ (x : ℂ) = mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I)) := by
  rw [GKSharp.mobQ_polar]
  simp [ellipse, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub]
  <;> ring

lemma ellipse_hasDerivAt (lam ρ : ℝ) (z : ℂ) :
    HasDerivAt (ellipse lam ρ) (ellipseD lam ρ z) z := by
  have hh := ((hasDerivAt_const z (-((ρ ^ 2 + lam : ℝ) : ℂ))).add
    ((Complex.hasDerivAt_cos z).const_mul (((1 + lam) * ρ : ℝ) : ℂ))).add
      ((Complex.hasDerivAt_sin z).const_mul (Complex.I * (((1 - lam) * ρ : ℝ) : ℂ)))
  convert hh using 1
  · rfl
  · dsimp [ellipseD]
    ring

lemma ellipse_contDiff (lam ρ : ℝ) : ContDiff ℂ ∞ (ellipse lam ρ) := by
  unfold ellipse
  fun_prop

lemma ellipse_im (lam ρ x : ℝ) :
    (ellipse lam ρ (x : ℂ)).im = (1 - lam) * ρ * Real.sin x := by
  rw [ellipse_real, GKSharp.mobQ_polar]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im]
  ring

lemma ellipse_upper {lam ρ x : ℝ} (hl : lam < 1) (hr : 0 < ρ) (hx0 : 0 < x) (hx : x < Real.pi) :
    0 < (ellipse lam ρ (x : ℂ)).im := by
  rw [ellipse_im]
  exact mul_pos (mul_pos (sub_pos.mpr hl) hr) (Real.sin_pos_of_pos_of_lt_pi hx0 hx)

lemma reQPow_cpow (z : ℂ) (q : ℝ) : reQPow z q = (z ^ (q : ℂ)).re := by
  rw [Complex.cpow_ofReal_re, reQPow]
  congr 1
  congr 1
  ring

lemma power_contDiffAt {lam ρ x q : ℝ} (hs : ellipse lam ρ (x : ℂ) ∈ Complex.slitPlane) :
    ContDiffAt ℂ ∞ (fun z => ellipse lam ρ z ^ (q : ℂ)) (x : ℂ) := by
  have he := (ellipse_contDiff lam ρ).contDiffAt (x := (x : ℂ))
  have hc : ContDiffAt ℂ ∞ (fun z => Complex.exp (Complex.log (ellipse lam ρ z) * (q : ℂ))) (x : ℂ) :=
    (((Complex.contDiffAt_log hs).comp _ he).mul contDiffAt_const).cexp
  apply hc.congr_of_eventuallyEq
  have hne : ellipse lam ρ (x : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hs
  have hn : ∀ᶠ z : ℂ in 𝓝 (x : ℂ), ellipse lam ρ z ≠ 0 :=
    he.continuousAt.eventually (eventually_ne_nhds hne)
  filter_upwards [hn] with z hz
  exact Complex.cpow_def_of_ne_zero hz _

lemma power_hasDerivAt {lam ρ q : ℝ} {z : ℂ} (hs : ellipse lam ρ z ∈ Complex.slitPlane) :
    HasDerivAt (fun z => ellipse lam ρ z ^ (q : ℂ))
      ((q : ℂ) * ellipse lam ρ z ^ ((q - 1 : ℝ) : ℂ) * ellipseD lam ρ z) z := by
  simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
    (ellipse_hasDerivAt lam ρ z).cpow_const (c := (q : ℂ)) hs

lemma ellipseD_real (lam ρ x : ℝ) :
    ellipseD lam ρ (x : ℂ) = Complex.I *
      ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I) -
        (lam : ℂ) * conj ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) := by
  apply Complex.ext <;>
    simp [ellipseD, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im] <;> ring

lemma power_derivative_dictionary (p lam ρ x : ℝ) :
    (((p / 2 : ℝ) : ℂ) * ellipse lam ρ (x : ℂ) ^ ((p / 2 - 1 : ℝ) : ℂ) *
      ellipseD lam ρ (x : ℂ)).re =
    -(p / 2) * ‖ellipse lam ρ (x : ℂ)‖ ^ (p / 2 - 1) *
      (conj (curveV p lam (Complex.arg (ellipse lam ρ (x : ℂ)))) *
        ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))).im := by
  rw [ellipseD_real]
  obtain ⟨hvr, hvi⟩ := GKSharp.curveV_re_im p lam (Complex.arg (ellipse lam ρ (x : ℂ)))
  have hc : Real.cos (Complex.arg (ellipse lam ρ (x : ℂ)) * (p / 2 - 1)) =
      Real.cos ((1 - p / 2) * Complex.arg (ellipse lam ρ (x : ℂ))) := by
    rw [show Complex.arg (ellipse lam ρ (x : ℂ)) * (p / 2 - 1) =
      -((1 - p / 2) * Complex.arg (ellipse lam ρ (x : ℂ))) by ring, Real.cos_neg]
  have hs : Real.sin (Complex.arg (ellipse lam ρ (x : ℂ)) * (p / 2 - 1)) =
      -Real.sin ((1 - p / 2) * Complex.arg (ellipse lam ρ (x : ℂ))) := by
    rw [show Complex.arg (ellipse lam ρ (x : ℂ)) * (p / 2 - 1) =
      -((1 - p / 2) * Complex.arg (ellipse lam ρ (x : ℂ))) by ring, Real.sin_neg]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im, Complex.cpow_ofReal_re, Complex.cpow_ofReal_im,
    hvr, hvi, hc, hs]
  ring

theorem eq_5_3_proved {p lam ρ φ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam)
    (hl1 : lam < 1) (hρ : 0 < ρ) (hφ0 : 0 < φ) (hφ : φ < Real.pi) :
    0 < (mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))).im ∧
    ContDiffAt ℝ ∞ (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ ∧
    HasDerivAt (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2))
      (-(p / 2) * ‖mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))‖ ^ (p / 2 - 1) *
        (conj (curveV p lam (Complex.arg (mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))))) *
          ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))).im) φ := by
  have hi := ellipse_upper hl1 hρ hφ0 hφ
  have hslit : ellipse lam ρ (φ : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hi))
  have feq : (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) =
      (fun x : ℝ => (ellipse lam ρ (x : ℂ) ^ ((p / 2 : ℝ) : ℂ)).re) := by
    funext x
    rw [← ellipse_real, reQPow_cpow]
  refine ⟨by simpa only [ellipse_real] using hi, ?_, ?_⟩
  · rw [feq]
    exact (power_contDiffAt (q := p / 2) hslit).real_of_complex
  · rw [feq]
    convert (power_hasDerivAt (q := p / 2) hslit).real_of_complex using 1
    rw [power_derivative_dictionary, ellipse_real]

end GKSharp.Proofs.EllipseCalculus

#print axioms GKSharp.Proofs.EllipseCalculus.eq_5_3_proved
