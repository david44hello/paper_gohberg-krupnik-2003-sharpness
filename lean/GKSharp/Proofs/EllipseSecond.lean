/-
EllipseSecond.lean — second derivative of the principal power along the ellipse, project019.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.EllipseCalculus

namespace GKSharp.Proofs.EllipseCalculus

open GKSharp ComplexConjugate Filter Topology

noncomputable def ellipseDD (lam ρ : ℝ) (z : ℂ) : ℂ :=
  -(((1 + lam) * ρ : ℝ) : ℂ) * Complex.cos z -
    Complex.I * (((1 - lam) * ρ : ℝ) : ℂ) * Complex.sin z

lemma ellipseD_hasDerivAt (lam ρ : ℝ) (z : ℂ) :
    HasDerivAt (ellipseD lam ρ) (ellipseDD lam ρ z) z := by
  have hh := ((Complex.hasDerivAt_sin z).const_mul (-(((1 + lam) * ρ : ℝ) : ℂ))).add
    ((Complex.hasDerivAt_cos z).const_mul (Complex.I * (((1 - lam) * ρ : ℝ) : ℂ)))
  convert hh using 1
  · rfl
  · dsimp [ellipseDD]
    ring

lemma ellipseDD_real (lam ρ x : ℝ) :
    ellipseDD lam ρ (x : ℂ) = -
      ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I) +
        (lam : ℂ) * conj ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) := by
  apply Complex.ext <;>
    simp [ellipseDD, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] <;> ring

lemma power_second_hasDerivAt {lam ρ q : ℝ} {z : ℂ} (hs : ellipse lam ρ z ∈ Complex.slitPlane) :
    HasDerivAt (fun z => (q : ℂ) * ellipse lam ρ z ^ ((q - 1 : ℝ) : ℂ) * ellipseD lam ρ z)
      ((q : ℂ) * ((q - 1 : ℝ) : ℂ) * ellipse lam ρ z ^ ((q - 2 : ℝ) : ℂ) * (ellipseD lam ρ z) ^ 2 +
        (q : ℂ) * ellipse lam ρ z ^ ((q - 1 : ℝ) : ℂ) * ellipseDD lam ρ z) z := by
  have hh := ((power_hasDerivAt (q := q - 1) hs).const_mul (q : ℂ)).mul (ellipseD_hasDerivAt lam ρ z)
  convert hh using 1
  rw [show q - 1 - 1 = q - 2 by ring]
  ring

lemma real_power_second {lam ρ q x : ℝ} (hs : ellipse lam ρ (x : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (deriv (fun t : ℝ => (ellipse lam ρ (t : ℂ) ^ (q : ℂ)).re))
      (((q : ℂ) * ((q - 1 : ℝ) : ℂ) * ellipse lam ρ (x : ℂ) ^ ((q - 2 : ℝ) : ℂ) *
          (ellipseD lam ρ (x : ℂ)) ^ 2 +
        (q : ℂ) * ellipse lam ρ (x : ℂ) ^ ((q - 1 : ℝ) : ℂ) * ellipseDD lam ρ (x : ℂ)).re) x := by
  have hd := (power_second_hasDerivAt (q := q) hs).real_of_complex
  have local_deriv : deriv (fun t : ℝ => (ellipse lam ρ (t : ℂ) ^ (q : ℂ)).re) =ᶠ[𝓝 x]
      (fun t : ℝ => ((q : ℂ) * ellipse lam ρ (t : ℂ) ^ ((q - 1 : ℝ) : ℂ) * ellipseD lam ρ (t : ℂ)).re) := by
    have hc : Continuous (fun t : ℝ => ellipse lam ρ (t : ℂ)) := by
      exact (ellipse_contDiff lam ρ).continuous.comp Complex.continuous_ofReal
    have hn : ∀ᶠ t : ℝ in 𝓝 x, ellipse lam ρ (t : ℂ) ∈ Complex.slitPlane :=
      hc.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds hs)
    filter_upwards [hn] with t ht
    exact (power_hasDerivAt (q := q) ht).real_of_complex.deriv
  exact hd.congr_of_eventuallyEq local_deriv

lemma cpow_polar (z : ℂ) (a : ℝ) :
    z ^ (a : ℂ) = ((‖z‖ ^ a : ℝ) : ℂ) * Complex.exp (((a * Complex.arg z : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.cpow_ofReal, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [mul_comm a (Complex.arg z)]

lemma cpow_phase (z : ℂ) (a b : ℝ) :
    z ^ (a : ℂ) * Complex.exp ((b : ℂ) * Complex.I) =
      ((‖z‖ ^ a : ℝ) : ℂ) * Complex.exp ((((a * Complex.arg z + b : ℝ) : ℂ)) * Complex.I) := by
  rw [cpow_polar, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma cpow_phase_re (z : ℂ) (a b : ℝ) :
    (z ^ (a : ℂ) * Complex.exp ((b : ℂ) * Complex.I)).re =
      ‖z‖ ^ a * Real.cos (a * Complex.arg z + b) := by
  rw [cpow_phase, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

lemma imaginary_phase_square (A d : ℝ) :
    (Complex.I * (A : ℂ) * Complex.exp ((d : ℂ) * Complex.I)) ^ 2 =
      -((A ^ 2 : ℝ) : ℂ) * Complex.exp (((2 * d : ℝ) : ℂ) * Complex.I) := by
  rw [mul_pow, mul_pow, Complex.I_sq]
  have he : Complex.exp ((d : ℂ) * Complex.I) ^ 2 =
      Complex.exp (((2 * d : ℝ) : ℂ) * Complex.I) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  push_cast
  ring

lemma first_second_term (z : ℂ) (q A : ℝ) :
    (((q : ℂ) * ((q - 1 : ℝ) : ℂ) * z ^ ((q - 2 : ℝ) : ℂ) *
      (Complex.I * (A : ℂ) * Complex.exp ((((1 - q) * Complex.arg z : ℝ) : ℂ) * Complex.I)) ^ 2)).re =
    q * (1 - q) * ‖z‖ ^ (q - 2) * A ^ 2 * Real.cos (q * Complex.arg z) := by
  rw [imaginary_phase_square]
  have he : (q : ℂ) * ((q - 1 : ℝ) : ℂ) * z ^ ((q - 2 : ℝ) : ℂ) *
      (-((A ^ 2 : ℝ) : ℂ) * Complex.exp (((2 * ((1 - q) * Complex.arg z) : ℝ) : ℂ) * Complex.I)) =
      ((q * (1 - q) * A ^ 2 : ℝ) : ℂ) *
        (z ^ ((q - 2 : ℝ) : ℂ) * Complex.exp (((2 * ((1 - q) * Complex.arg z) : ℝ) : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [he, Complex.re_ofReal_mul, cpow_phase_re,
    show (q - 2) * Complex.arg z + 2 * ((1 - q) * Complex.arg z) = -(q * Complex.arg z) by ring,
    Real.cos_neg]
  ring

end GKSharp.Proofs.EllipseCalculus

#print axioms GKSharp.Proofs.EllipseCalculus.real_power_second
