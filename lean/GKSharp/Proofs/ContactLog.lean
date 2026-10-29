/- GKSharp/Proofs/ContactLog.lean — a genuine local holomorphic logarithm.
Frozen source: short_v0.40/sec4b_failure.tex:29–30.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactScalar

namespace GKSharp
open Threshold Set Filter
open scoped Topology

private theorem mobContact_imag (lam : ℝ) (z : ℂ) :
    (mobContact lam z).im = (1 - lam) * z.im / Complex.normSq (z + 1) := by
  simp only [mobContact, Complex.div_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

/-- B:29–30. A local analytic logarithm of the actual Möbius map; the
neighborhood excludes the pole and the logarithm's cut explicitly. -/
theorem contact_local_log_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    ∃ ell : ℂ → ℂ, ∃ U ∈ 𝓝 ((yContact p lam : ℂ) + Complex.I * (theta p : ℂ)),
      AnalyticOnNhd ℂ ell U ∧
      ∀ u ∈ U, Complex.exp (ell u) = mobContact lam (Complex.exp u) ∧
        deriv ell u = (1 - (lam : ℂ)) * Complex.exp u /
          ((Complex.exp u + (lam : ℂ)) * (Complex.exp u + 1)) := by
  let u0 : ℂ := (yContact p lam : ℂ) + Complex.I * (theta p : ℂ)
  let ff : ℂ → ℂ := fun u => mobContact lam (Complex.exp u)
  obtain ⟨hr, _, _, _⟩ := contact_root_properties hp hp2 hlam
  have hrpos : 0 < rContact p lam := by linarith
  have hp0 : 0 < p := by linarith
  have ht0 : 0 < theta p := div_pos Real.pi_pos hp0
  have htpi : theta p < Real.pi := by
    unfold theta
    rw [div_lt_iff₀ hp0]
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (theta p) := Real.sin_pos_of_pos_of_lt_pi ht0 htpi
  have him : 0 < (Complex.exp u0).im := by
    have he : Complex.exp u0 = (rContact p lam : ℂ) *
        Complex.exp ((theta p : ℂ) * Complex.I) := by
      dsimp [u0, yContact]
      rw [Complex.exp_add, mul_comm Complex.I, ← Complex.ofReal_exp, Real.exp_log hrpos]
    rw [he, Complex.mul_im]
    simpa using mul_pos hrpos hsin
  have hden : Complex.exp u0 + 1 ≠ 0 := by
    intro hh
    have hh' := congrArg Complex.im hh
    simp only [Complex.add_im, Complex.one_im, Complex.zero_im, add_zero] at hh'
    linarith
  have hffim : 0 < (ff u0).im := by
    rw [show ff u0 = mobContact lam (Complex.exp u0) from rfl, mobContact_imag]
    exact div_pos (mul_pos (by linarith [hlam.2]) him) (Complex.normSq_pos.mpr hden)
  have hslit : ff u0 ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hffim))
  have hcont : ContinuousAt ff u0 := by
    exact (Complex.continuous_exp.continuousAt.add_const (lam : ℂ)).div
      (Complex.continuous_exp.continuousAt.add_const 1) hden
  let U : Set ℂ := {u | Complex.exp u + 1 ≠ 0 ∧ ff u ∈ Complex.slitPlane}
  have hU : U ∈ 𝓝 u0 := inter_mem
    ((Complex.continuous_exp.continuousAt.add_const 1).eventually_ne hden)
    (hcont.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hslit))
  refine ⟨fun u => Complex.log (ff u), U, hU, ?_, ?_⟩
  · intro u hu
    have hex : AnalyticAt ℂ Complex.exp u := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      exact Filter.Eventually.of_forall (fun _ => Complex.differentiable_exp.differentiableAt)
    have ha : AnalyticAt ℂ ff u := by
      exact (hex.add analyticAt_const).div (hex.add analyticAt_const) hu.1
    exact ha.clog hu.2
  · intro u hu
    have hf0 : ff u ≠ 0 := Complex.slitPlane_ne_zero hu.2
    have hnum : Complex.exp u + (lam : ℂ) ≠ 0 := by
      intro hh
      apply hf0
      simp [ff, mobContact, hh]
    refine ⟨Complex.exp_log hf0, ?_⟩
    have hd := (((Complex.hasDerivAt_exp u).add_const (lam : ℂ)).div
      ((Complex.hasDerivAt_exp u).add_const 1) hu.1).clog hu.2
    change deriv (fun u => Complex.log ((Complex.exp u + (lam : ℂ)) /
      (Complex.exp u + 1))) u = _
    change HasDerivAt (fun u => Complex.log ((Complex.exp u + (lam : ℂ)) /
      (Complex.exp u + 1))) _ u at hd
    rw [hd.deriv]
    simp only [Pi.div_apply]
    field_simp [hnum, hu.1]
    <;> ring

end GKSharp

#print axioms GKSharp.contact_local_log_proved
