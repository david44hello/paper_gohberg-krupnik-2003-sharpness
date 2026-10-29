/- exact contact K formula used by the analytic endpoint estimate.
Frozen source: short_v0.70/endpoint_estimate.tex:46–50.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.EndpointContact
import GKSharp.Proofs.ContactHarmonic
import GKSharp.Proofs.ContactDtGamma
import GKSharp.Proofs.ThresholdGammaLinks

namespace GKSharp
open Real Threshold Set

theorem endpoint_contact_k_identity {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let lam := endpointLambda p
    let eps := 1 - lam
    let Q := eps / sin a
    let r := contactRadius p lam
    let v := r - lam / r
    kConst p lam = 2 * Q * r ^ (-(p / 2)) *
      ‖(r : ℂ) * unitPoint (Real.pi / p) + (lam : ℂ)‖ ^ p / v := by
  dsimp only
  let lam := endpointLambda p
  have hhi : p ≤ (1000001 : ℝ) / 1000000 := by norm_num at hp1; linarith
  have hp2 : p < 2 := by linarith
  have hl := (endpoint_d_basic hp hp1).2.2.2.2
  have hl' : lam ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hl.1], hl.2⟩
  have hrad := ContactLower.contactRadius_interior p lam hp hp2 hl'
  have hsin : sin (endpointA p) = sn p := by
    have ha : endpointA p = Real.pi - Real.pi / p := by unfold endpointA; field_simp <;> ring
    rw [ha, sin_pi_sub]
    rfl
  rw [hrad, hsin]
  let r := rContact p lam
  let y := yContact p lam
  let t := theta p
  let GG := fun y t => bigG p (gk p lam) lam (zeta y t)
  let N := ‖(r : ℂ) * unitPoint (Real.pi / p) + (lam : ℂ)‖
  obtain ⟨hr1, -, hv, -⟩ := contact_root_properties hp hp2 hl'
  have hr0 : 0 < r := by linarith
  have hq : q p ≠ 0 := by unfold q; linarith
  have hs := sec4a_sn_pos hp
  have hz : zeta y t = (r : ℂ) * unitPoint (Real.pi / p) := by
    have hey : exp (log (rContact p lam)) = rContact p lam := exp_log (by linarith)
    dsimp only [y, yContact, t, theta, r, zeta, unitPoint]
    simp [Complex.exp_add, mul_comm Complex.I, ← Complex.ofReal_exp, hey]
  have hN0 : 0 < N := by
    obtain ⟨_, _, _, _, _, heps, hn⟩ := endpoint_contact_bounds hp hp1
    rw [hrad] at heps hn
    have he0 : 0 < 1 - lam := by linarith [hl.2]
    exact he0.trans_le (heps.trans hn)
  have hP : weightP p lam y t = N ^ p := by
    unfold weightP chi
    rw [hz, rpow_def_of_pos hN0]
    congr 1
    ring
  have hscale : exp (-q p * y) = r ^ (-(p / 2)) := by
    rw [rpow_def_of_pos hr0]
    dsimp only [y, yContact, r, q]
    congr 1
    ring
  have hfun : (fun x => gammaGK p lam y x) = fun x => exp (-q p * y) * GG y x :=
    funext (fun x => threshold_gamma_coordinate_bridge_proved p (gk p lam) lam y x hp)
  have hdt : dt (gammaGK p lam) y t = exp (-q p * y) * dt GG y t := by
    unfold dt
    rw [hfun, deriv_const_mul_field]
  have hGdt := (contact_harmonic_derivatives_proved p lam hp hp2 hl').2.2.2.1
  have hLdt := (contact_derivative_values_proved p lam hp hp2 hl').1
  have hGamma := contact_dt_gamma p lam hp hp2 hl'
  apply (mul_right_cancel₀ hq)
  calc
    kConst p lam * q p = -dt (gammaGK p lam) y t := by rw [hGamma]; ring
    _ = -(exp (-q p * y) * (p * weightP p lam y t * (-(1 - lam) / (sn p * vContact p lam)))) := by
      rw [hdt, hGdt, hLdt]
    _ = _ := by
      rw [hscale, hP]
      dsimp only [vContact, r, q, N]
      field_simp
      <;> ring

end GKSharp

#print axioms GKSharp.endpoint_contact_k_identity
