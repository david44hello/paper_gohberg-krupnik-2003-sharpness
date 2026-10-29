/- actual logarithmic level derivative, frozen short v0.70 sec5d:27.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneLevel

namespace GKSharp

open Filter Topology

set_option maxHeartbeats 1200000 in
theorem sec5d_level_derivative_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hl0 : lam ≠ 0) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    deriv (monoLogM p (θ / 2)) (curveGamma p lam θ) ≠ 0 ∧
    HasDerivAt (fun a => Real.log (curveKf p lam (2 * a)))
      (monoE p (θ / 2) (curveGamma p lam θ) /
        deriv (monoLogM p (θ / 2)) (curveGamma p lam θ)) (θ / 2) := by
  let a := θ / 2
  let b := (p - 1) * a
  let g := curveGamma p lam θ
  let G : ℝ → ℝ := fun x => curveGamma p lam (2 * x)
  let d := deriv G a
  have h2a : 2 * a = θ := by dsimp [a]; ring
  have hGa : G a = g := by dsimp [G,g]; rw [h2a]
  have hgamma : DifferentiableAt ℝ (curveGamma p lam) (2 * a) := by
    rw [h2a]
    exact curveGamma_differentiableAt hp1 hp2 hl hl1 hθ0 hθ
  have hlin : DifferentiableAt ℝ (fun x : ℝ => 2 * x) a := by fun_prop
  have hGdiff : DifferentiableAt ℝ G a := hgamma.comp a hlin
  have hG : HasDerivAt G d a := hGdiff.hasDerivAt
  have hab : 0 < b ∧ b < a ∧ a < Real.pi / 2 := by
    dsimp [a,b]
    refine ⟨mul_pos (by linarith) (half_pos hθ0), ?_, by linarith⟩
    nlinarith
  obtain ⟨hgb,hgpi,-,-⟩ := sec5d_gamma_spec_proved hp1 hp2 hl hl1 hθ0 hθ
  have hg : b < g ∧ g < Real.pi / 2 := ⟨hgb,hgpi⟩
  have hg0 : 0 < g := lt_trans hab.1 hg.1
  obtain ⟨hpb,hpa,hmb,-,-⟩ := sec5d_gamma_denominators_proved a b g hab hg
  have hga : g ≠ a := by
    intro hz
    exact hl0 ((sec5d_lambda_gamma_sign_proved hp1 hp2 hl hl1 hθ0 hθ).2.1.mpr hz)
  have hma : Real.sin (g - a) ≠ 0 := by
    have hh := Real.sin_eq_zero_iff_of_lt_of_lt (x := g - a)
      (by linarith [hab.2.2,Real.pi_pos]) (by linarith [hg.2,hab.1,hab.2.1,Real.pi_pos])
    exact fun hz => hga (sub_eq_zero.mp (hh.mp hz))
  have hs2a : Real.sin (2 * a) ≠ 0 := by
    rw [h2a]
    exact (Real.sin_pos_of_pos_of_lt_pi hθ0 hθ).ne'
  have hs2b : Real.sin (2 * b) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hab.1]) (by linarith [hab.2.1,hab.2.2])).ne'
  obtain ⟨hLa,hLg,hMa,hMg⟩ := mono_log_partials p a g hma hpa.ne' hmb.ne' hpb.ne' hs2a hs2b
  have hL := monoL_along (p := p) hG
    (by simpa only [hGa] using hmb.ne') (by simpa only [hGa] using hpb.ne')
    (by simpa only [hGa] using hpa.ne') hs2a hs2b
  have hM := monoM_along (p := p) hG
    (by simpa only [hGa] using hma) (by simpa only [hGa] using hpa.ne')
    (by simpa only [hGa] using hmb.ne') (by simpa only [hGa] using hpb.ne')
  rw [hGa] at hL hM
  have hLlin : HasDerivAt (fun x => monoLogL p x (G x))
      (deriv (fun x => monoLogL p x g) a + deriv (monoLogL p a) g * d) a := by
    apply hL.congr_deriv
    rw [hLa.deriv,hLg.deriv]
    ring
  have hMlin : HasDerivAt (fun x => monoLogM p x (G x))
      (deriv (fun x => monoLogM p x g) a + deriv (monoLogM p a) g * d) a := by
    apply hM.congr_deriv
    rw [hMa.deriv,hMg.deriv]
    ring
  have hnear : ∀ᶠ x : ℝ in 𝓝 a, 2 * x ∈ Set.Ioo 0 Real.pi := by
    have hc : ContinuousAt (fun x : ℝ => 2 * x) a := by fun_prop
    exact hc.eventually (isOpen_Ioo.mem_nhds (by change 2 * a ∈ Set.Ioo 0 Real.pi; rw [h2a]; exact ⟨hθ0,hθ⟩))
  have heqM : (fun x => monoLogM p x (G x)) =ᶠ[𝓝 a] (fun _ => Real.log |lam|) := by
    filter_upwards [hnear] with x hx
    have hh := sec5d_M_level_proved hp1 hp2 hl hl1 hl0 hx.1 hx.2
    rw [show 2 * x / 2 = x by ring] at hh
    exact hh
  have hMzero : HasDerivAt (fun x => monoLogM p x (G x)) 0 a :=
    (hasDerivAt_const a (Real.log |lam|)).congr_of_eventuallyEq heqM
  have hz := hMlin.unique hMzero
  have hS : monoS p a g ≠ 0 := by
    unfold monoS
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hma hpa.ne') hmb.ne') hpb.ne'
  have hmf := (sec5d_M_gamma_formula_proved hp1 hp2 hθ0 hθ hg hga).1.deriv
  have hsα : 0 < Real.sin ((1 - p / 2) * θ) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos (by linarith) hθ0) (by nlinarith [Real.pi_pos])
  have hX : |Real.cos (2 * g)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have hgap := (sec5d_denominator_positive_proved hp1 hp2 hθ0 hθ hX).1
  have hMgnz : deriv (monoLogM p a) g ≠ 0 := by
    rw [hmf]
    exact div_ne_zero (mul_pos hsα hgap).ne' hS
  have hquot : deriv (fun x => monoLogL p x g) a + deriv (monoLogL p a) g * d =
      monoE p a g / deriv (monoLogM p a) g := by
    apply (eq_div_iff hMgnz).mpr
    unfold monoE
    linear_combination deriv (monoLogL p a) g * hz
  have hlam : 0 < 2 * (1 - lam) := by positivity
  have heqK : (fun x => Real.log (curveKf p lam (2 * x))) =ᶠ[𝓝 a]
      (fun x => Real.log (2 * (1 - lam)) + monoLogL p x (G x)) := by
    filter_upwards [hnear] with x hx
    have hh := (sec5d_Kf_log_form_proved hp1 hp2 hl hl1 hx.1 hx.2).1
    rw [show 2 * x / 2 = x by ring] at hh
    rw [hh,Real.log_mul hlam.ne' (Real.exp_pos _).ne',Real.log_exp]
  have hK := ((hasDerivAt_const a (Real.log (2 * (1 - lam)))).add hLlin).congr_of_eventuallyEq heqK
  simp only [zero_add] at hK
  rw [hquot] at hK
  exact ⟨hMgnz,hK⟩

end GKSharp
