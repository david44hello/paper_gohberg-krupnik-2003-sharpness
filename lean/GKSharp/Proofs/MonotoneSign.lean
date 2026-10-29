/- sign formula and one-variable assembly, frozen short v0.70 sec5d.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneLevelDerivative
import GKSharp.Proofs.MonotoneDeterminant
import GKSharp.Proofs.MonotoneLambdaZero

namespace GKSharp

open Filter Topology
open scoped ContDiff

private theorem determinant_ratio (A E S N P : ℝ) (hA : A ≠ 0) (hS : S ≠ 0) (hN : N ≠ 0)
    (heq : A * E * S = P) : E / (N / S) = P / (A * N) := by
  field_simp [hA,hS,hN]
  <;> linear_combination heq

theorem log_derivative_nonzero {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hl0 : lam ≠ 0) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    HasDerivAt (fun a => Real.log (curveKf p lam (2 * a)))
      (monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ)) /
        monoSignDenominator p θ (Real.cos (2 * curveGamma p lam θ))) (θ / 2) := by
  let g := curveGamma p lam θ
  let A := 2 * Real.sin θ * Real.sin ((p - 1) * θ)
  let S := monoS p (θ / 2) g
  let N := Real.sin ((1 - p / 2) * θ) *
    (Real.cos ((1 - p / 2) * θ) - Real.cos (2 * g) * Real.cos (p / 2 * θ))
  let P := monoPi (p - 1) θ (Real.cos (2 * g))
  let D := monoSignDenominator p θ (Real.cos (2 * g))
  obtain ⟨hgb,hgpi,-,-⟩ := sec5d_gamma_spec_proved hp1 hp2 hl hl1 hθ0 hθ
  have hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2 := ⟨hgb,hgpi⟩
  have hga : g ≠ θ / 2 := by
    intro hz
    exact hl0 ((sec5d_lambda_gamma_sign_proved hp1 hp2 hl hl1 hθ0 hθ).2.1.mpr hz)
  have hlevel := sec5d_level_derivative_proved hp1 hp2 hl hl1 hl0 hθ0 hθ
  have hmg : deriv (monoLogM p (θ / 2)) g = N / S :=
    (sec5d_M_gamma_formula_proved hp1 hp2 hθ0 hθ hg hga).1.deriv
  have hN : N ≠ 0 := by
    intro hz
    apply hlevel.1
    rw [hmg,hz,zero_div]
  have hS : S ≠ 0 := by
    intro hz
    apply hlevel.1
    rw [hmg,hz,div_zero]
  have hD := (sec5d_denominator_positive_proved hp1 hp2 hθ0 hθ (Real.abs_cos_le_one (2 * g))).2
  have hDdef : D = A * N := by unfold D A N monoSignDenominator; ring
  have hA : A ≠ 0 := by
    intro hz
    have hh := hDdef
    rw [hz,zero_mul] at hh
    exact hD.ne' hh
  have hE : A * monoE p (θ / 2) g * S = P := sec5d_E_identity_proved hp1 hp2 hθ0 hθ hg hga
  have hratio : monoE p (θ / 2) g / deriv (monoLogM p (θ / 2)) g = P / D := by
    rw [hmg,hDdef]
    exact determinant_ratio _ _ _ _ _ hA hS hN hE
  exact hlevel.2.congr_deriv hratio

set_option maxHeartbeats 1200000 in
theorem lemma_signformula_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    HasDerivAt (fun a => Real.log (curveKf p lam (2 * a)))
      (monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ)) /
        monoSignDenominator p θ (Real.cos (2 * curveGamma p lam θ))) (θ / 2) ∧
    0 < monoSignDenominator p θ (Real.cos (2 * curveGamma p lam θ)) := by
  refine ⟨?_,(sec5d_denominator_positive_proved hp1 hp2 hθ0 hθ (Real.abs_cos_le_one _)).2⟩
  by_cases hl0 : lam = 0
  · subst lam
    let F : ℝ → ℝ := fun l => deriv (fun a => Real.log (curveKf p l (2 * a))) (θ / 2)
    let Q : ℝ → ℝ := fun l => monoPi (p - 1) θ (Real.cos (2 * curveGamma p l θ)) /
      monoSignDenominator p θ (Real.cos (2 * curveGamma p l θ))
    have hcont := sec5d_lambda_zero_continuity_proved hp1 hp2 hθ0 hθ
    have hF : ContinuousAt F 0 := hcont.2.1
    have hQ : ContinuousAt Q 0 := hcont.2.2
    have hsmall : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝[≠] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
    have hn : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), t ≠ 0 := by
      filter_upwards [(self_mem_nhdsWithin : ({0} : Set ℝ)ᶜ ∈ 𝓝[≠] (0 : ℝ))] with t ht
      simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using ht
    have heq : F =ᶠ[𝓝[≠] (0 : ℝ)] Q := by
      filter_upwards [hsmall,hn] with t ht htn
      exact (log_derivative_nonzero hp1 hp2 ht.1 ht.2 htn hθ0 hθ).deriv
    have hf : Tendsto F (𝓝[≠] (0 : ℝ)) (𝓝 (F 0)) := hF.tendsto.mono_left inf_le_left
    have hq : Tendsto Q (𝓝[≠] (0 : ℝ)) (𝓝 (Q 0)) := hQ.tendsto.mono_left inf_le_left
    have heq0 : F 0 = Q 0 := tendsto_nhds_unique (hf.congr' heq) hq
    let a := θ / 2
    have h2a : 2 * a = θ := by dsimp [a]; ring
    have hj : ContDiffAt ℝ 1 (fun x : ℝ × ℝ => curveKf p x.1 x.2) (0,2 * a) := by
      rw [h2a]
      exact LambdaZero.contDiffAt_curveKf 1 hp1 hp2 hθ0 hθ
    have hpath : DifferentiableAt ℝ (fun x : ℝ => ((0 : ℝ),2 * x)) a := by fun_prop
    have hk := (hj.differentiableAt (by norm_num)).comp a hpath
    have hk0 : curveKf p 0 (2 * a) ≠ 0 := by
      rw [h2a]
      exact (curveKf_positive_proved hp1 hp2 (by norm_num) (by norm_num) hθ0 hθ).ne'
    have hlog : DifferentiableAt ℝ (fun x => Real.log (curveKf p 0 (2 * x))) a := hk.log hk0
    exact hlog.hasDerivAt.congr_deriv heq0
  · exact log_derivative_nonzero hp1 hp2 hl hl1 hl0 hθ0 hθ

theorem lemma_onevar_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    DifferentiableAt ℝ (curveKf p lam) θ ∧
    SignType.sign (deriv (curveKf p lam) θ) =
      SignType.sign (4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 -
        monoPsi (p / (2 - p)) ((1 - p / 2) * θ)) := by
  apply sec5d_onevar_of_log_derivative ?_ hp1 hp2 hl hl1 hθ0 hθ
  intro p lam θ hp1 hp2 hl hl1 hθ0 hθ
  exact (lemma_signformula_proved hp1 hp2 hl hl1 hθ0 hθ).1

theorem sec5d_Pi_increase_iff_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (0 < deriv (curveKf p lam) θ ↔ 0 < monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ))) := by
  have hs := (lemma_onevar_proved hp1 hp2 hl hl1 hθ0 hθ).2.trans
    (sec5d_Pi_Psi_sign_proved hp1 hp2 hl hl1 hθ0 hθ).2.symm
  constructor
  · intro hd
    exact sign_eq_one_iff.mp (hs.symm.trans (sign_eq_one_iff.mpr hd))
  · intro hd
    exact sign_eq_one_iff.mp (hs.trans (sign_eq_one_iff.mpr hd))

theorem sec5d_onevar_increase_iff_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (0 < deriv (curveKf p lam) θ ↔ monoPsi (p / (2 - p)) ((1 - p / 2) * θ) <
      4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2) := by
  have hs := (lemma_onevar_proved hp1 hp2 hl hl1 hθ0 hθ).2
  constructor
  · intro hd
    exact sub_pos.mp (sign_eq_one_iff.mp (hs.symm.trans (sign_eq_one_iff.mpr hd)))
  · intro hd
    exact sign_eq_one_iff.mp (hs.trans (sign_eq_one_iff.mpr (sub_pos.mpr hd)))

end GKSharp
