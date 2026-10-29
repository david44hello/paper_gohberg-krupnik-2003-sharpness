/-
CstarLambdaSecond.lean — project019 Section5e, second derivative at the contact angle.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.Sec5Eq58
import GKSharp.Proofs.SharpA2
import GKSharp.Proofs.Contact

namespace GKSharp.Proofs.CstarLambdaSecond

open GKSharp ComplexConjugate Filter Topology
open scoped ContDiff

noncomputable abbrev curveW (p lam θ : ℝ) : ℂ := mobW lam (curveZ p lam θ)
noncomputable abbrev curveRho (p lam θ : ℝ) : ℝ := ‖curveW p lam θ‖
noncomputable abbrev curveTau (p lam θ : ℝ) : ℝ := curveRho p lam θ / ‖curveV p lam θ‖
noncomputable abbrev lamCurve (p C K lam θ : ℝ) : ℝ :=
  mobPhi p C K lam (curveW p lam θ) / (1 - lam) ^ p
noncomputable def curveFactor (p lam θ : ℝ) : ℝ :=
  p / 2 * ‖mobQ lam (curveW p lam θ)‖ ^ (p / 2 - 1) *
    (2 * curveTau p lam θ * Real.cos ((1 - p / 2) * θ) - 1) *
    (curveRho p lam θ * deriv (curveRho p lam) θ / curveTau p lam θ)

lemma curveW_smooth {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    ContDiffAt ℝ ∞ (curveW p lam) θ := by
  have hR : ContDiffAt ℝ ∞ (curveR p lam) θ :=
    (curve_root_analytic hp1 hp2 hl hl1 hθ0 hθ).contDiffAt
  have hRc : ContDiffAt ℝ ∞ (fun x => (curveR p lam x : ℂ)) θ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp θ hR
  have hi : ContDiffAt ℝ ∞ (fun x : ℝ => (x : ℂ)) θ := Complex.ofRealCLM.contDiff.contDiffAt
  have hphase : ContDiffAt ℝ ∞ (fun x : ℝ => Complex.exp (-(x : ℂ) * Complex.I)) θ :=
    (hi.neg.mul contDiffAt_const).cexp
  have hz : ContDiffAt ℝ ∞ (curveZ p lam) θ := hRc.mul hphase
  have hR0 := (curve_root_formula hp1 hp2 hθ0 hθ hl hl1).2.2.1
  have hden : 1 + curveZ p lam θ ≠ 0 := polar_one_add_ne_zero hR0 hθ0 hθ
  have hm : ContDiffAt ℂ ∞ (mobW lam) (curveZ p lam θ) := by
    exact (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)).div
      (contDiffAt_const.add contDiffAt_id) hden
  exact (hm.restrict_scalars ℝ).comp θ hz

lemma smooth_factors {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    ContDiffAt ℝ ∞ (curveFactor p lam) θ ∧ ContDiffAt ℝ ∞ (curveKf p lam) θ := by
  obtain ⟨hWV, hwi, _, hN, hE⟩ := Sec5GradPhi.curve_facts hp1 hp2 hl hl1 hθ0 hθ
  have hw0 : curveW p lam θ ≠ 0 := by intro hh; simpa [hh] using hwi
  have hV0 : curveV p lam θ ≠ 0 := by
    intro hh
    apply hw0
    change mobW lam (curveZ p lam θ) = 0
    rw [hWV, hh, mul_zero]
  have hQ0 : mobQ lam (curveW p lam θ) ≠ 0 := norm_pos_iff.mp hN
  have hw := curveW_smooth hp1 hp2 hl hl1 hθ0 hθ
  have hr : ContDiffAt ℝ ∞ (curveRho p lam) θ := hw.norm ℂ hw0
  have harg : ContDiffAt ℝ ∞ (fun x : ℝ => (((1 - p / 2) * x : ℝ) : ℂ)) θ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp θ (contDiffAt_const.mul contDiffAt_id)
  have hv : ContDiffAt ℝ ∞ (fun x => curveV p lam x) θ :=
    (harg.mul contDiffAt_const).cexp.add (contDiffAt_const.mul (harg.neg.mul contDiffAt_const).cexp)
  have hvn : ContDiffAt ℝ ∞ (fun x => ‖curveV p lam x‖) θ := hv.norm ℂ hV0
  have hτ : ContDiffAt ℝ ∞ (curveTau p lam) θ := hr.div hvn (norm_ne_zero_iff.mpr hV0)
  have hτ0 : curveTau p lam θ ≠ 0 := div_ne_zero (norm_ne_zero_iff.mpr hw0) (norm_ne_zero_iff.mpr hV0)
  have hmob : ContDiff ℝ ∞ (mobQ lam) :=
    (contDiff_id.sub contDiff_const).mul (contDiff_const.sub Complex.conjCLE.contDiff)
  have hQ : ContDiffAt ℝ ∞ (fun x => ‖mobQ lam (curveW p lam x)‖) θ :=
    (hmob.contDiffAt.comp θ hw).norm ℂ hQ0
  have hcos : ContDiffAt ℝ ∞ (fun x => Real.cos ((1 - p / 2) * x)) θ := by fun_prop
  have hEs : ContDiffAt ℝ ∞ (fun x => 2 * curveTau p lam x * Real.cos ((1 - p / 2) * x) - 1) θ :=
    ((contDiffAt_const.mul hτ).mul hcos).sub contDiffAt_const
  have hr' : ContDiffAt ℝ ∞ (deriv (curveRho p lam)) θ := hr.derivWithin (by simp)
  constructor
  · exact ((contDiffAt_const.mul (hQ.rpow_const_of_ne (norm_ne_zero_iff.mpr hQ0))).mul hEs).mul
      ((hr.mul hr').div hτ hτ0)
  · exact (((contDiffAt_const.mul (hr.rpow_const_of_ne (norm_ne_zero_iff.mpr hw0))).mul hτ).mul
      (hQ.rpow_const_of_ne (norm_ne_zero_iff.mpr hQ0))).div hEs hE.ne'

theorem sec5e_Lambda_second_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1) :
    let θ₀ := Real.pi / p
    let w := mobW lam (curveZ p lam θ₀)
    let τ := ‖w‖ / ‖curveV p lam θ₀‖
    let F := p / 2 * ‖mobQ lam w‖ ^ (p / 2 - 1) * (2 * τ * Real.cos ((1 - p / 2) * θ₀) - 1) *
      (‖w‖ * deriv (fun x => ‖mobW lam (curveZ p lam x)‖) θ₀ / τ)
    HasDerivAt (deriv (lamCurve p (gk p lam) (kConst p lam) lam))
      (F / (1 - lam) ^ p * (-deriv (curveKf p lam) θ₀)) θ₀ ∧ 0 < F / (1 - lam) ^ p := by
  intro θ₀ w τ F
  have hl : -1 ≤ lam := by linarith
  have hθ0 : 0 < θ₀ := div_pos Real.pi_pos (by linarith)
  have hθ : θ₀ < Real.pi := div_lt_self Real.pi_pos hp1
  have hA2 := sec5_A2_proved hp1 hp2 hl hl1
  have hpos (x : ℝ) (hx : x ∈ Set.Ioo 0 Real.pi) : 0 < deriv (curveRho p lam) x :=
    hA2.2.2.2.2.2.2.1 x hx
  have hmain := Sec5Eq58.eq_5_8_of_rho_deriv_pos (C := gk p lam) (K := kConst p lam)
    hp1 hp2 hl hl1 hθ0 hθ (hpos θ₀ ⟨hθ0, hθ⟩)
  refine ⟨?_, hmain.2.2.2⟩
  have hnear : deriv (lamCurve p (gk p lam) (kConst p lam) lam) =ᶠ[𝓝 θ₀]
      (fun x => curveFactor p lam x / (1 - lam) ^ p * (kConst p lam - curveKf p lam x)) := by
    filter_upwards [Ioo_mem_nhds hθ0 hθ] with x hx
    exact (Sec5Eq58.eq_5_8_of_rho_deriv_pos (C := gk p lam) (K := kConst p lam)
      hp1 hp2 hl hl1 hx.1 hx.2 (hpos x hx)).2.2.1.deriv
  obtain ⟨hFs, hKs⟩ := smooth_factors hp1 hp2 hl hl1 hθ0 hθ
  have hd := (hFs.differentiableAt (by simp)).hasDerivAt.div_const ((1 - lam) ^ p)
  have hk := (hasDerivAt_const θ₀ (kConst p lam)).sub ((hKs.differentiableAt (by simp)).hasDerivAt)
  have hprod := (hd.mul hk).congr_of_eventuallyEq hnear
  convert hprod using 1
  have hcontact : curveKf p lam θ₀ = kConst p lam := contact_Kf hp1 hp2 hl hl1
  simp only [Pi.sub_apply, hcontact, sub_self, mul_zero, zero_sub, zero_add]
  rfl

end GKSharp.Proofs.CstarLambdaSecond

#print axioms GKSharp.Proofs.CstarLambdaSecond.sec5e_Lambda_second_proved
