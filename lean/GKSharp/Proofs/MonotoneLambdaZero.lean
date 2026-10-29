/- regularity at lambda = 0, frozen sec5d_monotone.tex:33-35 (rows sec5d_lambda_zero_analytic,
sec5d_lambda_zero_continuity; types verbatim from the approved proposal v020).
Route = the text: at lambda = 0 the radicand of R is sin(p theta/2)^2 > 0, so R, gamma = arctan(tan((p-1)theta/2)
(1+R)/(1-R)) (R < 1) and, by the installed log form K_f = 2(1-lambda) exp L(theta/2, gamma) (-1 < lambda < 1), K_f are
C^n jointly in (lambda, theta) near (0, theta) for every n, analytic included (n = omega). The derivative side is the
partial derivative of a jointly C^1 function, hence continuous in lambda; the sign quotient is continuous because its
denominator is positive for |X| <= 1 (installed sec5d_denominator_positive).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneKfLog
import GKSharp.Proofs.MonotoneCurveAlgebra

open scoped ContDiff Topology

namespace GKSharp

namespace LambdaZero

/-- A jointly `C¹` function has a partial derivative in its second variable that is continuous in the first. -/
theorem continuousAt_deriv_slice {Φ : ℝ × ℝ → ℝ} {l0 a0 : ℝ} (h : ContDiffAt ℝ 1 Φ (l0, a0)) :
    ContinuousAt (fun l => deriv (fun a => Φ (l, a)) a0) l0 := by
  obtain ⟨Φ', u, hu, hcont, hder⟩ := contDiffAt_one_iff.1 h
  have hpath : ContinuousAt (fun l : ℝ => (l, a0)) l0 := (continuous_id.prodMk continuous_const).continuousAt
  have hev : ∀ᶠ l in 𝓝 l0, (l, a0) ∈ u := hpath.preimage_mem_nhds hu
  have heq : (fun l => Φ' (l, a0) (0, 1)) =ᶠ[𝓝 l0] fun l => deriv (fun a => Φ (l, a)) a0 := by
    filter_upwards [hev] with l hl
    exact (((hder _ hl).comp_hasDerivAt a0 ((hasDerivAt_const a0 l).prodMk (hasDerivAt_id a0))).deriv).symm
  have hΦ' : ContinuousAt (fun l : ℝ => Φ' (l, a0)) l0 :=
    ContinuousAt.comp (f := fun l : ℝ => (l, a0)) (hcont.continuousAt hu) hpath
  exact (hΦ'.clm_apply continuousAt_const).congr heq

variable {p θ : ℝ}

theorem contDiff_sin_mul (n : ℕ∞ω) (c : ℝ) : ContDiff ℝ n (fun x : ℝ × ℝ => Real.sin (c * x.2)) :=
  Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)

/-- `R` is `Cⁿ` (every `n`, analytic included) jointly in `(λ, θ)` at `(0, θ)`. -/
theorem contDiffAt_curveR (n : ℕ∞ω) (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    ContDiffAt ℝ n (fun x : ℝ × ℝ => curveR p x.1 x.2) (0, θ) := by
  obtain ⟨hs1, hs12, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  have hb : 0 < Real.sin (p / 2 * θ) := hs1.trans hs12
  have hrad : ContDiffAt ℝ n (fun x : ℝ × ℝ => (1 + x.1) ^ 2 * Real.sin (p / 2 * x.2) ^ 2 -
      4 * x.1 * Real.sin ((1 - p / 2) * x.2) ^ 2) (0, θ) :=
    ((((contDiff_const.add contDiff_fst).pow 2).mul ((contDiff_sin_mul n _).pow 2)).sub
      ((contDiff_const.mul contDiff_fst).mul ((contDiff_sin_mul n _).pow 2))).contDiffAt
  have hrad0 : (1 + (0 : ℝ)) ^ 2 * Real.sin (p / 2 * θ) ^ 2 - 4 * 0 * Real.sin ((1 - p / 2) * θ) ^ 2 ≠ 0 := by
    have := pow_pos hb 2
    norm_num
    exact hb.ne'
  have hden : ContDiffAt ℝ n (fun x : ℝ × ℝ => (1 + x.1) * Real.sin (p / 2 * x.2) +
      Real.sqrt ((1 + x.1) ^ 2 * Real.sin (p / 2 * x.2) ^ 2 - 4 * x.1 * Real.sin ((1 - p / 2) * x.2) ^ 2)) (0, θ) :=
    ((contDiff_const.add contDiff_fst).mul (contDiff_sin_mul n _)).contDiffAt.add (hrad.sqrt hrad0)
  have hden0 : (1 + (0 : ℝ)) * Real.sin (p / 2 * θ) +
      Real.sqrt ((1 + (0 : ℝ)) ^ 2 * Real.sin (p / 2 * θ) ^ 2 - 4 * 0 * Real.sin ((1 - p / 2) * θ) ^ 2) ≠ 0 := by
    have := Real.sqrt_nonneg ((1 + (0 : ℝ)) ^ 2 * Real.sin (p / 2 * θ) ^ 2 - 4 * 0 * Real.sin ((1 - p / 2) * θ) ^ 2)
    have h1 : 0 < (1 + (0 : ℝ)) * Real.sin (p / 2 * θ) := by norm_num; exact hb
    linarith
  exact (contDiff_const.mul (contDiff_sin_mul n _)).contDiffAt.div hden hden0

/-- `γ` is `Cⁿ` jointly in `(λ, θ)` at `(0, θ)`. -/
theorem contDiffAt_curveGamma (n : ℕ∞ω) (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    ContDiffAt ℝ n (fun x : ℝ × ℝ => curveGamma p x.1 x.2) (0, θ) := by
  have hR := contDiffAt_curveR n hp1 hp2 hθ0 hθ
  obtain ⟨-, -, -, -, -, -, hR1, -⟩ := curve_root_unique (lam := 0) hp1 hp2 hθ0 hθ (by norm_num) (by norm_num)
  have hb : (p - 1) * (θ / 2) < θ / 2 := by nlinarith
  have hcos : Real.cos ((p - 1) * (θ / 2)) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by linarith⟩).ne'
  have harg : ContDiffAt ℝ n (fun x : ℝ × ℝ => (p - 1) * (x.2 / 2)) (0, θ) :=
    (contDiff_const.mul (contDiff_snd.div_const 2)).contDiffAt
  have htan : ContDiffAt ℝ n (fun x : ℝ × ℝ => Real.tan ((p - 1) * (x.2 / 2))) (0, θ) :=
    ContDiffAt.comp (g := Real.tan) (f := fun x : ℝ × ℝ => (p - 1) * (x.2 / 2)) ((0 : ℝ), θ)
      (Real.contDiffAt_tan.2 hcos) harg
  have hsub : 1 - curveR p 0 θ ≠ 0 := sub_ne_zero.2 hR1.ne'
  have hin : ContDiffAt ℝ n (fun x : ℝ × ℝ => Real.tan ((p - 1) * (x.2 / 2)) * (1 + curveR p x.1 x.2) /
      (1 - curveR p x.1 x.2)) (0, θ) :=
    (htan.mul (contDiffAt_const.add hR)).div (contDiffAt_const.sub hR) hsub
  exact ContDiffAt.comp (g := Real.arctan) ((0 : ℝ), θ) Real.contDiff_arctan.contDiffAt hin

/-- `K_f` is `Cⁿ` jointly in `(λ, θ)` at `(0, θ)`, through the installed log form. -/
theorem contDiffAt_curveKf (n : ℕ∞ω) (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    ContDiffAt ℝ n (fun x : ℝ × ℝ => curveKf p x.1 x.2) (0, θ) := by
  have hg := contDiffAt_curveGamma n hp1 hp2 hθ0 hθ
  obtain ⟨hgb, hgpi, -, -⟩ := sec5d_gamma_spec_proved (lam := 0) hp1 hp2 (by norm_num) (by norm_num) hθ0 hθ
  have hab : 0 < (p - 1) * (θ / 2) ∧ (p - 1) * (θ / 2) < θ / 2 ∧ θ / 2 < Real.pi / 2 :=
    ⟨mul_pos (by linarith) (half_pos hθ0), by nlinarith, by linarith⟩
  obtain ⟨hpb, hpa, hmb, -, -⟩ := sec5d_gamma_denominators_proved (θ / 2) ((p - 1) * (θ / 2))
    (curveGamma p 0 θ) hab ⟨hgb, hgpi⟩
  have hs2a : 0 < Real.sin (2 * (θ / 2)) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs2b : 0 < Real.sin (2 * ((p - 1) * (θ / 2))) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hab.1]) (by linarith [hab.2.1, hab.2.2])
  have ha : ContDiffAt ℝ n (fun x : ℝ × ℝ => x.2 / 2) (0, θ) := (contDiff_snd.div_const 2).contDiffAt
  have logsin : ∀ {u : ℝ × ℝ → ℝ}, ContDiffAt ℝ n u (0, θ) → 0 < Real.sin (u (0, θ)) →
      ContDiffAt ℝ n (fun x => Real.log (Real.sin (u x))) (0, θ) := fun hu hpos =>
    (ContDiffAt.comp (g := Real.sin) ((0 : ℝ), θ) Real.contDiff_sin.contDiffAt hu).log hpos.ne'
  have hL : ContDiffAt ℝ n (fun x : ℝ × ℝ => monoLogL p (x.2 / 2) (curveGamma p x.1 x.2)) (0, θ) := by
    unfold monoLogL
    exact (((((contDiffAt_const.mul (logsin (hg.sub (contDiffAt_const.mul ha)) hmb)).add
      (contDiffAt_const.mul (logsin (hg.add (contDiffAt_const.mul ha)) hpb))).add
      (contDiffAt_const.mul (logsin (contDiffAt_const.mul ha) hs2a))).sub
      (contDiffAt_const.mul (logsin (hg.add ha) hpa))).sub
      (logsin (contDiffAt_const.mul (contDiffAt_const.mul ha)) hs2b))
  have hF : ContDiffAt ℝ n (fun x : ℝ × ℝ =>
      2 * (1 - x.1) * Real.exp (monoLogL p (x.2 / 2) (curveGamma p x.1 x.2))) (0, θ) :=
    (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_fst)).mul hL.exp
  have hU : Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo 0 Real.pi ∈ 𝓝 ((0 : ℝ), θ) :=
    prod_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)) (Ioo_mem_nhds hθ0 hθ)
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [hU] with x hx
  exact (sec5d_Kf_log_form_proved hp1 hp2 hx.1.1 hx.1.2 hx.2.1 hx.2.2).1

/-- The slice `λ ↦ (λ, θ)` is smooth. -/
theorem contDiffAt_slice (n : ℕ∞ω) (θ : ℝ) : ContDiffAt ℝ n (fun lam : ℝ => (lam, θ)) 0 :=
  (contDiff_id.prodMk contDiff_const).contDiffAt

end LambdaZero

open LambdaZero

theorem sec5d_lambda_zero_analytic_proved {p θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    AnalyticAt ℝ (fun lam => curveR p lam θ) 0 ∧
    AnalyticAt ℝ (fun lam => curveKf p lam θ) 0 ∧ 0 < curveKf p 0 θ := by
  refine ⟨?_, ?_, (sec5d_Kf_log_form_proved hp1 hp2 (by norm_num) (by norm_num) hθ0 hθ).2⟩
  · exact (ContDiffAt.comp (f := fun lam : ℝ => (lam, θ)) 0 (contDiffAt_curveR ω hp1 hp2 hθ0 hθ)
      (contDiffAt_slice ω θ)).analyticAt
  · exact (ContDiffAt.comp (f := fun lam : ℝ => (lam, θ)) 0 (contDiffAt_curveKf ω hp1 hp2 hθ0 hθ)
      (contDiffAt_slice ω θ)).analyticAt

theorem sec5d_lambda_zero_continuity_proved {p θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    ContDiffAt ℝ ∞ (fun lam => curveGamma p lam θ) 0 ∧
    ContinuousAt (fun lam => deriv (fun a => Real.log (curveKf p lam (2 * a))) (θ / 2)) 0 ∧
    ContinuousAt (fun lam => monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ)) /
      monoSignDenominator p θ (Real.cos (2 * curveGamma p lam θ))) 0 := by
  have hγ : ContDiffAt ℝ ∞ (fun lam => curveGamma p lam θ) 0 :=
    ContDiffAt.comp (f := fun lam : ℝ => (lam, θ)) 0 (contDiffAt_curveGamma ∞ hp1 hp2 hθ0 hθ)
      (contDiffAt_slice ∞ θ)
  refine ⟨hγ, ?_, ?_⟩
  · have h2θ0 : 0 < 2 * (θ / 2) := by linarith
    have h2θ : 2 * (θ / 2) < Real.pi := by linarith
    have hK := contDiffAt_curveKf 1 hp1 hp2 h2θ0 h2θ
    have hpos := (sec5d_Kf_log_form_proved (lam := 0) hp1 hp2 (by norm_num) (by norm_num) h2θ0 h2θ).2
    have hmap : ContDiffAt ℝ 1 (fun x : ℝ × ℝ => (x.1, 2 * x.2)) ((0 : ℝ), θ / 2) :=
      (contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)).contDiffAt
    have hΦ : ContDiffAt ℝ 1 (fun x : ℝ × ℝ => Real.log (curveKf p x.1 (2 * x.2))) ((0 : ℝ), θ / 2) :=
      (ContDiffAt.comp (f := fun x : ℝ × ℝ => (x.1, 2 * x.2)) ((0 : ℝ), θ / 2) hK hmap).log hpos.ne'
    exact continuousAt_deriv_slice hΦ
  · have hγc := hγ.continuousAt
    have hX : ContinuousAt (fun lam => Real.cos (2 * curveGamma p lam θ)) 0 :=
      Real.continuous_cos.continuousAt.comp (continuousAt_const.mul hγc)
    have hPi : ContinuousAt (fun lam => monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ))) 0 := by
      unfold monoPi
      fun_prop
    have hD : ContinuousAt (fun lam => monoSignDenominator p θ (Real.cos (2 * curveGamma p lam θ))) 0 := by
      unfold monoSignDenominator
      fun_prop
    have hD0 := (sec5d_denominator_positive_proved hp1 hp2 hθ0 hθ
      (Real.abs_cos_le_one (2 * curveGamma p 0 θ))).2
    exact hPi.div hD hD0.ne'

end GKSharp
