/- GKSharp/Proofs/A2Ift.lean - (A2) of Section 5, the text's step "θ is a smooth function of ρ (implicit function
theorem, f_ρ″ ≠ 0) and ρ′(θ)θ′(ρ) = 1" (sec5_sharp_inequality.tex l.86), by the text's own route.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.SharpA2
import GKSharp.Proofs.CriticalClassification
import GKSharp.Proofs.A2Injective

namespace GKSharp.A2Ift

open Filter Topology ComplexConjugate
open scoped ContDiff

variable {p lam : ℝ}

/-- `ρ(θ) = |w(z_θ)|` is smooth on `(0, π)`: near `θ₀` it equals `√(B/A)` (`rho_sq`, l.53), with `A, B > 0` built from
the analytic root `R` (l.48, `curve_root_analytic`). -/
theorem rho_contDiffAt (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) {θ₀ : ℝ} (hθ0 : 0 < θ₀)
    (hθ : θ₀ < Real.pi) : ContDiffAt ℝ ∞ (fun θ => ‖mobW lam (curveZ p lam θ)‖) θ₀ := by
  have hR : ContDiffAt ℝ ∞ (curveR p lam) θ₀ := (curve_root_analytic hp1 hp2 hl hl1 hθ0 hθ).contDiffAt
  have hA : ContDiffAt ℝ ∞ (fun θ => SharpA2.curveA p lam θ) θ₀ := by
    unfold SharpA2.curveA
    fun_prop
  have hB : ContDiffAt ℝ ∞ (fun θ => SharpA2.curveB p lam θ) θ₀ := by
    unfold SharpA2.curveB
    fun_prop
  obtain ⟨-, -, hR0, -, -⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  have hApos := SharpA2.curveA_pos hR0 hθ0 hθ
  have hBpos := SharpA2.curveB_pos hR0 hθ0 hθ
  refine ((hB.div hA hApos.ne').sqrt (div_pos hBpos hApos).ne').congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ0 hθ] with x hx
  rw [Pi.div_apply, ← SharpA2.rho_sq hp1 hp2 hl hl1 hx.1 hx.2, Real.sqrt_sq (norm_nonneg _)]

/-! ### The critical-angle equation `F(ρ, φ) = 0` -/

/-- `ρe^{iφ}` as a function of `(ρ, φ)`. -/
noncomputable def polarPt (v : ℝ × ℝ) : ℂ := (v.1 : ℂ) * Complex.exp ((v.2 : ℂ) * Complex.I)

/-- `F(ρ, φ) = f_ρ′(φ)` in the closed form of (5.3) (l.35). -/
noncomputable def critF (p lam : ℝ) (v : ℝ × ℝ) : ℝ :=
  -(p / 2) * ‖mobQ lam (polarPt v)‖ ^ (p / 2 - 1) *
    (conj (curveV p lam (Complex.arg (mobQ lam (polarPt v)))) * polarPt v).im

theorem critF_eq_deriv (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) {ρ φ : ℝ} (hρ : 0 < ρ)
    (hφ0 : 0 < φ) (hφ : φ < Real.pi) :
    critF p lam (ρ, φ) =
      deriv (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ :=
  ((Proofs.EllipseCalculus.eq_5_3_proved hp1 hp2 hl hl1 hρ hφ0 hφ).2.2.deriv).symm

theorem contDiff_ofReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun x => (f x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

theorem contDiff_polarPt : ContDiff ℝ ∞ polarPt :=
  (contDiff_ofReal contDiff_fst).mul
    ((Complex.contDiff_exp (𝕜 := ℝ)).comp ((contDiff_ofReal contDiff_snd).mul contDiff_const))

theorem contDiff_mobQ_polar : ContDiff ℝ ∞ (fun v => mobQ lam (polarPt v)) :=
  (contDiff_polarPt.sub contDiff_const).mul (contDiff_const.sub (Complex.conjCLE.contDiff.comp contDiff_polarPt))

theorem contDiff_curveV : ContDiff ℝ ∞ (curveV p lam) := by
  have hlin : ContDiff ℝ ∞ (fun θ : ℝ => (((1 - p / 2) * θ : ℝ) : ℂ)) :=
    contDiff_ofReal (contDiff_const.mul contDiff_id)
  have hexp : ContDiff ℝ ∞ Complex.exp := Complex.contDiff_exp
  exact (hexp.comp (hlin.mul contDiff_const)).add (contDiff_const.mul (hexp.comp (hlin.neg.mul contDiff_const)))

/-- `arg Q(ρe^{iφ})` is smooth where `Im Q > 0` (`arg = Im log` on the slit plane). -/
theorem contDiffAt_argQ {u : ℝ × ℝ} (hQ : 0 < (mobQ lam (polarPt u)).im) :
    ContDiffAt ℝ ∞ (fun v => Complex.arg (mobQ lam (polarPt v))) u := by
  have hslit : mobQ lam (polarPt u) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inr hQ.ne')
  have hlog := ((Complex.contDiffAt_log hslit).restrict_scalars ℝ).comp u (contDiff_mobQ_polar (lam := lam)).contDiffAt
  have := Complex.imCLM.contDiff.contDiffAt.comp u hlog
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using this

theorem contDiffAt_critF {u : ℝ × ℝ} (hQ : 0 < (mobQ lam (polarPt u)).im) : ContDiffAt ℝ ∞ (critF p lam) u := by
  have hQc := (contDiff_mobQ_polar (lam := lam)).contDiffAt (x := u)
  have hne : mobQ lam (polarPt u) ≠ 0 := fun h => by rw [h, Complex.zero_im] at hQ; exact lt_irrefl 0 hQ
  have hr := Real.contDiffAt_rpow_const_of_ne (n := ∞) (p := p / 2 - 1) (norm_ne_zero_iff.2 hne)
  have hN := hr.comp u (hQc.norm ℝ hne)
  have hV := (contDiff_curveV (p := p) (lam := lam)).contDiffAt.comp u (contDiffAt_argQ hQ)
  have hIm := Complex.imCLM.contDiff.contDiffAt.comp u
    ((Complex.conjCLE.contDiff.contDiffAt.comp u hV).mul contDiff_polarPt.contDiffAt)
  exact (contDiffAt_const.mul hN).mul hIm

/-- At a critical point, `∂_φF = f_ρ″ ≠ 0` (Lemma A, `eq_5_6_proved`): the partial derivative in `φ` is invertible. -/
theorem critF_partial_invertible (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) {ρ φ : ℝ}
    (hρ : 0 < ρ) (hφ0 : 0 < φ) (hφ : φ < Real.pi)
    (hcrit : deriv (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ = 0)
    (hd : DifferentiableAt ℝ (critF p lam) (ρ, φ)) :
    (fderiv ℝ (critF p lam) (ρ, φ) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
  obtain ⟨hdd, hneg⟩ := Proofs.CriticalMaximum.eq_5_6_proved hp1 hp2 hl hl1 hρ hφ0 hφ hcrit
  have hev : (fun x => critF p lam (ρ, x)) =ᶠ[𝓝 φ]
      deriv (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) := by
    filter_upwards [Ioo_mem_nhds hφ0 hφ] with x hx
    exact critF_eq_deriv hp1 hp2 hl hl1 hρ hx.1 hx.2
  have hc := hdd.congr_of_eventuallyEq hev
  have heq := (hd.hasFDerivAt.comp φ (hasFDerivAt_prodMk_right ρ φ)).unique hc.hasFDerivAt
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hneg.ne), ?_⟩
  rw [heq]
  ext
  simp [ContinuousLinearEquiv.unitsEquivAut_apply]

/-- The curve point `w(θ)` is a critical point of `f_{ρ(θ)}`: `F(|w(θ)|, arg w(θ)) = 0` (classification, "if"). -/
theorem critF_curve (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    critF p lam (‖mobW lam (curveZ p lam θ)‖, Complex.arg (mobW lam (curveZ p lam θ))) = 0 := by
  have him := A2Injective.mobW_curveZ_im_pos hp1 hp2 hl hl1 hθ.1 hθ.2
  have hρ : 0 < ‖mobW lam (curveZ p lam θ)‖ := norm_pos_iff.2 fun h => by
    rw [h, Complex.zero_im] at him; exact lt_irrefl 0 him
  have ha := A2Injective.arg_mem_Ioo_of_im_pos him
  rw [critF_eq_deriv hp1 hp2 hl hl1 hρ ha.1 ha.2]
  exact (Proofs.CriticalClassification.sec5_critical_points_proved hp1 hp2 hl hl1 hρ ha.1 ha.2).2
    (Or.inl ⟨θ, hθ, Complex.norm_mul_exp_arg_mul_I _⟩)

theorem continuousAt_curveW (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) {θ₀ : ℝ}
    (hθ0 : 0 < θ₀) (hθ : θ₀ < Real.pi) : ContinuousAt (fun θ => mobW lam (curveZ p lam θ)) θ₀ := by
  have hR := (curve_root_analytic hp1 hp2 hl hl1 hθ0 hθ).continuousAt
  have hz : ContinuousAt (fun θ => curveZ p lam θ) θ₀ :=
    (Complex.continuous_ofReal.continuousAt.comp hR).mul (by fun_prop)
  exact (continuousAt_const.add (continuousAt_const.mul hz)).div (continuousAt_const.add hz)
    (polar_one_add_ne_zero (A2Injective.curveR_pos hp1 hp2 hl hl1 hθ0 hθ) hθ0 hθ)

/-- (A2), the text's own step, sec5_sharp_inequality.tex l.86: "ρ′ > 0 since θ is a smooth function of ρ (implicit
function theorem, f_ρ″ ≠ 0) and ρ′(θ)θ′(ρ) = 1". The text's route: at `u = (ρ(θ₀), arg w(θ₀))`, `F(u) = 0` and
`∂_φF(u) = f_ρ″ ≠ 0`, so the implicit function theorem (`ContDiffAt.implicitFunction`) gives a smooth `ψ` with
`F(ρ, φ) = 0 ⇔ φ = ψ(ρ)` near `u`; the curve angle `θ(ρ) := arg Q(ρe^{iψ(ρ)})` is then smooth, `θ(ρ(θ)) = θ` (the
classification and `arg Q(w(θ)) = θ`), and `ρ′(θ₀)θ′(ρ(θ₀)) = 1` by the chain rule. No use of `ρ′ > 0`. -/
theorem sec5_A2_ift_proved {θ₀ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ₀) (hθ : θ₀ < Real.pi) :
    DifferentiableAt ℝ (fun θ => ‖mobW lam (curveZ p lam θ)‖) θ₀ ∧
    ∃ g : ℝ → ℝ, (∀ᶠ θ in 𝓝 θ₀, g ‖mobW lam (curveZ p lam θ)‖ = θ) ∧
      ContDiffAt ℝ ∞ g ‖mobW lam (curveZ p lam θ₀)‖ ∧
      deriv (fun θ => ‖mobW lam (curveZ p lam θ)‖) θ₀ * deriv g ‖mobW lam (curveZ p lam θ₀)‖ = 1 := by
  have hρd : DifferentiableAt ℝ (fun θ => ‖mobW lam (curveZ p lam θ)‖) θ₀ :=
    (rho_contDiffAt hp1 hp2 hl hl1 hθ0 hθ).differentiableAt (by simp)
  have him := A2Injective.mobW_curveZ_im_pos hp1 hp2 hl hl1 hθ0 hθ
  have hρ0 : 0 < ‖mobW lam (curveZ p lam θ₀)‖ := norm_pos_iff.2 fun h => by
    rw [h, Complex.zero_im] at him; exact lt_irrefl 0 him
  have ha := A2Injective.arg_mem_Ioo_of_im_pos him
  have hQ : 0 < (mobQ lam (polarPt (‖mobW lam (curveZ p lam θ₀)‖,
      Complex.arg (mobW lam (curveZ p lam θ₀))))).im :=
    (Proofs.EllipseCalculus.eq_5_3_proved hp1 hp2 hl hl1 hρ0 ha.1 ha.2).1
  have hu0 := critF_curve hp1 hp2 hl hl1 ⟨hθ0, hθ⟩
  have cdf := contDiffAt_critF (p := p) hQ
  have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hinv := critF_partial_invertible hp1 hp2 hl hl1 hρ0 ha.1 ha.2
    (by rw [← critF_eq_deriv hp1 hp2 hl hl1 hρ0 ha.1 ha.2]; exact hu0) (cdf.differentiableAt pn)
  have hψs : ContDiffAt ℝ ∞ (cdf.implicitFunction pn hinv) ‖mobW lam (curveZ p lam θ₀)‖ :=
    cdf.contDiffAt_implicitFunction pn hinv
  have hψ0 : cdf.implicitFunction pn hinv ‖mobW lam (curveZ p lam θ₀)‖ =
      Complex.arg (mobW lam (curveZ p lam θ₀)) := cdf.implicitFunction_apply_self pn hinv
  have hiff := cdf.eventually_apply_eq_iff_implicitFunction pn hinv
  -- the curve angle as a function of the radius
  set g : ℝ → ℝ := fun r => Complex.arg (mobQ lam (polarPt (r, cdf.implicitFunction pn hinv r))) with hgdef
  have hgs : ContDiffAt ℝ ∞ g ‖mobW lam (curveZ p lam θ₀)‖ := by
    have hQ' : 0 < (mobQ lam (polarPt (‖mobW lam (curveZ p lam θ₀)‖,
        cdf.implicitFunction pn hinv ‖mobW lam (curveZ p lam θ₀)‖))).im := by rw [hψ0]; exact hQ
    have hf : ContDiffAt ℝ ∞ (fun r => (r, cdf.implicitFunction pn hinv r)) ‖mobW lam (curveZ p lam θ₀)‖ :=
      contDiffAt_id.prodMk hψs
    exact ContDiffAt.comp (f := fun r => (r, cdf.implicitFunction pn hinv r)) _ (contDiffAt_argQ hQ') hf
  have hv : ContinuousAt (fun θ => (‖mobW lam (curveZ p lam θ)‖, Complex.arg (mobW lam (curveZ p lam θ)))) θ₀ :=
    hρd.continuousAt.prodMk (ContinuousAt.comp (f := fun θ => mobW lam (curveZ p lam θ))
      (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.2 (Or.inr him.ne'))) (continuousAt_curveW hp1 hp2 hl hl1 hθ0 hθ))
  have hleft : ∀ᶠ θ in 𝓝 θ₀, g ‖mobW lam (curveZ p lam θ)‖ = θ := by
    filter_upwards [hv.eventually hiff, Ioo_mem_nhds hθ0 hθ] with θ h1 h2
    have h3 : cdf.implicitFunction pn hinv ‖mobW lam (curveZ p lam θ)‖ =
        Complex.arg (mobW lam (curveZ p lam θ)) := h1.1 (by rw [critF_curve hp1 hp2 hl hl1 h2, hu0])
    show Complex.arg (mobQ lam (polarPt (‖mobW lam (curveZ p lam θ)‖,
      cdf.implicitFunction pn hinv ‖mobW lam (curveZ p lam θ)‖))) = θ
    rw [h3]
    show Complex.arg (mobQ lam ((‖mobW lam (curveZ p lam θ)‖ : ℂ) *
      Complex.exp ((Complex.arg (mobW lam (curveZ p lam θ)) : ℂ) * Complex.I))) = θ
    rw [Complex.norm_mul_exp_arg_mul_I]
    exact Proofs.CriticalClassification.polar_arg_Q hl1 (A2Injective.curveR_pos hp1 hp2 hl hl1 h2.1 h2.2) h2.1 h2.2
  refine ⟨hρd, g, hleft, hgs, ?_⟩
  have hcomp := ((hgs.differentiableAt pn).hasDerivAt).comp θ₀ hρd.hasDerivAt
  have hid : HasDerivAt (g ∘ fun θ => ‖mobW lam (curveZ p lam θ)‖) 1 θ₀ :=
    (hasDerivAt_id θ₀).congr_of_eventuallyEq hleft
  rw [mul_comm]
  exact hcomp.unique hid

end GKSharp.A2Ift
