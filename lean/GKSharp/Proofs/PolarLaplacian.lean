/- GKSharp/Proofs/PolarLaplacian.lean - slice_O16 (sec2_obstacle.tex l.58): for smooth 2π-periodic φ, the Laplacian
of r^q φ(t) is r^{q-2}(φ'' + q²φ) at every z = r e^{it}, r > 0 (the sum of the two second derivatives along the
horizontal and the vertical line through z).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential

namespace GKSharp.O16

open Complex Filter Topology

variable {q : ℝ} {φ : ℝ → ℝ}

/-- A `2π`-periodic function takes equal values at angles that agree mod `2π`. -/
theorem periodic_angle (hper : Function.Periodic φ (2 * Real.pi)) {α β : ℝ} (h : (α : Real.Angle) = β) :
    φ α = φ β := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h
  rw [show α = β + k * (2 * Real.pi) by linear_combination hk]
  exact hper.int_mul k β

theorem norm_polar {r : ℝ} (hr : 0 < r) (t : ℝ) : ‖(r : ℂ) * unitPoint t‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, unitPoint, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- `arg(r e^{it}) ≡ t` (mod `2π`). -/
theorem arg_polar_coe_angle {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (Complex.arg ((r : ℂ) * unitPoint t) : Real.Angle) = t := by
  have h : (r : ℂ) * unitPoint t =
      r * (↑(Real.Angle.cos (t : Real.Angle)) + ↑(Real.Angle.sin (t : Real.Angle)) * I) := by
    rw [unitPoint, Complex.exp_mul_I, Real.Angle.cos_coe, Real.Angle.sin_coe, Complex.ofReal_cos,
      Complex.ofReal_sin]
  rw [h, arg_mul_cos_add_sin_mul_I_coe_angle hr]

/-- Near `z₀` (`|z₀| = r`, `arg z₀ ≡ t`): with `L = log(w/z₀)`, `u(w) = r^q exp(q Re L) φ(t + Im L)` whenever
`w/z₀ ∈ slitPlane` (the jump of `arg` is absorbed by the periodicity of `φ`). -/
theorem angularPotential_eq_log (hper : Function.Periodic φ (2 * Real.pi)) {r t : ℝ} (hr : 0 < r) {z0 w : ℂ}
    (hn0 : ‖z0‖ = r) (harg : (arg z0 : Real.Angle) = t) (hw : w / z0 ∈ slitPlane) :
    angularPotential q φ w = r ^ q * (Real.exp (q * (log (w / z0)).re) * φ (t + (log (w / z0)).im)) := by
  have hz0ne : z0 ≠ 0 := by rw [← norm_ne_zero_iff, hn0]; exact hr.ne'
  obtain ⟨v, rfl⟩ : ∃ v, w = z0 * v := ⟨w / z0, by field_simp⟩
  rw [mul_div_cancel_left₀ v hz0ne] at hw ⊢
  have hvne : v ≠ 0 := slitPlane_ne_zero hw
  have hang : φ (arg (z0 * v)) = φ (t + arg v) :=
    periodic_angle hper (by rw [arg_mul_coe_angle hz0ne hvne, harg, Real.Angle.coe_add])
  unfold angularPotential
  rw [log_re, log_im, norm_mul, hn0, Real.mul_rpow hr.le (norm_nonneg _),
    Real.rpow_def_of_pos (norm_pos_iff.2 hvne), mul_comm (Real.log ‖v‖) q, hang]
  ring

theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {s : ℝ} (h : HasDerivAt f f' s) :
    HasDerivAt (fun x => (f x).re) f'.re s := by
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h
  simpa only [Function.comp_def, Complex.reCLM_apply] using this

theorem hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {s : ℝ} (h : HasDerivAt f f' s) :
    HasDerivAt (fun x => (f x).im) f'.im s := by
  have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s h
  simpa only [Function.comp_def, Complex.imCLM_apply] using this

/-- Real calculus: if `u = C exp(q a) φ(t + b)` on an open `U ∋ s₀`, then `u″(s₀)` is the chain-rule expression. -/
theorem deriv2_exp_mul (hφ : ContDiff ℝ 2 φ) (C t : ℝ) {a b A1 B1 : ℝ → ℝ} {A2 B2 s₀ : ℝ} {U : Set ℝ}
    (hUo : IsOpen U) (hs0 : s₀ ∈ U) (ha : ∀ s ∈ U, HasDerivAt a (A1 s) s) (hb : ∀ s ∈ U, HasDerivAt b (B1 s) s)
    (hA : HasDerivAt A1 A2 s₀) (hB : HasDerivAt B1 B2 s₀) {u : ℝ → ℝ}
    (hu : ∀ s ∈ U, u s = C * (Real.exp (q * a s) * φ (t + b s))) :
    deriv (deriv u) s₀ = C * Real.exp (q * a s₀) * (q ^ 2 * A1 s₀ ^ 2 * φ (t + b s₀) + q * A2 * φ (t + b s₀) +
      2 * q * A1 s₀ * B1 s₀ * deriv φ (t + b s₀) + deriv (deriv φ) (t + b s₀) * B1 s₀ ^ 2 +
      deriv φ (t + b s₀) * B2) := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφdd : Differentiable ℝ (deriv φ) := hφ.differentiable_deriv_two
  have hu' : ∀ s ∈ U, HasDerivAt u (C * (Real.exp (q * a s) * (q * A1 s) * φ (t + b s) +
      Real.exp (q * a s) * (deriv φ (t + b s) * B1 s))) s := by
    intro s hs
    have h1 := ((ha s hs).const_mul q).exp
    have h2 := (hφd (t + b s)).hasDerivAt.comp s ((hb s hs).const_add t)
    have hF : HasDerivAt (fun x => C * (Real.exp (q * a x) * φ (t + b x))) _ s := (h1.mul h2).const_mul C
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [hUo.mem_nhds hs] with x hx
    exact hu x hx
  have hEq : deriv u =ᶠ[𝓝 s₀] fun s => C * (Real.exp (q * a s) * (q * A1 s) * φ (t + b s) +
      Real.exp (q * a s) * (deriv φ (t + b s) * B1 s)) := by
    filter_upwards [hUo.mem_nhds hs0] with x hx
    exact (hu' x hx).deriv
  have hE := ((ha s₀ hs0).const_mul q).exp
  have hΦ := (hφd (t + b s₀)).hasDerivAt.comp s₀ ((hb s₀ hs0).const_add t)
  have hΦd := (hφdd (t + b s₀)).hasDerivAt.comp s₀ ((hb s₀ hs0).const_add t)
  have hF' : HasDerivAt (fun s => C * (Real.exp (q * a s) * (q * A1 s) * φ (t + b s) +
      Real.exp (q * a s) * (deriv φ (t + b s) * B1 s))) _ s₀ :=
    (((hE.mul (hA.const_mul q)).mul hΦ).add (hE.mul (hΦd.mul hB))).const_mul C
  rw [hEq.deriv_eq, hF'.deriv]
  simp only [Function.comp_apply, Pi.mul_apply]
  ring

/-- Second derivative of `u = angularPotential q φ` along a line `γ` (`γ′ ≡ d`) through `z₀ = γ(s₀)`,
`|z₀| = r > 0`, `arg z₀ ≡ t`: `L = log(γ/z₀)` has `L′ = d/γ`, `L″(s₀) = -d²/z₀²`, `L(s₀) = 0`. -/
theorem deriv2_line (hφ : ContDiff ℝ 2 φ) (hper : Function.Periodic φ (2 * Real.pi)) {r t : ℝ} (hr : 0 < r)
    {z0 : ℂ} (hn0 : ‖z0‖ = r) (harg : (arg z0 : Real.Angle) = t) {γ : ℝ → ℂ} {d : ℂ} {s₀ : ℝ}
    (hγ : ∀ s, HasDerivAt γ d s) (hγ0 : γ s₀ = z0) :
    deriv (deriv fun s => angularPotential q φ (γ s)) s₀ =
      r ^ q * (q ^ 2 * (d / z0).re ^ 2 * φ t + q * ((0 * z0 - d * d) / z0 ^ 2).re * φ t +
        2 * q * (d / z0).re * (d / z0).im * deriv φ t + deriv (deriv φ) t * (d / z0).im ^ 2 +
        deriv φ t * ((0 * z0 - d * d) / z0 ^ 2).im) := by
  have hz0ne : z0 ≠ 0 := by rw [← norm_ne_zero_iff, hn0]; exact hr.ne'
  have hcont : Continuous γ := continuous_iff_continuousAt.2 fun s => (hγ s).continuousAt
  have hUo : IsOpen {s | γ s / z0 ∈ slitPlane} := isOpen_slitPlane.preimage (hcont.div_const z0)
  have hs0 : s₀ ∈ {s | γ s / z0 ∈ slitPlane} := by
    show γ s₀ / z0 ∈ slitPlane
    rw [hγ0, div_self hz0ne]
    exact one_mem_slitPlane
  have hγne : ∀ s ∈ {s | γ s / z0 ∈ slitPlane}, γ s ≠ 0 := fun s hs h =>
    slitPlane_ne_zero hs (by rw [h, zero_div])
  have hL : ∀ s ∈ {s | γ s / z0 ∈ slitPlane}, HasDerivAt (fun s => log (γ s / z0)) (d / γ s) s := by
    intro s hs
    have h := ((hγ s).div_const z0).clog_real hs
    have he : d / z0 / (γ s / z0) = d / γ s := by
      have := hγne s hs
      field_simp
    rwa [he] at h
  have hL1 := (hasDerivAt_const s₀ d).div (hγ s₀) (hγne s₀ hs0)
  have h := deriv2_exp_mul (q := q) hφ (r ^ q) t hUo hs0 (fun s hs => hasDerivAt_re (hL s hs))
    (fun s hs => hasDerivAt_im (hL s hs)) (hasDerivAt_re hL1) (hasDerivAt_im hL1)
    (u := fun s => angularPotential q φ (γ s)) (fun s hs => angularPotential_eq_log hper hr hn0 harg hs)
  rw [h, hγ0, div_self hz0ne, log_one, zero_re, zero_im, mul_zero, Real.exp_zero, mul_one, add_zero]

/-- O16, sec2_obstacle.tex l.58: the classical polar Laplacian identity `Δ(r^q φ(t)) = r^{q-2}(φ″ + q²φ)` for smooth
`2π`-periodic `φ`, at `z = r e^{it}`, `r > 0` (`Δ` = the sum of the second derivatives along the horizontal and the
vertical line through `z`). -/
theorem slice_O16_proved (q : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hper : Function.Periodic φ (2 * Real.pi)) (r t : ℝ) (hr : 0 < r) :
    deriv (deriv fun x : ℝ => angularPotential q φ ((x : ℂ) + ((((r : ℂ) * unitPoint t)).im : ℂ) * Complex.I))
        ((r : ℂ) * unitPoint t).re +
      deriv (deriv fun y : ℝ => angularPotential q φ (((((r : ℂ) * unitPoint t)).re : ℂ) + (y : ℂ) * Complex.I))
        ((r : ℂ) * unitPoint t).im =
      r ^ (q - 2) * (deriv (deriv φ) t + q ^ 2 * φ t) := by
  have hn0 := norm_polar hr t
  have harg := arg_polar_coe_angle hr t
  generalize (r : ℂ) * unitPoint t = z0 at hn0 harg ⊢
  have hz0ne : z0 ≠ 0 := by rw [← norm_ne_zero_iff, hn0]; exact hr.ne'
  have hh : ∀ s : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ) + (z0.im : ℂ) * I) 1 s := fun s => by
    simpa using ((hasDerivAt_id' s).ofReal_comp).add_const ((z0.im : ℂ) * I)
  have hv : ∀ s : ℝ, HasDerivAt (fun y : ℝ => (z0.re : ℂ) + (y : ℂ) * I) I s := fun s => by
    simpa using (((hasDerivAt_id' s).ofReal_comp).mul_const I).const_add (z0.re : ℂ)
  rw [deriv2_line (q := q) hφ hper hr hn0 harg hh (Complex.re_add_im z0),
    deriv2_line (q := q) hφ hper hr hn0 harg hv (Complex.re_add_im z0)]
  have e1 : (0 * z0 - 1 * 1) / z0 ^ 2 = -((1 / z0) * (1 / z0)) := by field_simp; ring
  have e2 : (0 * z0 - I * I) / z0 ^ 2 = (1 / z0) * (1 / z0) := by rw [I_mul_I]; field_simp; ring
  have e3 : I / z0 = I * (1 / z0) := by ring
  have hw2 : (1 / z0).re ^ 2 + (1 / z0).im ^ 2 = 1 / r ^ 2 := by
    rw [sq (1 / z0).re, sq (1 / z0).im, ← Complex.normSq_apply, Complex.normSq_div, Complex.normSq_one,
      Complex.normSq_eq_norm_sq, hn0]
  rw [e1, e2, e3, neg_re, neg_im, I_mul_re, I_mul_im, Real.rpow_sub hr, Real.rpow_two]
  calc _ = r ^ q * (deriv (deriv φ) t + q ^ 2 * φ t) * ((1 / z0).re ^ 2 + (1 / z0).im ^ 2) := by ring
    _ = _ := by rw [hw2]; ring

end GKSharp.O16
