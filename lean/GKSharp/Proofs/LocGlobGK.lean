/- continuous + locally sub-mean ⇒ sub-mean on every circle (port of the 018 tools
circleAverage_normSq, LocGlobCore.center_le / submean_of_local into the 019 tree; no cited input).
Copyright (C) Dave Goel 2026--now.

  Fix a circle |z - c| = R and ε > 0. `exists_trig_approx` gives a trigonometric polynomial T with |T - u| < ε/2 on the
  circle. Its harmonic extension is P(z) = Re Y((z-c)/R), Y = toZ + toW a polynomial (`re_eval_toZ_add_toW`). f = u - P is
  continuous and locally sub-mean; `center_le` (f + δ|z|² has no interior maximum, since avg |z|² = |a|² + r²) gives
  f(c) ≤ max_circle f ≤ ε/2. Hence u(c) ≤ P(c) + ε/2 = mean P + ε/2 ≤ mean u + ε. -/
import GKSharp.Proofs.PolynomialPairs
import GKSharp.Proofs.Select

open Real Metric Set Filter Topology MeasureTheory

namespace GKSharp

namespace LocGlob

/-- `Re` of `toZ + toW` on the circle is `Re` of the trigonometric polynomial. -/
theorem re_eval_toZ_add_toW (c : ℤ →₀ ℂ) (θ : ℝ) :
    ((toZ c + toW c).eval (unitPt θ)).re = (trig c θ).re := by
  rw [Polynomial.eval_add, eval_toZ, eval_toW, trig_eq_add, Complex.add_re, Complex.add_re, Complex.conj_re]

/-- The circle average of `‖z‖²`: `‖c‖² + ρ²`. -/
theorem circleAverage_normSq (c : ℂ) (ρ : ℝ) : circleAverage (fun z => ‖z‖ ^ 2) c ρ = ‖c‖ ^ 2 + ρ ^ 2 := by
  have h : ∀ θ : ℝ, ‖circleMap c ρ θ‖ ^ 2 = (‖c‖ ^ 2 + ρ ^ 2) + (2 * ρ * c.re) * cos θ + (2 * ρ * c.im) * sin θ := by
    intro θ
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp only [circleMap, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero]
    nlinarith [sin_sq_add_cos_sq θ]
  rw [circleAverage_def]
  simp_rw [h]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos, integral_sin]
  simp only [sin_two_pi, sin_zero, cos_two_pi, cos_zero, sub_zero, sub_self, mul_zero, add_zero, smul_eq_mul]
  field_simp

/-- A point of the circle `|z - c| = R` is `circleMap c R θ` for some `θ ∈ [0, 2π]`. -/
theorem exists_theta {c0 z : ℂ} {R : ℝ} (hz : dist z c0 = R) :
    ∃ θ ∈ Icc (0 : ℝ) (2 * π), circleMap c0 R θ = z := by
  have hn : ‖z - c0‖ = R := by rw [← dist_eq_norm]; exact hz
  have hφ : circleMap c0 R (Complex.arg (z - c0)) = z := by
    simp only [circleMap]
    rw [← hn, Complex.norm_mul_exp_arg_mul_I]; ring
  rcases le_or_gt 0 (Complex.arg (z - c0)) with h | h
  · exact ⟨_, ⟨h, by linarith [Complex.arg_le_pi (z - c0), pi_pos]⟩, hφ⟩
  · refine ⟨Complex.arg (z - c0) + 2 * π, ⟨by linarith [Complex.neg_pi_lt_arg (z - c0)], by linarith⟩, ?_⟩
    rw [periodic_circleMap c0 R _, hφ]

/-- **Maximum principle at the centre** for a continuous, locally sub-mean `f` on the closed disc. -/
theorem center_le {f : ℂ → ℝ} (hf : Continuous f) {c0 : ℂ} {R : ℝ} (hR : 0 < R)
    (hloc : ∀ a ∈ ball c0 R, ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ → f a ≤ circleAverage f a r)
    {M : ℝ} (hM : ∀ θ ∈ Icc (0 : ℝ) (2 * π), f (circleMap c0 R θ) ≤ M) : f c0 ≤ M := by
  set B := (‖c0‖ + R) ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hKB : ∀ z ∈ closedBall c0 R, ‖z‖ ^ 2 ≤ B := by
    intro z hz
    have h1 : ‖z‖ ≤ ‖c0‖ + R := by
      have := norm_le_norm_add_norm_sub' z c0
      rw [mem_closedBall, dist_eq_norm] at hz
      linarith
    exact pow_le_pow_left₀ (norm_nonneg z) h1 2
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set d := δ / (B + 1) with hd
  have hd0 : 0 < d := by positivity
  have hdB : d * B ≤ δ := by
    rw [hd, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  set g : ℂ → ℝ := fun z => f z + d * ‖z‖ ^ 2 with hg
  have hgc : Continuous g := hf.add (continuous_const.mul (continuous_norm.pow 2))
  obtain ⟨z1, hz1K, hmax⟩ :=
    (isCompact_closedBall c0 R).exists_isMaxOn ⟨c0, mem_closedBall_self hR.le⟩ hgc.continuousOn
  have hz1R : dist z1 c0 = R := by
    by_contra hne
    have hlt : dist z1 c0 < R := lt_of_le_of_ne (mem_closedBall.mp hz1K) hne
    obtain ⟨ρ, hρ, hsub⟩ := hloc z1 (mem_ball.mpr hlt)
    set r := min (ρ / 2) ((R - dist z1 c0) / 2) with hr
    have hr0 : 0 < r := lt_min (by positivity) (by linarith)
    have hrρ : r < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hrR : r + dist z1 c0 < R := by
      have := min_le_right (ρ / 2) ((R - dist z1 c0) / 2); linarith
    have h1 := hsub r hr0 hrρ
    have hfint : CircleIntegrable f z1 r := hf.continuousOn.circleIntegrable'
    have hqint : CircleIntegrable (fun z => d * ‖z‖ ^ 2) z1 r :=
      (continuous_const.mul (continuous_norm.pow 2)).continuousOn.circleIntegrable'
    have hgavg : circleAverage g z1 r = circleAverage f z1 r + d * (‖z1‖ ^ 2 + r ^ 2) := by
      rw [hg, circleAverage_fun_add hfint hqint, ← circleAverage_normSq z1 r]
      congr 1
      simp only [← smul_eq_mul]; exact circleAverage_fun_smul
    have hle : circleAverage g z1 r ≤ g z1 := by
      refine circleAverage_mono_on_of_le_circle hgc.continuousOn.circleIntegrable' fun z hz => hmax ?_
      rw [mem_sphere, abs_of_pos hr0] at hz
      rw [mem_closedBall]
      linarith [dist_triangle z z1 c0]
    rw [hgavg] at hle
    simp only [hg] at hle
    have : 0 < d * r ^ 2 := by positivity
    nlinarith
  obtain ⟨θ, hθ, hθz⟩ := exists_theta hz1R
  have h1 : g c0 ≤ g z1 := hmax (mem_closedBall_self hR.le)
  have h2 : f z1 ≤ M := by rw [← hθz]; exact hM θ hθ
  have h3 : d * ‖z1‖ ^ 2 ≤ d * B := mul_le_mul_of_nonneg_left (hKB z1 hz1K) hd0.le
  have h4 : 0 ≤ d * ‖c0‖ ^ 2 := by positivity
  simp only [hg] at h1
  linarith

/-- **Local ⇒ global sub-mean** for continuous `u` (every circle, every radius). -/
theorem submean_of_local {u : ℂ → ℝ} (hu : Continuous u)
    (hloc : ∀ a, ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ → u a ≤ circleAverage u a r) {c0 : ℂ} {R : ℝ} (hR : 0 < R) :
    u c0 ≤ circleAverage u c0 R := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set g : ℝ → ℝ := fun θ => u (circleMap c0 R θ) with hg
  have hgc : Continuous g := hu.comp (continuous_circleMap c0 R)
  have hper : g 0 = g (2 * π) := by
    simp only [hg]; rw [← periodic_circleMap c0 R 0, zero_add]
  obtain ⟨c, hc⟩ := exists_trig_approx g hgc hper (ε / 2) (by positivity)
  set Y := toZ c + toW c with hY
  set P : ℂ → ℝ := fun z => (Y.eval ((z - c0) / R)).re with hP
  have hYa : ∀ z, AnalyticAt ℂ (fun z => Y.eval ((z - c0) / R)) z := fun z =>
    (Y.differentiable.comp ((differentiable_id.sub_const c0).div_const _)).analyticAt z
  have hPh : ∀ s : Set ℂ, InnerProductSpace.HarmonicOnNhd P s := fun s z _ => (hYa z).harmonicAt_re
  have hPc : Continuous P :=
    Complex.continuous_re.comp (Y.continuous.comp ((continuous_id.sub continuous_const).div_const _))
  have hPmean : ∀ a r, circleAverage P a r = P a := fun a r => (hPh _).circleAverage_eq
  have hPcirc : ∀ θ, P (circleMap c0 R θ) = (trig c θ).re := by
    intro θ
    simp only [hP]
    rw [circleMap_sub_center, circleMap_zero, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hR.ne')]
    exact re_eval_toZ_add_toW c θ
  set f : ℂ → ℝ := fun z => u z - P z with hf
  have hfc : Continuous f := hu.sub hPc
  have hfloc : ∀ a ∈ ball c0 R, ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ → f a ≤ circleAverage f a r := by
    intro a _
    obtain ⟨ρ, hρ, h⟩ := hloc a
    refine ⟨ρ, hρ, fun r hr hrρ => ?_⟩
    have h1 := h r hr hrρ
    rw [hf, circleAverage_fun_sub hu.continuousOn.circleIntegrable' hPc.continuousOn.circleIntegrable', hPmean]
    linarith
  have hfM : ∀ θ ∈ Icc (0 : ℝ) (2 * π), f (circleMap c0 R θ) ≤ ε / 2 := by
    intro θ hθ
    have h1 := abs_lt.mp (hc θ hθ)
    simp only [hf, hPcirc]
    simp only [hg] at h1
    linarith [h1.1]
  have h1 := center_le hfc hR hfloc hfM
  have h2 : circleAverage P c0 R ≤ circleAverage u c0 R + ε / 2 := by
    rw [circleAverage_def, circleAverage_def, smul_eq_mul, smul_eq_mul]
    have hPi : IntervalIntegrable (fun θ => P (circleMap c0 R θ)) volume 0 (2 * π) :=
      (hPc.comp (continuous_circleMap c0 R)).intervalIntegrable _ _
    have hui : IntervalIntegrable (fun θ => u (circleMap c0 R θ)) volume 0 (2 * π) :=
      (hu.comp (continuous_circleMap c0 R)).intervalIntegrable _ _
    have hmono : ∫ θ in (0 : ℝ)..(2 * π), P (circleMap c0 R θ)
        ≤ ∫ θ in (0 : ℝ)..(2 * π), (u (circleMap c0 R θ) + ε / 2) :=
      intervalIntegral.integral_mono_on two_pi_pos.le hPi (hui.add intervalIntegrable_const) fun θ hθ => by
        have h3 := abs_lt.mp (hc θ hθ)
        rw [hPcirc]
        simp only [hg] at h3
        linarith [h3.2]
    rw [intervalIntegral.integral_add hui intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul,
      sub_zero] at hmono
    have h2pi : 0 < 2 * π := two_pi_pos
    calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), P (circleMap c0 R θ)
        ≤ (2 * π)⁻¹ * ((∫ θ in (0 : ℝ)..(2 * π), u (circleMap c0 R θ)) + 2 * π * (ε / 2)) :=
          mul_le_mul_of_nonneg_left hmono (inv_pos.mpr h2pi).le
      _ = (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π), u (circleMap c0 R θ)) + ε / 2 := by
          field_simp
  rw [hPmean] at h2
  simp only [hf] at h1
  linarith

end LocGlob

end GKSharp
