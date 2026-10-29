/- uniform leading Gamma asymptotics for arbitrary complex ratios.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GammaCoercive

open Real Filter Topology Set
namespace GKSharp.Asymptotics

private theorem coefficient_continuous (p C : ℝ) (hp : 0 < p) :
    Continuous (fun x : ℝ × ℝ => C ^ p * x.1 ^ p - x.2 ^ p) := by
  exact (continuous_const.mul (continuous_fst.rpow_const (fun _ => Or.inr hp.le))).sub
    (continuous_snd.rpow_const (fun _ => Or.inr hp.le))

private theorem unit_add_norm_bound (t s : ℝ) (hs : 0 ≤ s) (a : ℂ) :
    |‖unitPoint t + (s : ℂ) * a‖ - 1| ≤ s * ‖a‖ := by
  have h := abs_norm_sub_norm_le (unitPoint t + (s : ℂ) * a) (unitPoint t)
  simpa [norm_unitPoint, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] using h

private theorem scaled_unit_add_norm_bound (t s : ℝ) (hs : 0 ≤ s) (a : ℂ) :
    |‖(s : ℂ) * unitPoint t + a‖ - ‖a‖| ≤ s := by
  have h := abs_norm_sub_norm_le ((s : ℂ) * unitPoint t + a) a
  simpa [norm_unitPoint, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] using h

theorem gamma_positive_tail {p : ℝ} (hp : 0 < p) (C : ℝ) (rho : ℂ) :
    ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y t : ℝ, Y < y →
      |gamma p C rho y t / Real.exp (p / 2 * y) - (C ^ p - 1)| < ε := by
  intro ε hε
  obtain ⟨δ,hδ,hcontrol⟩ := Metric.continuousAt_iff.mp
    (coefficient_continuous p C hp).continuousAt ε hε
  have hden : 0 < ‖rho‖ + 1 := by positivity
  have hsmall : ∀ᶠ y : ℝ in atTop, Real.exp (-y) < δ / (‖rho‖ + 1) :=
    tendsto_exp_neg_atTop_nhds_zero.eventually (eventually_lt_nhds (div_pos hδ hden))
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hsmall
  refine ⟨Y, fun y t hy => ?_⟩
  let s := Real.exp (-y)
  have hs : 0 < s := Real.exp_pos _
  have hsum : s * (‖rho‖ + 1) < δ := (lt_div_iff₀ hden).mp (hY y hy.le)
  have hsa : s < δ := by nlinarith [mul_nonneg hs.le (norm_nonneg rho)]
  have hsb : s * ‖rho‖ < δ := by nlinarith
  have ha := unit_add_norm_bound t s hs.le 1
  have hb := unit_add_norm_bound t s hs.le rho
  have hdist : dist (‖unitPoint t + (s : ℂ)‖, ‖unitPoint t + (s : ℂ) * rho‖)
      ((1 : ℝ),1) < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    apply max_lt
    · have hh : |‖unitPoint t + (s : ℂ)‖ - 1| ≤ s := by simpa using ha
      exact hh.trans_lt hsa
    · exact hb.trans_lt hsb
  have hvalue := hcontrol hdist
  have hquot : gamma p C rho y t / Real.exp (p / 2 * y) =
      C ^ p * ‖unitPoint t + (s : ℂ)‖ ^ p - ‖unitPoint t + (s : ℂ) * rho‖ ^ p := by
    apply (div_eq_iff (Real.exp_ne_zero _)).mpr
    rw [Coercive.gamma_normalized_positive]
    dsimp [s]
    ring
  rw [hquot]
  convert hvalue using 1 <;> simp [Real.dist_eq] <;> congr 1 <;> ring

private theorem gamma_negative_radial_tail {p : ℝ} (hp : 0 < p) (C : ℝ) (rho : ℂ) :
    ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y t : ℝ, Y < y →
      |gamma p C rho (-y) t / Real.exp (p / 2 * y) - (C ^ p - ‖rho‖ ^ p)| < ε := by
  intro ε hε
  obtain ⟨δ,hδ,hcontrol⟩ := Metric.continuousAt_iff.mp
    (coefficient_continuous p C hp).continuousAt ε hε
  have hsmall : ∀ᶠ y : ℝ in atTop, Real.exp (-y) < δ :=
    tendsto_exp_neg_atTop_nhds_zero.eventually (eventually_lt_nhds hδ)
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hsmall
  refine ⟨Y, fun y t hy => ?_⟩
  let s := Real.exp (-y)
  have hs : 0 < s := Real.exp_pos _
  have hsd : s < δ := hY y hy.le
  have ha := scaled_unit_add_norm_bound t s hs.le 1
  have hb := scaled_unit_add_norm_bound t s hs.le rho
  have hdist : dist (‖(s : ℂ) * unitPoint t + 1‖, ‖(s : ℂ) * unitPoint t + rho‖)
      ((1 : ℝ), ‖rho‖) < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt (by simpa using ha.trans_lt hsd) (hb.trans_lt hsd)
  have hvalue := hcontrol hdist
  have hquot : gamma p C rho (-y) t / Real.exp (p / 2 * y) =
      C ^ p * ‖(s : ℂ) * unitPoint t + 1‖ ^ p - ‖(s : ℂ) * unitPoint t + rho‖ ^ p := by
    apply (div_eq_iff (Real.exp_ne_zero _)).mpr
    rw [Coercive.gamma_normalized_negative]
    dsimp [s]
    ring
  rw [hquot]
  convert hvalue using 1 <;> simp [Real.dist_eq] <;> congr 1 <;> ring

theorem gamma_negative_tail {p : ℝ} (hp : 0 < p) (C : ℝ) (rho : ℂ) :
    ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y t : ℝ, y < Y →
      |gamma p C rho y t / Real.exp (-(p / 2) * y) - (C ^ p - ‖rho‖ ^ p)| < ε := by
  intro ε hε
  obtain ⟨Y,hY⟩ := gamma_negative_radial_tail hp C rho ε hε
  refine ⟨-Y, fun y t hy => ?_⟩
  have h := hY (-y) t (by linarith)
  simpa only [neg_neg, mul_neg, neg_mul] using h

theorem slice_O11_proved {p : ℝ} (hp : 1 < p) (C : ℝ) (rho : ℂ) (hC : max 1 ‖rho‖ < C) :
    (∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y t : ℝ, Y < y →
      |gamma p C rho y t / Real.exp (p / 2 * y) - (C ^ p - 1)| < ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y t : ℝ, y < Y →
      |gamma p C rho y t / Real.exp (-(p / 2) * y) - (C ^ p - ‖rho‖ ^ p)| < ε) ∧
    UniformCoercive p C rho := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  exact ⟨gamma_positive_tail hp0 C rho, gamma_negative_tail hp0 C rho,
    Coercive.gamma_uniform_coercive hp0 rho hC⟩

end GKSharp.Asymptotics

#print axioms GKSharp.Asymptotics.gamma_positive_tail
#print axioms GKSharp.Asymptotics.gamma_negative_tail
#print axioms GKSharp.Asymptotics.slice_O11_proved
