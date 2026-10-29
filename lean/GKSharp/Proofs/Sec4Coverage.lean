/- GKSharp/Proofs/Sec4Coverage.lean - slice (b): four small printed steps of sec4a/sec4b (short v0.40).
## localF_endpoint_constant.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v1.30, each as `<row>_proved` with the row's exact type.
- sec4_arch_interval_length (sec4a l.32): `π - π/p < π/q = 2π/p` iff `p < 3`.
- sec4_omegaFirst_unique_critical (sec4a l.51): the numerator of `ω₁'` is `p u^{q-1} sQuad(s)`, `u = s(1 - s)`, so
  `ω₁'(s) = 0` iff `sQuad(s) = 0` iff `s = s*` (row sStar_spec).
- sec4_contact_ray_real_part (sec4b l.30): `(z + λ)(z + 1)/z = (1 + λ) + z + λ/z`, `z = r e^{iθ}`, `cos θ = -cs`.
- sec4_localF_endpoint_constant (sec4b l.101): `π > 3.14`, `π < 3.15` give `(π²/4)(1 - π²/216)² > 2.4649 · 0.954² > 56/25`.
- sec4_gk_kconst_continuous (sec4b v0.70 l.105): `GK_p(λ) = √(gkRootHi)` (shared gk_sq_eq, `GK ≥ 0`) is continuous on
  all of `ℝ`; `K` is a product of continuous factors and `(GK² + λ)^{q-1}` with `GK² + λ > 1 + λ > 0` on `(-1, 1)`.
-/
import GKSharp.Proofs.Sec4aOmega
import GKSharp.Defs.ThresholdAnalysis
import GKSharp.Defs.RealLine

namespace GKSharp

open Set GKSharp.Threshold

/-- sec4a_criterion.tex:32, row `sec4_arch_interval_length`. -/
theorem sec4_arch_interval_length_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    Real.pi - Real.pi / p < Real.pi / q p := by
  have hp0 : 0 < p := by linarith
  have hpi := Real.pi_pos
  have h1 : Real.pi / q p = 2 * (Real.pi / p) := by unfold q; field_simp
  have h2 : Real.pi / 3 < Real.pi / p := by
    rw [div_lt_div_iff₀ (by norm_num) hp0]
    nlinarith
  rw [h1]
  linarith

/-- sec4a_criterion.tex:51, row `sec4_omegaFirst_unique_critical`. -/
theorem sec4_omegaFirst_unique_critical_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ∀ s ∈ Ioo (0 : ℝ) 1, deriv (omegaFirst p) s = 0 ↔ s = sStar p := by
  intro s hs
  have hp0 : 0 < p := by linarith
  have hu : 0 < s * (1 - s) := mul_pos hs.1 (by linarith [hs.2])
  have hs0 : s ≠ 0 := hs.1.ne'
  have hs1 : 1 - s ≠ 0 := (sub_pos.2 hs.2).ne'
  have hN : p * (s * (1 - s)) ^ q p - p * (aConst p + s) * ((1 - 2 * s) * q p * (s * (1 - s)) ^ (q p - 1)) =
      p * (s * (1 - s)) ^ (q p - 1) * sQuad p s := by
    rw [Real.rpow_sub_one hu.ne']
    simp only [sQuad, bConst]
    field_simp
    ring
  have hD : ((s * (1 - s)) ^ q p) ^ 2 ≠ 0 := by positivity
  have hX : 0 < (s * (1 - s)) ^ (q p - 1) := Real.rpow_pos_of_pos hu _
  rw [(sec4a_omegaFirst_hasDerivAt p hs.1 hs.2).deriv, hN, div_eq_zero_iff, or_iff_left hD, mul_eq_zero,
    or_iff_right (mul_pos hp0 hX).ne']
  obtain ⟨-, h2, h3, -, -⟩ := sStar_spec_proved p hp hp2
  exact ⟨h3 s hs, fun h => h ▸ h2⟩

/-- sec4b_failure.tex:30, row `sec4_contact_ray_real_part`. -/
theorem sec4_contact_ray_real_part_proved (p lam r : ℝ) (hr : 0 < r) :
    (((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)) + lam) *
        ((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)) + 1) /
      ((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)))).re =
      1 + lam - cs p * (r + lam / r) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : Complex.exp (Complex.I * (theta p : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have key : ((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)) + lam) *
        ((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)) + 1) /
      ((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ))) =
      ((1 + lam : ℝ) : ℂ) + (r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)) +
        ((lam / r : ℝ) : ℂ) * Complex.exp (-(Complex.I * (theta p : ℂ))) := by
    rw [Complex.exp_neg]
    push_cast
    field_simp
    ring
  have hre1 : (Complex.exp (Complex.I * (theta p : ℂ))).re = Real.cos (theta p) := by
    rw [mul_comm]
    exact Complex.exp_ofReal_mul_I_re _
  have hre2 : (Complex.exp (-(Complex.I * (theta p : ℂ)))).re = Real.cos (theta p) := by
    rw [show -(Complex.I * (theta p : ℂ)) = ((-theta p : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have hcos : Real.cos (theta p) = -cs p := by unfold cs theta; ring
  rw [key, Complex.add_re, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hre1,
    hre2, hcos]
  ring

/-- sec4b_failure.tex:101, row `sec4_localF_endpoint_constant`. -/
theorem sec4_localF_endpoint_constant_proved :
    2 - (Real.pi ^ 2 / 4) * (1 - Real.pi ^ 2 / 216) ^ 2 < -(6 / 25 : ℝ) := by
  have hlo := Real.pi_gt_d2
  have hhi := Real.pi_lt_d2
  have hu1 : (9.8596 : ℝ) < Real.pi ^ 2 := by nlinarith
  have hu2 : Real.pi ^ 2 < (9.9225 : ℝ) := by nlinarith
  have h4 : (2.4649 : ℝ) < Real.pi ^ 2 / 4 := by linarith
  have hw : (0.954 : ℝ) < 1 - Real.pi ^ 2 / 216 := by linarith
  have hw2 : (0.954 : ℝ) ^ 2 < (1 - Real.pi ^ 2 / 216) ^ 2 := by nlinarith
  have hprod := mul_lt_mul'' h4 hw2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢
  linarith

/-- sec4b_failure.tex v0.70:105, row `sec4_gk_kconst_continuous`. -/
theorem sec4_gk_kconst_continuous_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ContinuousOn (fun lam : ℝ => gk p lam) (Ioo (-1 : ℝ) 1) ∧
      ContinuousOn (kConst p) (Ioo (-1 : ℝ) 1) := by
  have hgk : Continuous (fun lam : ℝ => gk p lam) := by
    have h : (fun lam : ℝ => gk p lam) = fun lam : ℝ => Real.sqrt (gkRootHi p lam) := by
      funext lam
      rw [← gk_sq_eq, Real.sqrt_sq (gk_nonneg _ _)]
    rw [h]
    unfold gkRootHi gkMid
    fun_prop
  refine ⟨hgk.continuousOn, ?_⟩
  have hne : ∀ lam ∈ Ioo (-1 : ℝ) 1, gk p lam ^ 2 + lam ≠ 0 := by
    intro lam hlam
    have hC1 : 1 < gk p lam := lt_of_le_of_lt (le_max_left _ _)
      (gk_gt_max hp (ne_of_lt hp2) (ρ := (lam : ℂ)) (by
        intro hh
        have hh' : lam = 1 := by exact_mod_cast hh
        linarith [hlam.2]))
    nlinarith [hlam.1]
  have hk : kConst p = fun lam : ℝ => 2 * (1 - lam) * gk p lam * Real.sin (Real.pi / p) ^ (p - 2) *
      (-Real.cos (Real.pi / p)) ^ (1 - p / 2) * (gk p lam ^ 2 + lam) ^ (p / 2 - 1) := by
    funext lam
    rfl
  have hW : ContinuousOn (fun lam : ℝ => (gk p lam ^ 2 + lam) ^ (p / 2 - 1)) (Ioo (-1 : ℝ) 1) :=
    ((hgk.pow 2).add continuous_id).continuousOn.rpow_const (fun lam hlam => Or.inl (hne lam hlam))
  rw [hk]
  refine ContinuousOn.mul ?_ hW
  exact (by fun_prop : Continuous fun lam : ℝ => 2 * (1 - lam) * gk p lam * Real.sin (Real.pi / p) ^ (p - 2) *
      (-Real.cos (Real.pi / p)) ^ (1 - p / 2)).continuousOn

end GKSharp
