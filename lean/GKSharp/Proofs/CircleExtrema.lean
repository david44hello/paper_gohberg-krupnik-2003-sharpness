/-
CircleExtrema.lean — attained circle extrema for project 019, equation (5.2).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.MobiusDict

namespace GKSharp.Proofs.CircleExtrema

open GKSharp ComplexConjugate Filter Topology

lemma reQPow_arccos {z : ℂ} (hz : z ≠ 0) (q : ℝ) :
    reQPow z q = ‖z‖ ^ q * Real.cos (q * Real.arccos (z.re / ‖z‖)) := by
  unfold reQPow
  by_cases hi : 0 ≤ z.im
  · rw [Complex.arg_of_im_nonneg_of_ne_zero hi hz]
  · rw [Complex.arg_of_im_neg (lt_of_not_ge hi), mul_neg, Real.cos_neg]

lemma continuous_reQPow {q : ℝ} (hq : 0 < q) : Continuous (fun z : ℂ => reQPow z q) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    have hn : Tendsto (fun z : ℂ => ‖z‖ ^ q) (𝓝 0) (𝓝 0) := by
      have cont : Continuous (fun z : ℂ => ‖z‖ ^ q) :=
        continuous_norm.rpow_const (fun _ => Or.inr hq.le)
      simpa only [norm_zero, Real.zero_rpow hq.ne'] using cont.tendsto (0 : ℂ)
    have bound : ∀ z : ℂ, ‖reQPow z q‖ ≤ ‖z‖ ^ q := by
      intro z
      rw [Real.norm_eq_abs, reQPow, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (norm_nonneg _) _) (Real.abs_cos_le_one _)
    simpa [ContinuousAt, reQPow, Real.zero_rpow hq.ne'] using squeeze_zero_norm bound hn
  · have equal : (fun z : ℂ => reQPow z q) =ᶠ[𝓝 z]
        (fun z : ℂ => ‖z‖ ^ q * Real.cos (q * Real.arccos (z.re / ‖z‖))) := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact reQPow_arccos hw q
    apply (continuousAt_congr equal).mpr
    have angle : ContinuousAt (fun w : ℂ => q * Real.arccos (w.re / ‖w‖)) z :=
      continuousAt_const.mul ((Complex.continuous_re.continuousAt.div
        continuous_norm.continuousAt (norm_ne_zero_iff.mpr hz)).arccos)
    exact (continuous_norm.continuousAt.rpow_const (Or.inr hq.le)).mul
      (Real.continuous_cos.continuousAt.comp angle)

lemma reQPow_conj (z : ℂ) (q : ℝ) : reQPow (conj z) q = reQPow z q := by
  simpa using GKSharp.reQPow_real_mul_conj (c := 1) (by norm_num) z q

lemma circle_half {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : ‖w‖ = ρ) :
    ∃ φ ∈ Set.Icc (0 : ℝ) Real.pi,
      (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = w ∨
      (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = conj w := by
  by_cases hi : 0 ≤ w.im
  · refine ⟨Complex.arg w, ⟨Complex.arg_nonneg_iff.mpr hi, Complex.arg_le_pi w⟩, Or.inl ?_⟩
    simpa [hw] using Complex.norm_mul_exp_arg_mul_I w
  · refine ⟨Complex.arg (conj w), ⟨?_, Complex.arg_le_pi _⟩, Or.inr ?_⟩
    · apply Complex.arg_nonneg_iff.mpr
      simp only [Complex.conj_im]
      linarith
    · simpa [hw] using Complex.norm_mul_exp_arg_mul_I (conj w)

theorem eq_5_2_proved {p C K lam ρ : ℝ} (hp : 0 < p) (hK : 0 ≤ K) (hl1 : lam < 1) (hρ : 0 < ρ) :
    ∃ M : ℝ,
      IsGreatest ((fun φ : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))) (p / 2)) ''
        Set.Icc 0 Real.pi) M ∧
      IsLeast ((mobPhi p C K lam) '' Metric.sphere (0 : ℂ) ρ)
        ((1 - lam) ^ p * (C ^ p - ρ ^ p) - K * M) := by
  let polar : ℝ → ℂ := fun φ => (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
  let f : ℝ → ℝ := fun φ => reQPow (mobQ lam (polar φ)) (p / 2)
  have cp : Continuous polar := by fun_prop
  have cq : Continuous (mobQ lam) := by unfold mobQ; fun_prop
  have cf : Continuous f := (continuous_reQPow (by linarith : 0 < p / 2)).comp (cq.comp cp)
  obtain ⟨φ, hφ, maximum⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr Real.pi_pos.le) cf.continuousOn
  have norm_polar (θ : ℝ) : ‖polar θ‖ = ρ := by
    simp [polar, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      Complex.norm_exp_ofReal_mul_I]
  have value (w : ℂ) (hw : ‖w‖ = ρ) :
      mobPhi p C K lam w = (1 - lam) ^ p * (C ^ p - ρ ^ p) - K * reQPow (mobQ lam w) (p / 2) := by
    simp only [mobPhi, hw]
  refine ⟨f φ, ⟨⟨φ, hφ, rfl⟩, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro _ ⟨θ, hθ, rfl⟩
    exact maximum hθ
  · refine ⟨polar φ, ?_, ?_⟩
    · simpa [Metric.mem_sphere, dist_zero_right] using norm_polar φ
    · exact value _ (norm_polar φ)
  · rintro _ ⟨w, hw, rfl⟩
    have hn : ‖w‖ = ρ := by simpa [Metric.mem_sphere, dist_zero_right] using hw
    obtain ⟨θ, hθ, equal⟩ := circle_half hρ hn
    have upper : reQPow (mobQ lam w) (p / 2) ≤ f φ := by
      have maxθ := maximum hθ
      rcases equal with he | he
      · simpa [f, polar, he] using maxθ
      · simpa [f, polar, he, GKSharp.mobQ_conj, reQPow_conj] using maxθ
    rw [value w hn]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left upper hK) _

end GKSharp.Proofs.CircleExtrema

#print axioms GKSharp.Proofs.CircleExtrema.eq_5_2_proved
