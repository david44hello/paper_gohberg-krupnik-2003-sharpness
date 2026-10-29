/- GKSharp/Proofs/Sec4Continuity.lean - slice (b): the v0.70 continuity paragraph of sec4b (short v0.70).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v1.30, each as `<row>_proved` with the row's exact type.
- sec4_coercive_local_uniform (v0.70 l.106): on `[λ - ε, λ + ε]`, `ε = (1 - |λ|)/2`, one has `|ll| ≤ a = (1 + |λ|)/2 < 1`
  and `Cmin ≤ GK_p(ll) ≤ Cmax` with `Cmin = min GK > 1` (continuity of `GK`, compactness). The shared radial lower
  bounds `Γ(±y, t) ≥ e^{qy} L±(C, |ρ|, e^{-y})`, `L+ = C^p(1-s)^p - (1 + as)^p`, `L- = C^p(1-s)^p - (a + s)^p`, grow in
  `C` and shrink in `a`, so `L±(Cmin, a)` bounds every `ll` at once and tends to `+∞`. Each minimizer `yy` of
  `Γ_ll(·, 0)` (shared obstacle_eq_min) has `Γ_ll(yy, 0) ≤ Γ_ll(0, 0) ≤ Cmax^p 2^p`, so `|yy| ≤ Y` for the `Y` of the
  bound `B = Cmax^p 2^p + 1`.
- sec4_mGK0_h_continuous (v0.70 l.107): near `λ`, `obstacle(ll, 0) = inf_{[-Y, Y]} Γ_ll(·, 0)`; `(ll, y) ↦ Γ_ll(y, 0)`
  is jointly continuous, so the infimum over the compact is continuous (IsCompact.continuous_sInf); `h = that - K`
  with `K` continuous (row sec4_gk_kconst_continuous).
- sec4_h_continuousOn (sec4b l.112): the second half of the previous row.
-/
import GKSharp.Proofs.Sec4Coverage
import GKSharp.Proofs.Sec4bAxis
import GKSharp.Proofs.ObstacleMinimum

namespace GKSharp

open Set Filter GKSharp.Threshold
open scoped Topology

lemma sec4c_gammaGK_eq (p ll y t : ℝ) : gammaGK p ll y t = GKSharp.gamma p (gk p ll) (ll : ℂ) y t := rfl

/-- `λ ↦ GK_p(λ)` is continuous on `ℝ`: `GK = √gkRootHi` (same route as sec4_gk_kconst_continuous). -/
lemma sec4c_gk_continuous (p : ℝ) : Continuous (fun lam : ℝ => gk p lam) := by
  have h : (fun lam : ℝ => gk p lam) = fun lam : ℝ => Real.sqrt (gkRootHi p lam) := by
    funext lam
    rw [← gk_sq_eq, Real.sqrt_sq (gk_nonneg _ _)]
  rw [h]
  unfold gkRootHi gkMid
  fun_prop

lemma sec4c_gk_gt {p ll : ℝ} (hp : 1 < p) (hp2 : p < 2) (hll : ll < 1) : max 1 ‖(ll : ℂ)‖ < gk p ll :=
  gk_gt_max hp (ne_of_lt hp2) (ρ := (ll : ℂ)) (by
    intro hh
    have hh' : ll = 1 := by exact_mod_cast hh
    linarith)

/-- `(ll, y) ↦ Γ_ll(y, 0)` is jointly continuous on `ℝ × ℝ`. -/
lemma sec4c_gamma_axis_continuous {p : ℝ} (hp : 1 < p) :
    Continuous (fun x : ℝ × ℝ => GKSharp.gamma p (gk p x.1) (x.1 : ℂ) x.2 0) := by
  have hgk := sec4c_gk_continuous p
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hq0 : (0 : ℝ) ≤ p / 2 := by linarith
  simp only [sec4b_gamma_axis]
  refine Continuous.sub ?_ ?_
  · exact ((hgk.comp continuous_fst).rpow_const fun _ => Or.inr hp0).mul
      (((continuous_const.mul (Real.continuous_cosh.comp continuous_snd)).add continuous_const).rpow_const
        fun _ => Or.inr hq0)
  · exact (((Real.continuous_exp.comp continuous_snd).add
      ((continuous_fst.pow 2).mul (Real.continuous_exp.comp continuous_snd.neg))).add
      (continuous_const.mul continuous_fst)).rpow_const fun _ => Or.inr hq0

lemma sec4c_lowerPositive_mono {p C C' a a' s : ℝ} (hp : 0 < p) (hC : 0 ≤ C) (hCC : C ≤ C') (ha : 0 ≤ a)
    (haa : a ≤ a') (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Coercive.lowerPositive p C a' s ≤ Coercive.lowerPositive p C' a s := by
  unfold Coercive.lowerPositive
  have h1 := Real.rpow_le_rpow hC hCC hp.le
  have h2 := Real.rpow_le_rpow (add_nonneg zero_le_one (mul_nonneg ha hs0))
    (show 1 + a * s ≤ 1 + a' * s by nlinarith) hp.le
  have h3 := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 - s by linarith) p
  linarith [mul_le_mul_of_nonneg_right h1 h3]

lemma sec4c_lowerNegative_mono {p C C' a a' s : ℝ} (hp : 0 < p) (hC : 0 ≤ C) (hCC : C ≤ C') (ha : 0 ≤ a)
    (haa : a ≤ a') (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Coercive.lowerNegative p C a' s ≤ Coercive.lowerNegative p C' a s := by
  unfold Coercive.lowerNegative
  have h1 := Real.rpow_le_rpow hC hCC hp.le
  have h2 := Real.rpow_le_rpow (add_nonneg ha hs0) (show a + s ≤ a' + s by linarith) hp.le
  have h3 := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 - s by linarith) p
  linarith [mul_le_mul_of_nonneg_right h1 h3]

/-- Coercivity of `Γ`, uniform in `C ≥ Cmin > 1`, `‖ρ‖ ≤ a < 1` and the angle. -/
lemma sec4c_uniform_coercive {p Cmin amax : ℝ} (hp : 0 < p) (hC : 1 < Cmin) (ha0 : 0 ≤ amax) (ha1 : amax < 1)
    (B : ℝ) : ∃ Y > 0, ∀ (C : ℝ) (ρ : ℂ), Cmin ≤ C → ‖ρ‖ ≤ amax →
      ∀ y t : ℝ, Y ≤ |y| → B ≤ GKSharp.gamma p C ρ y t := by
  have hn : ‖(amax : ℂ)‖ = amax := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
  obtain ⟨Rp, hRp⟩ := tendsto_atTop_atTop.mp (Coercive.positive_lower_tendsto hp hC (amax : ℂ)) B
  obtain ⟨Rm, hRm⟩ := tendsto_atTop_atTop.mp
    (Coercive.negative_lower_tendsto (C := Cmin) hp (amax : ℂ) (by rw [hn]; linarith)) B
  simp only [hn] at hRp hRm
  have hC0 : 0 ≤ Cmin := by linarith
  refine ⟨max 1 (max Rp Rm), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro C ρ hCC hρ y t hy
  have hYp : Rp ≤ max 1 (max Rp Rm) := (le_max_left _ _).trans (le_max_right _ _)
  have hYm : Rm ≤ max 1 (max Rp Rm) := (le_max_right _ _).trans (le_max_right _ _)
  by_cases hy0 : 0 ≤ y
  · rw [abs_of_nonneg hy0] at hy
    have h1 := hRp y (hYp.trans hy)
    have h2 := mul_le_mul_of_nonneg_left (sec4c_lowerPositive_mono hp hC0 hCC (norm_nonneg ρ) hρ
      (Real.exp_pos (-y)).le (Real.exp_le_one_iff.2 (by linarith))) (Real.exp_pos (p / 2 * y)).le
    have h3 := Coercive.gamma_lower_positive hp C (hC0.trans hCC) ρ y t hy0
    linarith
  · have hyn : y < 0 := lt_of_not_ge hy0
    rw [abs_of_neg hyn] at hy
    have h1 := hRm (-y) (hYm.trans hy)
    have h2 := mul_le_mul_of_nonneg_left (sec4c_lowerNegative_mono hp hC0 hCC (norm_nonneg ρ) hρ
      (Real.exp_pos (-(-y))).le (Real.exp_le_one_iff.2 (by linarith))) (Real.exp_pos (p / 2 * -y)).le
    have h3 := Coercive.gamma_lower_negative hp C (hC0.trans hCC) ρ (-y) t (by linarith)
    simp only [neg_neg] at h1 h2 h3
    linarith

/-- sec4b_failure.tex v0.70:106, row `sec4_coercive_local_uniform`. -/
theorem sec4_coercive_local_uniform_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    ∃ eps > 0, Icc (lam - eps) (lam + eps) ⊆ Ioo (-1 : ℝ) 1 ∧
      (∀ B : ℝ, ∃ Y > 0, ∀ ll ∈ Icc (lam - eps) (lam + eps),
        ∀ y t : ℝ, Y ≤ |y| → B ≤ gammaGK p ll y t) ∧
      (∃ Y > 0, ∀ ll ∈ Icc (lam - eps) (lam + eps),
        ∃ yy ∈ Icc (-Y) Y, Threshold.obstacle p ll 0 = gammaGK p ll yy 0 ∧
          ∀ y : ℝ, gammaGK p ll yy 0 ≤ gammaGK p ll y 0) := by
  have hp0 : 0 < p := by linarith
  have hl : |lam| < 1 := abs_lt.2 ⟨hlam.1, hlam.2⟩
  have hl0 := abs_nonneg lam
  set eps := (1 - |lam|) / 2 with heps
  set amax := (1 + |lam|) / 2 with hamax
  have heps0 : 0 < eps := by rw [heps]; linarith
  have hbox : ∀ ll ∈ Icc (lam - eps) (lam + eps), |ll| ≤ amax := by
    intro ll hll
    rw [abs_le]
    constructor <;> linarith [neg_abs_le lam, le_abs_self lam, hll.1, hll.2]
  have hamax1 : amax < 1 := by rw [hamax]; linarith
  have hamax0 : 0 ≤ amax := by rw [hamax]; linarith
  have hsub : Icc (lam - eps) (lam + eps) ⊆ Ioo (-1 : ℝ) 1 := fun ll hll =>
    abs_lt.1 ((hbox ll hll).trans_lt hamax1)
  have hne : (Icc (lam - eps) (lam + eps)).Nonempty := ⟨lam, by constructor <;> linarith⟩
  have hcK := (sec4c_gk_continuous p).continuousOn (s := Icc (lam - eps) (lam + eps))
  obtain ⟨l0, hl0K, hl0⟩ := isCompact_Icc.exists_isMinOn hne hcK
  obtain ⟨l1, -, hl1⟩ := isCompact_Icc.exists_isMaxOn hne hcK
  have hCmin : 1 < gk p l0 := lt_of_le_of_lt (le_max_left _ _) (sec4c_gk_gt hp hp2 (hsub hl0K).2)
  have hlow : ∀ ll ∈ Icc (lam - eps) (lam + eps), gk p l0 ≤ gk p ll := fun ll hll => isMinOn_iff.1 hl0 ll hll
  have hup : ∀ ll ∈ Icc (lam - eps) (lam + eps), gk p ll ≤ gk p l1 := fun ll hll => isMaxOn_iff.1 hl1 ll hll
  have hnorm : ∀ ll ∈ Icc (lam - eps) (lam + eps), ‖(ll : ℂ)‖ ≤ amax := fun ll hll => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hbox ll hll
  refine ⟨eps, heps0, hsub, fun B => ?_, ?_⟩
  · obtain ⟨Y, hY0, hY⟩ := sec4c_uniform_coercive hp0 hCmin hamax0 hamax1 B
    exact ⟨Y, hY0, fun ll hll y t hy => hY (gk p ll) ll (hlow ll hll) (hnorm ll hll) y t hy⟩
  · obtain ⟨Y, hY0, hY⟩ := sec4c_uniform_coercive hp0 hCmin hamax0 hamax1 (gk p l1 ^ p * (2 : ℝ) ^ p + 1)
    refine ⟨Y, hY0, fun ll hll => ?_⟩
    obtain ⟨yy, hmin, heq⟩ := obstacle_eq_min hp0 (ll : ℂ) (sec4c_gk_gt hp hp2 (hsub hll).2) 0
    have hyy : |yy| ≤ Y := by
      by_contra hcon
      have hB := hY (gk p ll) ll (hlow ll hll) (hnorm ll hll) yy 0 (lt_of_not_ge hcon).le
      have h0 := (hmin 0).trans (gamma_zero_upper hp0 (gk_nonneg p _) (ll : ℂ) 0)
      have hpw := Real.rpow_le_rpow (gk_nonneg p _) (hup ll hll) hp0.le
      have h2 := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) p
      nlinarith [mul_le_mul_of_nonneg_right hpw h2]
    exact ⟨yy, abs_le.1 hyy, heq, hmin⟩

/-- sec4b_failure.tex v0.70:107, row `sec4_mGK0_h_continuous`. -/
theorem sec4_mGK0_h_continuous_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ContinuousOn (fun lam : ℝ => Threshold.obstacle p lam 0) (Ioo (-1 : ℝ) 1) ∧
      ContinuousOn (Threshold.h p) (Ioo (-1 : ℝ) 1) := by
  have hm : ContinuousOn (fun lam : ℝ => Threshold.obstacle p lam 0) (Ioo (-1 : ℝ) 1) := by
    intro lam hlam
    obtain ⟨eps, heps, -, -, Y, -, hY⟩ := sec4_coercive_local_uniform_proved p lam hp hp2 hlam
    have hcont : Continuous fun ll : ℝ =>
        sInf ((fun y => GKSharp.gamma p (gk p ll) (ll : ℂ) y 0) '' Icc (-Y) Y) :=
      isCompact_Icc.continuous_sInf (f := fun (ll y : ℝ) => GKSharp.gamma p (gk p ll) (ll : ℂ) y 0)
        (by simpa only [Function.HasUncurry.uncurry, id] using sec4c_gamma_axis_continuous hp)
    have heq : (fun ll : ℝ => sInf ((fun y => GKSharp.gamma p (gk p ll) (ll : ℂ) y 0) '' Icc (-Y) Y)) =ᶠ[𝓝 lam]
        fun ll => Threshold.obstacle p ll 0 := by
      filter_upwards [Icc_mem_nhds (show lam - eps < lam by linarith) (show lam < lam + eps by linarith)]
        with ll hll
      obtain ⟨yy, hyy, hob, hmin⟩ := hY ll hll
      have hleast : IsLeast ((fun y => GKSharp.gamma p (gk p ll) (ll : ℂ) y 0) '' Icc (-Y) Y)
          (gammaGK p ll yy 0) := ⟨⟨yy, hyy, rfl⟩, by rintro _ ⟨y, -, rfl⟩; exact hmin y⟩
      rw [hleast.csInf_eq, hob]
    exact (hcont.continuousAt.congr heq).continuousWithinAt
  exact ⟨hm, hm.sub (sec4_gk_kconst_continuous_proved p hp hp2).2⟩

/-- sec4b_failure.tex:112, row `sec4_h_continuousOn`. -/
theorem sec4_h_continuousOn_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ContinuousOn (Threshold.h p) (Ioo (-1 : ℝ) 1) :=
  (sec4_mGK0_h_continuous_proved p hp hp2).2

end GKSharp

