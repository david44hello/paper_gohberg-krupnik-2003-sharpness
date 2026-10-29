/- GKSharp/Proofs/Sec4JointCont.lean - slice (b): joint continuity of the actual obstacle in (λ, t) (short v0.70).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Row of PROPOSAL_CHECKS_THRESHOLDS.lean v1.40 as `<row>_proved` with the row's exact type.
- obstacle_joint_continuous (B:112): near `(λ, t₀)`, take `ε` and the locally uniform coercivity of row
  sec4_coercive_local_uniform (all angles), `Cmax = max GK` on `[λ - ε, λ + ε]` and the radius `Y` for the bound
  `B = Cmax^p 2^p + 1`. Every minimizer `yy` of `Γ_ll(·, t)` (shared obstacle_eq_min) has
  `Γ_ll(yy, t) ≤ Γ_ll(0, t) ≤ GK^p 2^p` (shared gamma_zero_upper), so `|yy| ≤ Y`, and
  `obstacle(ll, t) = inf_{[-Y, Y]} Γ_ll(·, t)` for all `ll` near `λ` and all `t`. The map `((ll, t), y) ↦ Γ_ll(y, t)` is
  jointly continuous, so the infimum over the compact `[-Y, Y]` is continuous in `(ll, t)` (IsCompact.continuous_sInf).
-/
import GKSharp.Proofs.Sec4Continuity
import GKSharp.Proofs.ContactDtGamma

namespace GKSharp

open Set Filter GKSharp.Threshold
open scoped Topology

/-- `((ll, t), y) ↦ Γ_ll(y, t)` is jointly continuous. -/
lemma sec4j_gamma_continuous {p : ℝ} (hp : 1 < p) :
    Continuous (fun x : (ℝ × ℝ) × ℝ => GKSharp.gamma p (gk p x.1.1) (x.1.1 : ℂ) x.2 x.1.2) := by
  have hgk := sec4c_gk_continuous p
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hq0 : (0 : ℝ) ≤ p / 2 := by linarith
  have hl : Continuous fun x : (ℝ × ℝ) × ℝ => x.1.1 := continuous_fst.fst
  have ht : Continuous fun x : (ℝ × ℝ) × ℝ => x.1.2 := continuous_fst.snd
  have hy : Continuous fun x : (ℝ × ℝ) × ℝ => x.2 := continuous_snd
  simp only [sec4t_gamma_real]
  refine Continuous.sub ?_ ?_
  · exact ((hgk.comp hl).rpow_const fun _ => Or.inr hp0).mul
      (((continuous_const.mul (Real.continuous_cosh.comp hy)).add
        (continuous_const.mul (Real.continuous_cos.comp ht))).rpow_const fun _ => Or.inr hq0)
  · exact (((Real.continuous_exp.comp hy).add ((hl.pow 2).mul (Real.continuous_exp.comp hy.neg))).add
      (continuous_const.mul (hl.mul (Real.continuous_cos.comp ht)))).rpow_const fun _ => Or.inr hq0

/-- B:112, row `obstacle_joint_continuous`. -/
theorem obstacle_joint_continuous_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ContinuousOn (fun x : ℝ × ℝ => Threshold.obstacle p x.1 x.2) (Ioo (-1 : ℝ) 1 ×ˢ univ) := by
  have hp0 : 0 < p := by linarith
  intro x hx
  obtain ⟨eps, heps, hsub, hcoer, -⟩ := sec4_coercive_local_uniform_proved p x.1 hp hp2 hx.1
  have hne : (Icc (x.1 - eps) (x.1 + eps)).Nonempty := ⟨x.1, by constructor <;> linarith⟩
  obtain ⟨l1, -, hl1⟩ := isCompact_Icc.exists_isMaxOn hne (sec4c_gk_continuous p).continuousOn
  obtain ⟨Y, -, hY⟩ := hcoer (gk p l1 ^ p * (2 : ℝ) ^ p + 1)
  have hmin : ∀ ll ∈ Icc (x.1 - eps) (x.1 + eps), ∀ t : ℝ,
      Threshold.obstacle p ll t = sInf ((fun y => GKSharp.gamma p (gk p ll) (ll : ℂ) y t) '' Icc (-Y) Y) := by
    intro ll hll t
    obtain ⟨yy, hm, heq⟩ := obstacle_eq_min hp0 (ll : ℂ) (sec4c_gk_gt hp hp2 (hsub hll).2) t
    have hyy : |yy| ≤ Y := by
      by_contra hcon
      have hB : gk p l1 ^ p * (2 : ℝ) ^ p + 1 ≤ GKSharp.gamma p (gk p ll) (ll : ℂ) yy t :=
        hY ll hll yy t (lt_of_not_ge hcon).le
      have h0 := (hm 0).trans (gamma_zero_upper hp0 (gk_nonneg p _) (ll : ℂ) t)
      have hpw := Real.rpow_le_rpow (gk_nonneg p _) (isMaxOn_iff.1 hl1 ll hll) hp0.le
      have h2 := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) p
      nlinarith [mul_le_mul_of_nonneg_right hpw h2]
    have hleast : IsLeast ((fun y => GKSharp.gamma p (gk p ll) (ll : ℂ) y t) '' Icc (-Y) Y)
        (GKSharp.gamma p (gk p ll) (ll : ℂ) yy t) :=
      ⟨⟨yy, abs_le.1 hyy, rfl⟩, by rintro _ ⟨y, -, rfl⟩; exact hm y⟩
    rw [hleast.csInf_eq]
    exact heq
  have hcont : Continuous fun z : ℝ × ℝ =>
      sInf ((fun y => GKSharp.gamma p (gk p z.1) (z.1 : ℂ) y z.2) '' Icc (-Y) Y) :=
    isCompact_Icc.continuous_sInf (f := fun (z : ℝ × ℝ) (y : ℝ) => GKSharp.gamma p (gk p z.1) (z.1 : ℂ) y z.2)
      (by simpa only [Function.HasUncurry.uncurry, id] using sec4j_gamma_continuous hp)
  have heq : (fun z : ℝ × ℝ => sInf ((fun y => GKSharp.gamma p (gk p z.1) (z.1 : ℂ) y z.2) '' Icc (-Y) Y)) =ᶠ[𝓝 x]
      fun z => Threshold.obstacle p z.1 z.2 := by
    filter_upwards [prod_mem_nhds (Icc_mem_nhds (show x.1 - eps < x.1 by linarith) (show x.1 < x.1 + eps by linarith))
      (univ_mem : univ ∈ 𝓝 x.2)] with z hz
    exact (hmin z.1 hz.1 z.2).symm
  exact (hcont.continuousAt.congr heq).continuousWithinAt

end GKSharp
