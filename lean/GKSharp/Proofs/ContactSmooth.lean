/- GKSharp/Proofs/ContactSmooth.lean — local smoothness and critical branch.
Frozen source: short_v0.70/sec4b_failure.tex:29–32.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactScaling
import Mathlib.Analysis.Calculus.ImplicitContDiff

namespace GKSharp
open Threshold ContactCalc Set Filter
open scoped Topology ContDiff

namespace ContactSmooth

lemma Q_contDiff (c : ℝ) : ContDiff ℝ ω (fun u : ℝ × ℝ => Q c u.2 u.1) := by
  unfold Q
  fun_prop

lemma gamma_contDiffAt (p lam y t : ℝ) (hp : 1 < p) (hS : PositiveBases lam y t) :
    ContDiffAt ℝ ω (fun u : ℝ × ℝ => gammaGK p lam u.2 u.1) (t, y) := by
  have heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (t, y),
      gammaGK p lam u.2 u.1 = Real.exp (-q p * u.2) *
        (gk p lam ^ p * Real.exp (p * (1 / 2 * Real.log (Q 1 u.2 u.1))) -
          Real.exp (p * (1 / 2 * Real.log (Q lam u.2 u.1)))) := by
    have h1 := ((Q_contDiff 1).continuous.tendsto (t, y)).eventually (lt_mem_nhds hS.1)
    have hl := ((Q_contDiff lam).continuous.tendsto (t, y)).eventually (lt_mem_nhds hS.2)
    filter_upwards [h1, hl] with u hu1 hul
    unfold gammaGK
    rw [threshold_gamma_coordinate_bridge_proved p (gk p lam) lam u.2 u.1 hp]
    have hn1 := norm_pos_of_Q hu1
    have hnl := norm_pos_of_Q hul
    rw [Complex.ofReal_one] at hn1
    simp only [bigG, GKSharp.obstacleG]
    rw [add_comm (1 : ℂ), add_comm (lam : ℂ), Real.rpow_def_of_pos hn1,
      Real.rpow_def_of_pos hnl]
    have he1 : Real.log ‖zeta u.2 u.1 + 1‖ = 1 / 2 * Real.log (Q 1 u.2 u.1) := by
      simpa only [chi, Complex.ofReal_one] using chi_eq 1 u.2 u.1
    have hel := chi_eq lam u.2 u.1
    change Real.log ‖zeta u.2 u.1 + (lam : ℂ)‖ = _ at hel
    rw [he1, hel, mul_comm (1 / 2 * Real.log (Q 1 u.2 u.1)) p,
      mul_comm (1 / 2 * Real.log (Q lam u.2 u.1)) p]
  have hh : ContDiffAt ℝ ω (fun u : ℝ × ℝ => Real.exp (-q p * u.2) *
      (gk p lam ^ p * Real.exp (p * (1 / 2 * Real.log (Q 1 u.2 u.1))) -
        Real.exp (p * (1 / 2 * Real.log (Q lam u.2 u.1))))) (t, y) := by
    have h1 := ((Q_contDiff 1).contDiffAt (x := (t, y))).log hS.1.ne'
    have hl := ((Q_contDiff lam).contDiffAt (x := (t, y))).log hS.2.ne'
    fun_prop
  exact hh.congr_of_eventuallyEq heq

/-- A scalar partial derivative is evaluation of the genuine Frechet derivative. -/
lemma dy_eq_fderiv {f : ℝ → ℝ → ℝ} {t y : ℝ}
    (hf : DifferentiableAt ℝ (fun u : ℝ × ℝ => f u.2 u.1) (t, y)) :
    dy f y t = fderiv ℝ (fun u : ℝ × ℝ => f u.2 u.1) (t, y) (0, 1) := by
  have hh := hf.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y t).prodMk (hasDerivAt_id y))
  exact hh.deriv

lemma dy_contDiffAt {f : ℝ → ℝ → ℝ} {t y : ℝ}
    (hf : ContDiffAt ℝ ω (fun u : ℝ × ℝ => f u.2 u.1) (t, y)) :
    ContDiffAt ℝ ω (fun u : ℝ × ℝ => dy f u.2 u.1) (t, y) := by
  have heq : (fun u : ℝ × ℝ => dy f u.2 u.1) =ᶠ[𝓝 (t, y)]
      (fun u => fderiv ℝ (fun v : ℝ × ℝ => f v.2 v.1) u (0, 1)) := by
    filter_upwards [hf.eventually (by simp)] with u hu
    exact dy_eq_fderiv (hu.differentiableAt (by simp))
  exact ((hf.fderiv_right (m := ω) (by simp)).clm_apply contDiffAt_const).congr_of_eventuallyEq heq

lemma scalar_isInvertible {L : ℝ →L[ℝ] ℝ} (h : L 1 ≠ 0) : L.IsInvertible := by
  have heq : L = (L 1) • ContinuousLinearMap.id ℝ ℝ := by
    ext x
    simpa using (L.map_smul x 1)
  rw [heq]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  · ext x
    simp [h, mul_assoc]
  · ext x
    simp [h, mul_assoc]

/-- Analytic scalar IFT with local uniqueness, applied to an actual partial derivative. -/
lemma critical_branch {f : ℝ → ℝ → ℝ} {t y : ℝ}
    (hf : ContDiffAt ℝ ω (fun u : ℝ × ℝ => f u.2 u.1) (t, y))
    (hz : dy f y t = 0) (hyy : dyy f y t ≠ 0) :
    ∃ branch : ℝ → ℝ, branch t = y ∧ ContDiffAt ℝ ω branch t ∧
      (∀ᶠ s in 𝓝 t, dy f (branch s) s = 0) ∧
      (∀ᶠ u : ℝ × ℝ in 𝓝 (t, y), dy f u.2 u.1 = 0 ↔ branch u.1 = u.2) := by
  let H : ℝ × ℝ → ℝ := fun u => dy f u.2 u.1
  have hH : ContDiffAt ℝ ω H (t, y) := dy_contDiffAt hf
  have hder : (fderiv ℝ H (t, y) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) 1 = dyy f y t := by
    have hh := dy_eq_fderiv (hH.differentiableAt (by simp))
    exact hh.symm
  have hi : (fderiv ℝ H (t, y) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible :=
    scalar_isInvertible (by rw [hder]; exact hyy)
  let branch := hH.implicitFunction (by simp) hi
  refine ⟨branch, hH.implicitFunction_apply_self (by simp) hi,
    hH.contDiffAt_implicitFunction (by simp) hi, ?_, ?_⟩
  · simpa only [H, hz] using hH.eventually_apply_implicitFunction (by simp) hi
  · simpa only [H, hz] using hH.eventually_apply_eq_iff_implicitFunction (by simp) hi

lemma contact_positiveBases (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) : PositiveBases lam (yContact p lam) (theta p) := by
  obtain ⟨hr, _, _, _⟩ := contact_root_properties hp hp2 hlam
  have hey : Real.exp (yContact p lam) = rContact p lam := Real.exp_log (by linarith)
  have hs : 0 < sn p := Real.sin_pos_of_pos_of_lt_pi
    (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hp)
  have hh (c : ℝ) : 0 < Q c (yContact p lam) (theta p) := by
    rw [Q_sos, hey]
    change 0 < (rContact p lam * Real.cos (theta p) + c) ^ 2 + (rContact p lam * sn p) ^ 2
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (mul_pos (by linarith) hs))
  exact ⟨hh 1, hh lam⟩

/-- The canonical Gamma has a genuine smooth stationary branch with local uniqueness. -/
theorem contact_critical_branch (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    ∃ branch : ℝ → ℝ, branch (theta p) = yContact p lam ∧
      ContDiffAt ℝ ω branch (theta p) ∧
      (∀ᶠ t in 𝓝 (theta p), dy (gammaGK p lam) (branch t) t = 0) ∧
      (∀ᶠ u : ℝ × ℝ in 𝓝 (theta p, yContact p lam),
        dy (gammaGK p lam) u.2 u.1 = 0 ↔ branch u.1 = u.2) := by
  obtain ⟨_, _, _, _, _, hz, hyy⟩ := contact_spec_proved p lam hp hp2 hlam
  exact critical_branch (gamma_contDiffAt p lam _ _ hp (contact_positiveBases p lam hp hp2 hlam)) hz hyy.ne'

end ContactSmooth
end GKSharp

#print axioms GKSharp.ContactSmooth.contact_critical_branch

