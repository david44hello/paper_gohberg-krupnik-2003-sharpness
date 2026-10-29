/- GKSharp/Proofs/ContactEnvelope.lean — actual contact envelope and curvature.
Frozen source: short_v0.70/sec4b_failure.tex:29–32.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactSmooth
import GKSharp.Proofs.ObstacleMinimum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace GKSharp
open Threshold Set Filter
open scoped Topology ContDiff

namespace ContactSmooth

lemma dt_eq_fderiv {f : ℝ → ℝ → ℝ} {t y : ℝ}
    (hf : DifferentiableAt ℝ (fun u : ℝ × ℝ => f u.2 u.1) (t, y)) :
    dt f y t = fderiv ℝ (fun u : ℝ × ℝ => f u.2 u.1) (t, y) (1, 0) := by
  exact (hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))).deriv

lemma dt_contDiffAt {f : ℝ → ℝ → ℝ} {t y : ℝ}
    (hf : ContDiffAt ℝ ω (fun u : ℝ × ℝ => f u.2 u.1) (t, y)) :
    ContDiffAt ℝ ω (fun u : ℝ × ℝ => dt f u.2 u.1) (t, y) := by
  have heq : (fun u : ℝ × ℝ => dt f u.2 u.1) =ᶠ[𝓝 (t, y)]
      (fun u => fderiv ℝ (fun v : ℝ × ℝ => f v.2 v.1) u (1, 0)) := by
    filter_upwards [hf.eventually (by simp)] with u hu
    exact dt_eq_fderiv (hu.differentiableAt (by simp))
  exact ((hf.fderiv_right (m := ω) (by simp)).clm_apply contDiffAt_const).congr_of_eventuallyEq heq

lemma chain_deriv {f : ℝ → ℝ → ℝ} {branch : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ (fun u : ℝ × ℝ => f u.2 u.1) (t, branch t))
    (hb : DifferentiableAt ℝ branch t) :
    deriv (fun s => f (branch s) s) t = dt f (branch t) t + dy f (branch t) t * deriv branch t := by
  have hh := (hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hb.hasDerivAt)).deriv
  change deriv (fun s => f (branch s) s) t = _ at hh
  rw [hh, dt_eq_fderiv hf, dy_eq_fderiv hf]
  rw [show (1, deriv branch t) = (1, 0) + deriv branch t • ((0, 1) : ℝ × ℝ) by ext <;> simp]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

lemma mixed_partials {f : ℝ → ℝ → ℝ} {t y : ℝ}
    (hf : ContDiffAt ℝ ω (fun u : ℝ × ℝ => f u.2 u.1) (t, y)) :
    dy (dt f) y t = dty f y t := by
  let F : ℝ × ℝ → ℝ := fun u => f u.2 u.1
  have hD : DifferentiableAt ℝ (fderiv ℝ F) (t, y) :=
    (hf.fderiv_right (m := ω) (by simp)).differentiableAt (by simp)
  have heq (v : ℝ × ℝ) (part : ℝ → ℝ → ℝ)
      (hpart : ∀ u, DifferentiableAt ℝ F u → part u.2 u.1 = fderiv ℝ F u v) :
      fderiv ℝ (fun u : ℝ × ℝ => part u.2 u.1) (t, y) =
        fderiv ℝ (fun u => fderiv ℝ F u v) (t, y) := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hf.eventually (by simp)] with u hu
    exact hpart u (hu.differentiableAt (by simp))
  rw [dy_eq_fderiv ((dt_contDiffAt hf).differentiableAt (by simp))]
  change _ = dt (dy f) y t
  rw [dt_eq_fderiv ((dy_contDiffAt hf).differentiableAt (by simp))]
  rw [heq (1, 0) (dt f) (fun u hu => dt_eq_fderiv hu),
    heq (0, 1) (dy f) (fun u hu => dy_eq_fderiv hu)]
  rw [fderiv_clm_apply hD (differentiableAt_const _), fderiv_clm_apply hD (differentiableAt_const _)]
  simpa using (hf.isSymmSndFDerivAt_of_omega (0, 1) (1, 0))

/-- Schur complement is the second derivative of the actual stationary envelope. -/
lemma stationary_curvature {f : ℝ → ℝ → ℝ} {branch : ℝ → ℝ} {t : ℝ}
    (hf : ContDiffAt ℝ ω (fun u : ℝ × ℝ => f u.2 u.1) (t, branch t))
    (hb : ContDiffAt ℝ ω branch t) (hz : ∀ᶠ s in 𝓝 t, dy f (branch s) s = 0)
    (hyy : dyy f (branch t) t ≠ 0) :
    deriv (deriv (fun s => f (branch s) s)) t =
      dtt f (branch t) t - dty f (branch t) t ^ 2 / dyy f (branch t) t := by
  have hbd := hb.differentiableAt (by simp)
  have hcrit := chain_deriv ((dy_contDiffAt hf).differentiableAt (by simp)) hbd
  have hzero : deriv (fun s => dy f (branch s) s) t = 0 := by
    have heq : (fun s => dy f (branch s) s) =ᶠ[𝓝 t] (fun _ => 0) := hz
    rw [heq.deriv_eq]
    exact deriv_const t 0
  have hbp : deriv branch t = -dty f (branch t) t / dyy f (branch t) t := by
    rw [hzero] at hcrit
    apply (eq_div_iff hyy).mpr
    change 0 = dty f (branch t) t + dyy f (branch t) t * deriv branch t at hcrit
    linarith
  have heq : deriv (fun s => f (branch s) s) =ᶠ[𝓝 t] (fun s => dt f (branch s) s) := by
    have htend : Tendsto (fun s => (s, branch s)) (𝓝 t) (𝓝 (t, branch t)) :=
      continuousAt_id.prodMk hb.continuousAt
    filter_upwards [htend.eventually (hf.eventually (by simp)), hb.eventually (by simp), hz]
      with s hfs hbs hzs
    rw [chain_deriv (hfs.differentiableAt (by simp)) (hbs.differentiableAt (by simp)), hzs]
    ring
  rw [heq.deriv_eq, chain_deriv ((dt_contDiffAt hf).differentiableAt (by simp)) hbd,
    mixed_partials hf, hbp]
  unfold dtt
  ring

end ContactSmooth

/-- The full approved contact-envelope target: actual branch, smoothness,
stationarity, upper bound for the canonical obstacle, and exact Schur curvature. -/
theorem contact_envelope_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    ∃ branch : ℝ → ℝ, ∃ eps > 0,
      branch (theta p) = yContact p lam ∧
      ContDiffOn ℝ ∞ branch (Ioo (theta p - eps) (theta p + eps)) ∧
      (∀ t ∈ Ioo (theta p - eps) (theta p + eps),
        dy (gammaGK p lam) (branch t) t = 0 ∧
        Threshold.obstacle p lam t ≤ gammaGK p lam (branch t) t) ∧
      deriv (deriv (fun t => gammaGK p lam (branch t) t)) (theta p) = muSecond p lam := by
  obtain ⟨branch, hpoint, hb, hstat, _⟩ := ContactSmooth.contact_critical_branch p lam hp hp2 hlam
  have hf := ContactSmooth.gamma_contDiffAt p lam _ _ hp
    (ContactSmooth.contact_positiveBases p lam hp hp2 hlam)
  have hf' : ContDiffAt ℝ ω (fun u : ℝ × ℝ => gammaGK p lam u.2 u.1)
      (theta p, branch (theta p)) := by simpa only [hpoint] using hf
  obtain ⟨_, _, _, _, _, _, hyy⟩ := contact_spec_proved p lam hp hp2 hlam
  have hcurv := ContactSmooth.stationary_curvature hf' hb hstat (by simpa only [hpoint] using hyy.ne')
  obtain ⟨U, hU, hC⟩ := hb.contDiffOn (m := ∞) (by simp) (by simp)
  obtain ⟨eps, heps, hall⟩ := Metric.eventually_nhds_iff.mp (hstat.and hU)
  have hsubset : Ioo (theta p - eps) (theta p + eps) ⊆ U := by
    intro t ht
    exact (hall (by rw [Real.dist_eq]; exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).2
  have hCmax : max 1 ‖(lam : ℂ)‖ < gk p lam := gk_gt_max hp (ne_of_lt hp2) (by
    intro heq
    have : lam = 1 := by exact_mod_cast heq
    linarith [hlam.2])
  refine ⟨branch, eps, heps, hpoint, hC.mono hsubset, ?_, ?_⟩
  · intro t ht
    refine ⟨(hall (by rw [Real.dist_eq]; exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).1, ?_⟩
    exact csInf_le (obstacle_bddBelow (by linarith) (lam : ℂ) hCmax t) ⟨branch t, rfl⟩
  · simpa only [hpoint, muSecond] using hcurv

end GKSharp

#print axioms GKSharp.contact_envelope_proved

