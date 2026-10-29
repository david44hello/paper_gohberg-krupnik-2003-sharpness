/- GKSharp/Proofs/ContactObstacleEndpoint.lean — smooth actual endpoint obstacle.
Frozen source: short_v0.70/sec4_criterion.tex:28.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactEndpoint

namespace GKSharp.ContactSmooth
open GKSharp.Threshold GKSharp.ContactCalc Set Filter
open scoped Topology ContDiff

/-- Smoothness at lambda=-1 uses its genuine y=0 contact. -/
theorem obstacle_regular_endpoint (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    (∃ eps > 0, ContDiffOn ℝ ∞ (Threshold.obstacle p (-1))
      (Ioo (theta p - eps) (theta p + eps))) ∧
    deriv (Threshold.obstacle p (-1)) (theta p) = dt (gammaGK p (-1)) 0 (theta p) := by
  obtain ⟨_, hz, hyy, hstrict⟩ := endpoint_contact_data p hp hp2
  have hs := sec4a_sn_pos hp
  have hQ (c : ℝ) : 0 < Q c 0 (theta p) := by
    rw [Q_sos, Real.exp_zero, one_mul, one_mul]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hs)
  have hf := gamma_contDiffAt p (-1) 0 (theta p) hp ⟨hQ 1, hQ (-1)⟩
  obtain ⟨branch, hpoint, hb, _, hlocal⟩ := critical_branch hf hz hyy.ne'
  have hC : max 1 ‖((-1 : ℝ) : ℂ)‖ < gk p (-1 : ℝ) :=
    gk_gt_max hp (ne_of_lt hp2) (by norm_num)
  obtain ⟨Y, _, hY⟩ := exists_obstacle_min_compact (p := p) (C := gk p (-1 : ℝ))
    (by linarith) ((-1 : ℝ) : ℂ) hC
  have hF : Continuous (fun u : ℝ × ℝ => gammaGK p (-1) u.2 u.1) := by
    unfold gammaGK Threshold.gamma GKSharp.gamma unitPoint
    fun_prop (disch := positivity)
  have hmatch := minimum_eq_branch (K := Icc (-Y) Y) hF isCompact_Icc hstrict hlocal
  have heq : Threshold.obstacle p (-1) =ᶠ[𝓝 (theta p)]
      (fun t => gammaGK p (-1) (branch t) t) := by
    filter_upwards [hmatch] with t ht
    obtain ⟨y, hy, hmin, hvalue⟩ := hY t
    have hby := ht y hy hmin
    simpa only [Threshold.obstacle, gammaGK, Threshold.gamma, hby] using hvalue
  have hf' : ContDiffAt ℝ ω (fun u : ℝ × ℝ => gammaGK p (-1) u.2 u.1)
      (theta p, branch (theta p)) := by simpa only [hpoint] using hf
  have hpair : ContDiffAt ℝ ω (fun t : ℝ => (t, branch t)) (theta p) := contDiffAt_id.prodMk hb
  have hmu : ContDiffAt ℝ ω (fun t => gammaGK p (-1) (branch t) t) (theta p) :=
    ContDiffAt.comp (theta p) (f := fun t : ℝ => (t, branch t))
      (g := fun u : ℝ × ℝ => gammaGK p (-1) u.2 u.1) hf' hpair
  have hobs := hmu.congr_of_eventuallyEq heq
  obtain ⟨U, hU, hCreg⟩ := hobs.contDiffOn (m := ∞) (by simp) (by simp)
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hU
  constructor
  · refine ⟨eps, heps, hCreg.mono ?_⟩
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · rw [heq.deriv_eq, chain_deriv (hf'.differentiableAt (by simp)) (hb.differentiableAt (by simp)),
      hpoint, hz]
    ring

end GKSharp.ContactSmooth

#print axioms GKSharp.ContactSmooth.obstacle_regular_endpoint
