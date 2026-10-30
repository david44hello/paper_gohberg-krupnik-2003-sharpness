/- GKSharp/Proofs/ContactObstacle.lean — identify the actual obstacle near contact.
Frozen source: short_v2.30/sec5e_cstar.tex:13–14 ("m_GK = μ_* near θ₀, since the minimiser is unique ... and
non-degenerate"; printed for 0 < λ < 1, proved here for −1 < λ < 1).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactMinimum
import GKSharp.Proofs.ContactEnvelope

namespace GKSharp
open Threshold ContactCalc Set Filter
open scoped Topology ContDiff

namespace ContactSmooth

/-- The contact is a strict global minimum of the actual Gamma, not merely a stationary point. -/
lemma gamma_contact_strict_min (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) (y : ℝ) (hy : y ≠ yContact p lam) :
    gammaGK p lam (yContact p lam) (theta p) < gammaGK p lam y (theta p) := by
  have hcontact := (contact_spec_proved p lam hp hp2 hlam).2.2.2.2.1
  rw [hcontact, sec4b_gammaGK_eq]
  let R := Real.exp y
  let C := gk p lam
  let A := 2 * Real.cosh y + 2 * Real.cos (theta p)
  let B := Real.exp y + lam ^ 2 * Real.exp (-y) + 2 * (lam * Real.cos (theta p))
  have hR : 0 < R := Real.exp_pos y
  have hC : 1 < C := lt_of_le_of_lt (le_max_left _ _)
    (gk_gt_max hp (ne_of_lt hp2) (by
      intro hh
      have : lam = 1 := by exact_mod_cast hh
      linarith [hlam.2]))
  have hs : 0 < sn p := sec4a_sn_pos hp
  have hQ (c : ℝ) : 0 < Q c y (theta p) := by
    rw [Q_sos]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (mul_pos hR hs))
  have hRA : R * A = Q 1 y (theta p) := by
    dsimp [R, A, Q]
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp
    ring
  have hRB : R * B = Q lam y (theta p) := by
    dsimp [R, B, Q]
    rw [Real.exp_neg]
    field_simp
    ring
  have hA : 0 < A := pos_of_mul_pos_right (hRA.symm ▸ hQ 1) hR.le
  have hB : 0 < B := pos_of_mul_pos_right (hRB.symm ▸ hQ lam) hR.le
  have hne : R ≠ rContact p lam := by
    intro heq
    apply hy
    have hh := congrArg Real.log heq
    simpa only [R, Real.log_exp, yContact] using hh
  have hgap := contact_ray_squared_gap p lam R hp hp2 hlam
  have hgap' : R * (C ^ 2 * A - B) = (C ^ 2 - 1) * (R - rContact p lam) ^ 2 := by
    rw [mul_sub, ← mul_assoc, mul_comm R (C ^ 2), mul_assoc, hRA, hRB]
    dsimp [Q, R] at *
    simp only [cs, theta] at hgap ⊢
    dsimp [C]
    linear_combination hgap
  have hpositive : 0 < C ^ 2 * A - B := by
    have hh : 0 < (C ^ 2 - 1) * (R - rContact p lam) ^ 2 :=
      mul_pos (by nlinarith [sq_nonneg (C - 1)]) (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
    exact pos_of_mul_pos_right (hgap'.symm ▸ hh) hR.le
  have hpow : C ^ p * A ^ (p / 2) = (C ^ 2 * A) ^ (p / 2) := by
    rw [Real.mul_rpow (sq_nonneg C) hA.le, ← Real.rpow_natCast C 2, ← Real.rpow_mul (by linarith : 0 ≤ C)]
    congr 2
    ring
  change 0 < C ^ p * A ^ (p / 2) - B ^ (p / 2)
  rw [hpow]
  exact sub_pos.mpr (Real.rpow_lt_rpow hB.le (by linarith) (by linarith))

/-- Interior ratios: the actual infimum equals the analytic stationary branch nearby. -/
theorem obstacle_branch_interior (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    ∃ branch : ℝ → ℝ, branch (theta p) = yContact p lam ∧ ContDiffAt ℝ ω branch (theta p) ∧
      ∀ᶠ t in 𝓝 (theta p), Threshold.obstacle p lam t = gammaGK p lam (branch t) t := by
  obtain ⟨branch, hpoint, hb, _, hlocal⟩ := contact_critical_branch p lam hp hp2 hlam
  have hC : max 1 ‖(lam : ℂ)‖ < gk p lam := gk_gt_max hp (ne_of_lt hp2) (by
    intro hh
    have : lam = 1 := by exact_mod_cast hh
    linarith [hlam.2])
  obtain ⟨Y, _, hY⟩ := exists_obstacle_min_compact (p := p) (C := gk p lam) (by linarith) (lam : ℂ) hC
  have hF : Continuous (fun u : ℝ × ℝ => gammaGK p lam u.2 u.1) := by
    unfold gammaGK Threshold.gamma GKSharp.gamma unitPoint
    fun_prop (disch := positivity)
  have hmatch := minimum_eq_branch (K := Icc (-Y) Y) hF isCompact_Icc
    (gamma_contact_strict_min p lam hp hp2 hlam) hlocal
  refine ⟨branch, hpoint, hb, ?_⟩
  filter_upwards [hmatch] with t ht
  obtain ⟨y, hy, hmin, hvalue⟩ := hY t
  have hby := ht y hy hmin
  simpa only [Threshold.obstacle, gammaGK, Threshold.gamma, hby] using hvalue

/-- Genuine smoothness of the actual obstacle for interior ratios. The endpoint
and the closed-form angular derivative are separate obligations. -/
theorem obstacle_regular_interior (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    (∃ eps > 0, ContDiffOn ℝ ∞ (Threshold.obstacle p lam)
      (Ioo (theta p - eps) (theta p + eps))) ∧
    deriv (Threshold.obstacle p lam) (theta p) = dt (gammaGK p lam) (yContact p lam) (theta p) := by
  obtain ⟨branch, hpoint, hb, heq⟩ := obstacle_branch_interior p lam hp hp2 hlam
  have hf := gamma_contDiffAt p lam _ _ hp (contact_positiveBases p lam hp hp2 hlam)
  have hf' : ContDiffAt ℝ ω (fun u : ℝ × ℝ => gammaGK p lam u.2 u.1)
      (theta p, branch (theta p)) := by simpa only [hpoint] using hf
  have hpair : ContDiffAt ℝ ω (fun t : ℝ => (t, branch t)) (theta p) := contDiffAt_id.prodMk hb
  have hmu : ContDiffAt ℝ ω (fun t => gammaGK p lam (branch t) t) (theta p) :=
    ContDiffAt.comp (theta p) (f := fun t : ℝ => (t, branch t))
      (g := fun u : ℝ × ℝ => gammaGK p lam u.2 u.1) hf' hpair
  have heq' : Threshold.obstacle p lam =ᶠ[𝓝 (theta p)] (fun t => gammaGK p lam (branch t) t) := heq
  have hobs := hmu.congr_of_eventuallyEq heq'
  obtain ⟨U, hU, hC⟩ := hobs.contDiffOn (m := ∞) (by simp) (by simp)
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hU
  constructor
  · refine ⟨eps, heps, hC.mono ?_⟩
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · rw [heq'.deriv_eq, chain_deriv (hf'.differentiableAt (by simp)) (hb.differentiableAt (by simp)), hpoint,
      (contact_spec_proved p lam hp hp2 hlam).2.2.2.2.2.1]
    ring

end ContactSmooth
end GKSharp

#print axioms GKSharp.ContactSmooth.obstacle_branch_interior
#print axioms GKSharp.ContactSmooth.obstacle_regular_interior
