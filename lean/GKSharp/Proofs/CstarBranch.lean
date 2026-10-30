/- GKSharp/Proofs/CstarBranch.lean — Theorem C*: the actual obstacle equals μ near the contact angle.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactObstacle

namespace GKSharp.Proofs.CstarBranch

open GKSharp GKSharp.Threshold GKSharp.ContactCalc GKSharp.ContactSmooth Set Filter
open scoped Topology ContDiff

/-- The minimiser of Γ_C at the contact angle is unique (Lemma E) and non-degenerate, so the actual obstacle m_GK
equals μ(t) = Γ_C(y_*(t), t) near θ₀ = π/p, for the smooth stationary branch y_* with y_*(θ₀) = log r. -/
theorem sec5e_mGK_eq_mu_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1) :
    ∃ ystar : ℝ → ℝ, ystar (Real.pi / p) = yContact p lam ∧ ContDiffAt ℝ ∞ ystar (Real.pi / p) ∧
      (∀ᶠ t in 𝓝 (Real.pi / p), dy (gammaGK p lam) (ystar t) t = 0) ∧
      ∀ᶠ t in 𝓝 (Real.pi / p), GKSharp.obstacle p (gk p lam) lam t = gammaGK p lam (ystar t) t := by
  rw [show Real.pi / p = theta p from rfl]
  have hlam : lam ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hl1⟩
  obtain ⟨branch, hpoint, hb, hstat, hlocal⟩ := contact_critical_branch p lam hp1 hp2 hlam
  have hC : max 1 ‖(lam : ℂ)‖ < gk p lam := gk_gt_max hp1 (ne_of_lt hp2) (by
    intro hh
    have : lam = 1 := by exact_mod_cast hh
    linarith)
  obtain ⟨Y, _, hY⟩ := exists_obstacle_min_compact (p := p) (C := gk p lam) (by linarith) (lam : ℂ) hC
  have hF : Continuous (fun u : ℝ × ℝ => gammaGK p lam u.2 u.1) := by
    unfold gammaGK Threshold.gamma GKSharp.gamma unitPoint
    fun_prop (disch := positivity)
  have hmatch := minimum_eq_branch (K := Icc (-Y) Y) hF isCompact_Icc
    (gamma_contact_strict_min p lam hp1 hp2 hlam) hlocal
  refine ⟨branch, hpoint, hb.of_le le_top, hstat, ?_⟩
  filter_upwards [hmatch] with t ht
  obtain ⟨y, hy, hmin, hvalue⟩ := hY t
  have hby := ht y hy hmin
  simpa only [gammaGK, Threshold.gamma, hby] using hvalue

end GKSharp.Proofs.CstarBranch
