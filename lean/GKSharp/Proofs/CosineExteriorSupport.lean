/- the exterior cosine-support application in Proposition Q, route R13.
Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.CosineNecessity
import GKSharp.Proofs.TheoremRIf

namespace GKSharp

open Set Threshold

/-- short_v0.70/sec4a_criterion.tex:31-33: "So $m_{\GK} \ge \varphi \ge K\cos(qt)$ on $[\theta_0, \pi]$".
The K-valued arch is the result of the already proved amplitude identification. -/
theorem sec4_cosine_exterior_support_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (_hlam : lam ∈ Ico (-1 : ℝ) 1) (ff : ℝ → ℝ) (hf : QSubtrig (q p) ff)
    (hminor : ∀ t, ff t ≤ Threshold.obstacle p lam t)
    (harch : ∀ t ∈ Icc (-theta p) (theta p), ff t = kConst p lam * Real.cos (q p * t)) :
    ∀ t ∈ Icc (theta p) Real.pi,
      kConst p lam * Real.cos (q p * t) ≤ ff t ∧ ff t ≤ Threshold.obstacle p lam t := by
  have hconv := (TheoremRIf.qsub_continuous_trigconvex_proved (q p)
    (by unfold q; linarith) ff hf).2
  have htt0 : 0 < theta p := div_pos Real.pi_pos (by linarith)
  have htti : theta p < Real.pi := div_lt_self Real.pi_pos hp
  have hqtt : q p * theta p = Real.pi / 2 := by
    unfold q theta
    field_simp [show p ≠ 0 by linarith]
  have hs := cosine_support_of_arch (by unfold q; linarith) (by unfold q; linarith)
    htt0 htti hqtt hconv harch
  intro t ht
  exact ⟨hs t ⟨htt0.le.trans ht.1, ht.2⟩, hminor t⟩

end GKSharp

#print axioms GKSharp.sec4_cosine_exterior_support_proved
