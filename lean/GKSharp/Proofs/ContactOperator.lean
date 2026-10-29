/- GKSharp/Proofs/ContactOperator.lean — positive contact coefficient and local operator failure.
Frozen source: short_v0.70/sec4a_criterion.tex:22 and sec4b_failure.tex:17–22.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GKLowerReal
import GKSharp.Proofs.ContactObstruction

namespace GKSharp
open Threshold Set

theorem contact_kConst_pos (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) : 0 < kConst p lam := by
  have hC : 1 < gk p lam := lt_of_le_of_lt (le_max_left _ _)
    (gk_gt_max hp (ne_of_lt hp2) (by
      intro hh
      have : lam = 1 := by exact_mod_cast hh
      linarith [hlam.2]))
  have hsin : 0 < Real.sin (Real.pi / p) := sin_theta_positive hp
  have hcos : 0 < -Real.cos (Real.pi / p) := neg_pos.mpr (cos_theta_negative hp hp2)
  have hbase : 0 < gk p lam ^ 2 + lam := by nlinarith [hlam.1, sq_nonneg (gk p lam - 1)]
  unfold kConst
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2)
    (sub_pos.mpr hlam.2)) (by linarith)) (Real.rpow_pos_of_pos hsin _))
      (Real.rpow_pos_of_pos hcos _)) (Real.rpow_pos_of_pos hbase _)

/-- Operator assembly helper; the necessity direction of Proposition Q is an
explicit input until that theorem is installed. No extra lower-bound premise. -/
theorem local_failure_of_cosine_criterion (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p)
    (hp : 1 < p) (hp2 : p < 2) (lam : ℝ) (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (hlocal : 1 < localTest p lam)
    (hcriterion : pencilNorm P lam = gk p lam →
      ∀ t ∈ Icc (-Real.pi) Real.pi, kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t) :
    gk p lam < pencilNorm P lam := by
  have hl : lam ∈ Ico (-1 : ℝ) 1 := ⟨by linarith [hlam.1], hlam.2⟩
  have hge := gk_le_pencilNorm_real p P hp hp2 lam hl
  by_contra hn
  have heq : pencilNorm P lam = gk p lam := le_antisymm (le_of_not_gt hn) hge
  exact (localTest_excludes_cosine_minorant p lam (kConst p lam) hp hp2 hlam hlocal) (hcriterion heq)

end GKSharp

#print axioms GKSharp.contact_kConst_pos
#print axioms GKSharp.local_failure_of_cosine_criterion
