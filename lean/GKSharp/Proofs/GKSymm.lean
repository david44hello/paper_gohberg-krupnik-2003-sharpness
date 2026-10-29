/- GKSharp/Proofs/GKSymm.lean - GK_p(1) = 1 and N_p(1) = 1 (P019_paper.tex l.55-57, sec5_sharp_inequality.tex
l.177-178).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GKRoot
import GKSharp.Proofs.PencilModes
import GKSharp.Proofs.Pencil

namespace GKSharp

open ComplexConjugate

/-- `GK_p(1) = 1`. -/
theorem gk_one (p : ℝ) : gk p 1 = 1 := by
  have h : gkRootHi p 1 = 1 := by
    unfold gkRootHi gkMid
    norm_num
  exact (pow_left_inj₀ (gk_nonneg _ _) zero_le_one two_ne_zero).1 (by rw [gk_sq_eq, h, one_pow])

/-- `N_p(1) = 1`, as `P₊ + P₋ = I`. -/
theorem pencilNorm_one {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) : pencilNorm P 1 = 1 := by
  apply le_antisymm
  · show ‖pencil P 1 1‖ ≤ 1
    rw [pencil_one]
    exact ContinuousLinearMap.norm_id_le
  · have h := max_one_le_pencilNorm P 1
    rw [norm_one, max_self] at h
    exact h

end GKSharp
