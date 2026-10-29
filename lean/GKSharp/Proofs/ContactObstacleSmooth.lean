/- GKSharp/Proofs/ContactObstacleSmooth.lean — assembly with explicit angular derivative leaves.
Frozen source: short_v0.70/sec4_criterion.tex:28.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactObstacle
import GKSharp.Proofs.ContactObstacleEndpoint

namespace GKSharp
open Threshold Set
open scoped ContDiff

/-- Assembly helper, not a completed paper row. The actual angular derivative
identities are explicit premises until their scalar proofs are delivered. -/
theorem obstacle_smooth_contact_of_dt (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1)
    (hinterior : lam ∈ Ioo (-1 : ℝ) 1 →
      dt (gammaGK p lam) (yContact p lam) (theta p) = -q p * kConst p lam)
    (hendpoint : lam = -1 → dt (gammaGK p lam) 0 (theta p) = -q p * kConst p lam) :
    ∃ eps > 0, ContDiffOn ℝ ∞ (Threshold.obstacle p lam)
      (Ioo (theta p - eps) (theta p + eps)) ∧
      deriv (Threshold.obstacle p lam) (theta p) = -q p * kConst p lam := by
  by_cases heq : lam = -1
  · subst lam
    obtain ⟨⟨eps, heps, hreg⟩, hd⟩ := ContactSmooth.obstacle_regular_endpoint p hp hp2
    exact ⟨eps, heps, hreg, hd.trans (hendpoint rfl)⟩
  · have hl : lam ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · by_contra hh
        exact heq (by linarith [hlam.1])
      · exact hlam.2
    obtain ⟨⟨eps, heps, hreg⟩, hd⟩ := ContactSmooth.obstacle_regular_interior p lam hp hp2 hl
    exact ⟨eps, heps, hreg, hd.trans (hinterior hl)⟩

end GKSharp

#print axioms GKSharp.obstacle_smooth_contact_of_dt
