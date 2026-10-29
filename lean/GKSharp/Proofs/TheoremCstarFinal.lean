/-
GKSharp/Proofs/TheoremCstarFinal.lean — Theorem C*, short v0.70 P019_paper.tex l.137-140 (proof sec5e_cstar.tex
l.7-26): for 1 < p < 2 and 0 < λ < 1, ‖P₊ + λP₋‖_p = GK_p(λ) iff h(λ, p) ≥ 0 and λ < λ_loc(p). The last input of
`thm_Cstar_of` is the edge value h(λ_loc(p), p) < 0 for p < p_c (Proposition edge, sec4b_failure.tex l.111-114).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.TheoremCstar
import GKSharp.Proofs.PropositionEdge

namespace GKSharp.Proofs.TheoremCstarFinal

open GKSharp GKSharp.ComputerChecked

/-- Theorem C*, given the computer checks of Proposition edge and of λ_loc (CheckLocalF). -/
theorem thm_Cstar_proved (hc : CheckLocalF) (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp1 : 1 < p) (hp2 : p < 2) (P : RieszProjection p)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    pencilNorm P lam = gk p lam ↔
      kConst p lam ≤ obstacle p (gk p lam) lam 0 ∧ lam < Threshold.lambdaLoc p :=
  TheoremCstar.thm_Cstar_of TheoremCstar.kf_slope hc hp1 hp2 P
    (fun hpc => boundary_edge_proved hc hb hs p hp1 hpc) hl0 hl1

end GKSharp.Proofs.TheoremCstarFinal
