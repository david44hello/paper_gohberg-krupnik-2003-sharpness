/- Coverage of strengthened table/abstract claims in frozen short3.90.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Paper.Statements

namespace GKSharp.CoverageLinks.Delta390Links

open GKSharp GKSharp.Paper GKSharp.Threshold GKSharp.ComputerChecked

/-- P019_paper.tex:39 (abstract, W2-E67C1a), P019_paper.tex:70 (table, P47-P2a):
"outside this interval it is not sharp for any real ratio below and sufficiently close to $1$";
"for $p<p_0$ or $p>p_0'$, the bound is not sharp for real ratios $\lambda<1$ sufficiently close to $1$".
The full universal near-one conclusion is the corresponding conjunct of `thm_classification`.
All hypotheses below are exactly its named computer checks, not new assumptions. -/
theorem cover_delta390_near_one (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hcd : CheckCornerDerivatives) (hct : CheckCornerTails)
    (hbm : CheckStripBulkMiddle) (hbt : CheckStripBulkTails)
    (hc : CheckLocalF) (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p)
    (hout : p < p0 ∨ p0 / (p0 - 1) < p) :
    ∃ ε > 0, ∀ lam : ℝ, 1 - ε < lam → lam < 1 → gk p lam < pencilNorm P lam :=
  (thm_classification hn hr hcd hct hbm hbt hc hb hs hp P).2.2.2.1 hout

end GKSharp.CoverageLinks.Delta390Links
