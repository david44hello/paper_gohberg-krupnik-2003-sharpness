/- GKSharp/Proofs/PropSFinal.lean - the row sec5_prop_S (Proposition S, sec5f_strip.tex l.38-40, l.67-71), slice (b)
v1.40 type with its seven explicit checks: PropS.sec5_prop_S_of_cstarIf with the proved "if" half of Theorem C*
(TheoremCstar.cstar_if_proved).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.PropS
import GKSharp.Proofs.TheoremCstar

namespace GKSharp

open Set GKSharp.Threshold GKSharp.ComputerChecked

/-- Proposition S (the strip), sec5f_strip.tex l.38-40: "Let p₀ ≤ p ≤ 1.268 and 0 < λ < 1. Then h(λ, p) > 0. Hence
‖P₊ + λP₋‖_p = GK_p(λ) for every real λ when p₀ ≤ p < 3 − √3". The six strip checks and `CheckLocalF` (for
`λ_loc = 1`, as `p_c < p₀`) are explicit; `ClaimS p P` is written out. -/
theorem sec5_prop_S_proved (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hcd : CheckCornerDerivatives) (hct : CheckCornerTails) (hbm : CheckStripBulkMiddle)
    (hbt : CheckStripBulkTails) (hc : CheckLocalF) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) :
    (p ∈ Icc p0 (317 / 250 : ℝ) → ∀ lam ∈ Ioo (0 : ℝ) 1, 0 < h p lam) ∧
    (p ∈ Ico p0 (3 - Real.sqrt 3) → ∀ lam : ℝ, pencilNorm P lam = gk p lam) :=
  PropS.sec5_prop_S_of_cstarIf
    (fun hp1 hp2 P _ hl0 hl1 hh hloc => Proofs.TheoremCstar.cstar_if_proved hp1 hp2 P hl0 hl1 hh hloc)
    hn hr hcd hct hbm hbt hc p P

end GKSharp
