/- complete Proposition edge at the actual local threshold.
Frozen source: short_v0.70/sec4b_failure.tex:111–136.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.EndpointEstimate
import GKSharp.Proofs.AxisOrigin
import GKSharp.Proofs.Sec4bChecks
import GKSharp.Proofs.StripLeaves
import GKSharp.Proofs.LocalGapCertificate
import GKSharp.Proofs.Sec4Limits
import GKSharp.Proofs.Sec4Continuity
import GKSharp.Proofs.LocalConsequences

namespace GKSharp
open Threshold Set ComputerChecked

/-- The endpoint value required by C*, with only the three original explicit checks. -/
theorem boundary_edge_proved (hc : CheckLocalF) (hb : CheckBoundaryBulk)
    (hs : CheckBoundarySliver) (p : ℝ) (hp : 1 < p) (hpc : p < pc) :
    Threshold.h p (lambdaLoc p) < 0 := by
  by_cases hsmall : p ≤ 1000001 / 1000000
  · have hh : p ≤ 1 + (10 : ℝ) ^ (-6 : ℤ) := by norm_num; linarith
    exact (endpoint_estimate_proved hp hh).2
  · by_cases hbulk : p ≤ 6067 / 5000
    · exact boundary_bulk_proved hb p ⟨by linarith, hbulk⟩
    · exact boundary_sliver_proved cDelta_eq_gk_proved hc hs checkLocalGap_proved p ⟨by linarith, hpc⟩

/-- The full original ClaimEdge, including least-zero existence and the actual operator norm. -/
theorem sec4_prop_edge_proved (hc : CheckLocalF) (hb : CheckBoundaryBulk)
    (hs : CheckBoundarySliver) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) :
    1 < p → p < pc → Threshold.h p (lambdaLoc p) < 0 ∧
      IsLeast (axisZeros p) (lambda0 p) ∧ 0 < lambda0 p ∧ lambda0 p < lambdaLoc p ∧
      gk p (lambdaLoc p) < pencilNorm P (lambdaLoc p) := by
  intro hp hpc
  have hp2 : p < 2 := by have hh := (pc_spec_proved hc).2.1.2; linarith
  have hl := ((lambdaLoc_spec_proved hc).1 p ⟨hp, hpc⟩).2
  have hedge := boundary_edge_proved hc hb hs p hp hpc
  have hcont : ContinuousOn (Threshold.h p) (Icc 0 (lambdaLoc p)) :=
    (sec4_h_continuousOn_proved p hp hp2).mono (by
      intro lam hlam
      exact ⟨by linarith [hlam.1], lt_of_le_of_lt hlam.2 hl.2⟩)
  obtain ⟨hzero, hzero0, hzerol⟩ := first_axis_zero_of_proved p
    (axis_zero_positive_proved p hp hp2) hl.1 hcont hedge
  refine ⟨hedge, hzero, hzero0, hzerol, ?_⟩
  exact sec4_axis_negative_fails_proved p P hp hp2 (lambdaLoc p)
    ⟨by linarith [hl.1], hl.2⟩ hedge

end GKSharp

#print axioms GKSharp.boundary_edge_proved
#print axioms GKSharp.sec4_prop_edge_proved
