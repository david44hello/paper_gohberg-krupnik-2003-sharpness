/- Coverage links for the approved targets of slice SliceB: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 2a9233424ca2e13c4810a581e2c45f0e; do not edit. -/
import GKSharp.Defs.RealLine
import GKSharp.Defs.Pencil
import GKSharp.Defs.Potential
import GKSharp.Defs.Threshold
import GKSharp.Proofs.LocalFCertificate
import GKSharp.Defs.ThresholdAnalysis
import GKSharp.ComputerChecked
import GKSharp.Paper.Statements

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceB

namespace GKSharp.Proposal14

noncomputable section
open Set Filter GKSharp.Threshold
open scoped Topology ContDiff

abbrev zeta := GKSharp.Threshold.zeta
abbrev bigG := GKSharp.Threshold.bigG
abbrev gamma := GKSharp.Threshold.gamma
abbrev obstacleAt := GKSharp.Threshold.obstacleAt
abbrev obstacle := GKSharp.Threshold.obstacle
abbrev h := GKSharp.Threshold.h
abbrev axisZeros := GKSharp.Threshold.axisZeros
abbrev lambda0 := GKSharp.Threshold.lambda0
abbrev cDelta := GKSharp.Threshold.cDelta
abbrev powSlope := GKSharp.Threshold.powSlope
abbrev phi := GKSharp.Threshold.phi
abbrev tOne := GKSharp.Threshold.tOne
abbrev kap := GKSharp.Threshold.kap
abbrev g := GKSharp.Threshold.g
abbrev axisUpper := GKSharp.Threshold.axisUpper
abbrev exprel := GKSharp.Threshold.exprel
abbrev eta1 := GKSharp.Threshold.eta1
abbrev sEta := GKSharp.Threshold.sEta
abbrev deltaEta := GKSharp.Threshold.deltaEta
abbrev vWeight := GKSharp.Threshold.vWeight
abbrev etilde := GKSharp.Threshold.etilde
abbrev eTwo := GKSharp.Threshold.eTwo
abbrev cFour := GKSharp.Threshold.cFour
abbrev lowTail := GKSharp.Threshold.lowTail
abbrev highTail := GKSharp.Threshold.highTail
abbrev a0 := GKSharp.Threshold.a0
abbrev b0 := GKSharp.Threshold.b0
abbrev b1 := GKSharp.Threshold.b1
abbrev bulkDomain := GKSharp.Threshold.bulkDomain
abbrev theta := GKSharp.Threshold.theta
abbrev sigmaContact := GKSharp.Threshold.sigmaContact
abbrev rContact := GKSharp.Threshold.rContact
abbrev yContact := GKSharp.Threshold.yContact
abbrev vContact := GKSharp.Threshold.vContact
abbrev dOne := GKSharp.Threshold.dOne
abbrev mobContact := GKSharp.Threshold.mobContact
abbrev chi := GKSharp.Threshold.chi
abbrev logGap := GKSharp.Threshold.logGap
abbrev weightP := GKSharp.Threshold.weightP
abbrev dy := GKSharp.Threshold.dy
abbrev dt := GKSharp.Threshold.dt
abbrev dyy := GKSharp.Threshold.dyy
abbrev dtt := GKSharp.Threshold.dtt
abbrev dty := GKSharp.Threshold.dty
abbrev gammaGK := GKSharp.Threshold.gammaGK
abbrev muSecond := GKSharp.Threshold.muSecond
abbrev bZero := GKSharp.Threshold.bZero
abbrev signBracket := GKSharp.Threshold.signBracket
abbrev TrigConvexOn := GKSharp.Threshold.TrigConvexOn
abbrev QTrigConvex := GKSharp.Threshold.QTrigConvex

end
end GKSharp.Proposal14

namespace GKSharp.ComputerChecked.Proposal14

abbrev CheckOmegaNeg := GKSharp.ComputerChecked.CheckOmegaNeg
abbrev CheckOmegaRoot := GKSharp.ComputerChecked.CheckOmegaRoot
abbrev CheckLocalF := GKSharp.ComputerChecked.CheckLocalF
abbrev CheckBoundaryBulk := GKSharp.ComputerChecked.CheckBoundaryBulk
abbrev CheckBoundarySliver := GKSharp.ComputerChecked.CheckBoundarySliver
abbrev CheckLocalGap := GKSharp.ComputerChecked.CheckLocalGap
abbrev CheckCornerDerivatives := GKSharp.ComputerChecked.CheckCornerDerivatives
abbrev CheckCornerTails := GKSharp.ComputerChecked.CheckCornerTails
abbrev CheckStripBulkMiddle := GKSharp.ComputerChecked.CheckStripBulkMiddle
abbrev CheckStripBulkTails := GKSharp.ComputerChecked.CheckStripBulkTails

end GKSharp.ComputerChecked.Proposal14

namespace GKSharp.Proposal14
noncomputable section
open Set Filter GKSharp.ComputerChecked.Proposal14 GKSharp.Threshold
open scoped Topology ContDiff

def ClaimQ (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) : Prop :=
  1 < p → p < 2 → ∀ lam ∈ Ico (-1 : ℝ) 1,
    (pencilNorm P lam = gk p lam ↔
      ∀ t ∈ Icc (-Real.pi) Real.pi,
        kConst p lam * Real.cos (q p * |t|) ≤ obstacle p lam t) ∧
    ((pencilNorm P lam = gk p lam) ↔
      ∀ z : ℂ, 0 ≤ GKSharp.critD p (gk p lam) (kConst p lam) lam z)

def ClaimF (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) : Prop :=
  1 < p → p < 2 → omega p < 0 →
    ∃ eps > 0, ∀ lam : ℝ, 1 - eps < lam → lam < 1 → gk p lam < pencilNorm P lam

def ClaimL (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) : Prop :=
  1 < p → p < 2 → ∀ lam ∈ Ioo (0 : ℝ) 1,
    1 < localTest p lam → gk p lam < pencilNorm P lam

def ClaimEdge (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) : Prop :=
  1 < p → p < pc → h p (lambdaLoc p) < 0 ∧
    IsLeast (axisZeros p) (lambda0 p) ∧ 0 < lambda0 p ∧ lambda0 p < lambdaLoc p ∧
    gk p (lambdaLoc p) < pencilNorm P (lambdaLoc p)

/-- Coverage link (renamed): the approved target `taylor_positive` of slice SliceB, from installed rows. Paper place: sec5f_strip.tex l.52-57 (short v3.70). -/
theorem cover_taylor_positive : ∀ (eta bound value initial e2 c4 tau : ℝ)
    (heta : 0 < eta) (hb : eta ≤ bound) (hi : 0 ≤ initial) (ht : 0 ≤ tau)
    (hc : bound ^ 2 * |c4| ≤ tau)
    (hv : value = initial + e2 * eta ^ 2 + c4 * eta ^ 4)
    (hm : tau < e2 ∨ bound ^ 2 * (max 0 (-e2) + tau) < initial), 0 < value :=
  @GKSharp.Paper.sec5_corner_taylor_inference

def ClaimS (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) : Prop :=
  (p ∈ Icc p0 (317 / 250 : ℝ) → ∀ lam ∈ Ioo (0 : ℝ) 1, 0 < h p lam) ∧
  (p ∈ Ico p0 (3 - Real.sqrt 3) → ∀ lam : ℝ, pencilNorm P lam = gk p lam)

/-- Coverage link (renamed): the approved target `strip_endpoint_compare` of slice SliceB, from installed rows. Paper place: sec5f_strip.tex l.44-45 (short v3.70). -/
theorem cover_strip_endpoint_compare : 3 - Real.sqrt 3 < (317 / 250 : ℝ) :=
  @GKSharp.Paper.sec5_strip_endpoint

/-- Coverage link (stronger): the approved target `obstacle_attained` of slice SliceB, from installed rows. Paper place: sec2_obstacle.tex l.57-60 (short v3.70). -/
theorem cover_obstacle_attained : ∀ (p C lam t : ℝ) (hp : 1 < p) (hC : max 1 |lam| < C),
    ∃ y : ℝ, gamma p C lam y t = obstacleAt p C lam t ∧
      ∀ x : ℝ, obstacleAt p C lam t ≤ gamma p C lam x t :=
  by intro p C lam t hp hC; have hC' : max 1 ‖(lam : ℂ)‖ < C  := (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hC); obtain ⟨Y, hY0, hY⟩ := (GKSharp.Paper.slice_O12 hp C (lam : ℂ) hC').1; obtain ⟨y, hy, hmin, heq⟩ := hY t; refine ⟨y, heq.symm, ?_⟩; intro x; change GKSharp.obstacle p C (lam : ℂ) t ≤ GKSharp.gamma p C (lam : ℂ) x t; rw [heq]; exact hmin x

/-- Coverage link (stronger): the approved target `sec5_cDelta_quadratic` of slice SliceB, from installed rows. Paper place: sec5f_strip.tex:23. -/
theorem cover_sec5_cDelta_quadratic : ∀ (p delta : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hd : delta < 1),
    sn p * cDelta p delta ^ 2 - delta * cDelta p delta - sn p * (1 - delta) = 0 ∧
      0 < cDelta p delta :=
  by intro p delta hp _ hd; exact GKSharp.Paper.sec5_cDelta_quadratic p delta hp hd

end
end GKSharp.Proposal14

end GKSharp.CoverageLinks.SliceB
