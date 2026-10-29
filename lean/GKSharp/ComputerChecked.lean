/- GKSharp/ComputerChecked.lean - exact ordinary computer-check Prop hypotheses.
Frozen source: short_v0.40/.
No axioms, proof placeholders or assumed properties.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.ThresholdAnalysis

namespace GKSharp.ComputerChecked
open Set GKSharp.Threshold

/-- COMPUTER-CHECKED, NOT proved in Lean. A:53,V:18. omega_negative.py,
negative_omega.stdout.log. 120-bit external balls; exact rational endpoints. -/
def CheckOmegaNeg : Prop := ∀ p ∈ Icc (1001 / 1000 : ℝ) a0, omega p < 0

/-- COMPUTER-CHECKED, NOT proved in Lean. S:43–44,V:19.
omega_positive.py / positive_omega_root.stdout.log, importing omega_negative.py. -/
def CheckOmegaRoot : Prop :=
  (∀ p ∈ Icc a0 b0, 0 < deriv omega p) ∧
  (∀ p ∈ Icc b0 (317 / 250 : ℝ), 0 < omega p)

/-- COMPUTER-CHECKED, NOT proved in Lean. B:102–103,V:20–21.
local_threshold.py / local_threshold_root.stdout.log. Derivative means actual deriv.
The bracket endpoint signs are proved by localF_bracket_lower/upper, not hypotheses. -/
def CheckLocalF : Prop :=
  (∀ p ∈ Icc (1000001 / 1000000 : ℝ) (6067 / 5000), 0 < localF p) ∧
  (∀ p ∈ Icc (1517 / 1250 : ℝ) (3 / 2), localF p < 0) ∧
  (∀ p ∈ Icc (6067 / 5000 : ℝ) (1517 / 1250), deriv localF p < 0)

/-- COMPUTER-CHECKED, NOT proved in Lean. B:121–123,V:22.
boundary_bulk.py / boundary_bulk_1,2,3.stdout.log. Arithmetic witness only;
the infimum/axis upper bound is a separate internal theorem. -/
def CheckBoundaryBulk : Prop :=
  ∀ p ∈ Icc (1000001 / 1000000 : ℝ) (6067 / 5000),
    ∃ theta ∈ Ioo (0 : ℝ) 1, axisUpper p (lambdaLoc p) theta < 0

/-- COMPUTER-CHECKED, NOT proved in Lean. B:134,V:23.
boundary_sliver.py / boundary_sliver.stdout.log; includes the exact removable value. -/
def CheckBoundarySliver : Prop :=
  ∀ p ∈ Icc (6067 / 5000 : ℝ) (12134904 / 10000000),
    ∀ delta ∈ Icc (0 : ℝ) (3 / 100), g p delta (1371 / 5000) < 0

/-- COMPUTER-CHECKED history: sec4b_failure.tex:135,calculation_certificates.tex:31.
Formerly NOT proved in Lean. NOW KERNEL-PROVED by GKSharp.checkLocalGap_proved in Proofs/LocalGapCertificate.lean;
public mathematical certificate GKSharp.Paper.sec4_local_gap_kernel is audited as PROVED.
boundary_sliver.py / boundary_sliver.stdout.log is historical external evidence; the final public rows discharge this premise. -/
def CheckLocalGap : Prop :=
  ∀ p ∈ Icc (6067 / 5000 : ℝ) (12134904 / 10000000),
    2 * Real.sqrt (max (localD2 p) 0) ≤ 3 / 100

/-- COMPUTER-CHECKED, NOT proved in Lean. S:51–55,V:24.
strip_corner.py / strip_corner.stdout.log. Only compact derivative/margin
enclosures: Taylor, evenness and Omega-minimum facts are NOT assumed here. -/
def CheckCornerDerivatives : Prop :=
  ∀ p ∈ Icc a0 b1, ∀ sigma ∈ Icc (9 / 200 : ℝ) (19 / 20),
    ∃ tau ∈ Icc (0 : ℝ) (191 / 10000),
      (∀ eta ∈ Icc (0 : ℝ) eta1, eta1 ^ 2 * |cFour p eta sigma| ≤ tau) ∧
      (tau < eTwo p sigma ∨
        eta1 ^ 2 * (max 0 (-eTwo p sigma) + tau) < etilde p 0 sigma)

/-- COMPUTER-CHECKED, NOT proved in Lean. S:60,V:35.
strip_corner.py / strip_corner.stdout.log; analytic s-tail reductions are separate. -/
def CheckCornerTails : Prop :=
  ∀ p ∈ Icc a0 b1, ∀ delta ∈ Icc (0 : ℝ) (1 / 20),
    2920 / 10000 < lowTail p delta ∧ 6320 / 1000 < highTail p delta

/-- COMPUTER-CHECKED, NOT proved in Lean. S:62–66,V:25.
strip_bulk.py --corner main / strip_bulk_main.stdout.log; closed s-core. -/
def CheckStripBulkMiddle : Prop :=
  ∀ p delta : ℝ, bulkDomain p delta →
    ∀ s ∈ Icc (1 / 20 : ℝ) (19 / 20), 0 < g p delta s

/-- COMPUTER-CHECKED, NOT proved in Lean. S:62–64,V:25.
strip_bulk.py --corner main / strip_bulk_main.stdout.log; only tail lower expressions. -/
def CheckStripBulkTails : Prop :=
  ∀ p delta : ℝ, bulkDomain p delta → 0 < lowTail p delta ∧ 0 < highTail p delta

end GKSharp.ComputerChecked
