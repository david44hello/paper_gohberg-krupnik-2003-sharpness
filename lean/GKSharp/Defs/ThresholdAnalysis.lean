/- GKSharp/Defs/ThresholdAnalysis.lean - criterion/contact/strip objects.
Paper places: short_v3.90/.
No axioms, proof placeholders or assumed properties.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Threshold
import GKSharp.Defs.Potential

namespace GKSharp.Threshold
noncomputable section
open Set Filter
open scoped Topology

def zeta (y t : ℝ) : ℂ := Complex.exp ((y : ℂ) + Complex.I * (t : ℂ))
def bigG (p C lam : ℝ) (z : ℂ) : ℝ := GKSharp.obstacleG p C (lam : ℂ) z
/-- Specialize the canonical shared Gamma to a real ratio. -/
def gamma (p C lam y t : ℝ) : ℝ := GKSharp.gamma p C (lam : ℂ) y t
/-- Specialize the canonical shared obstacle; no second infimum definition. -/
def obstacleAt (p C lam t : ℝ) : ℝ := GKSharp.obstacle p C (lam : ℂ) t
def obstacle (p lam t : ℝ) : ℝ := GKSharp.obstacle p (gk p lam) (lam : ℂ) t
/-- Canonical h from the corrected shared Potential definition. -/
def h (p lam : ℝ) : ℝ := GKSharp.axisGap p lam

/-- sec4b_failure.tex:119. First zero is not assumed by defining sInf. -/
def axisZeros (p : ℝ) : Set ℝ := {lam | 0 < lam ∧ lam < lambdaLoc p ∧ h p lam = 0}
def lambda0 (p : ℝ) : ℝ := sInf (axisZeros p)

/-- sec5f_strip.tex:23. This is the continued positive quadratic root, NOT gk
for negative delta. This distinction is essential in the involution. -/
def cDelta (p delta : ℝ) : ℝ :=
  delta / (2 * sn p) + Real.sqrt (delta ^ 2 / (4 * sn p ^ 2) + 1 - delta)

def powSlope (p x : ℝ) : ℝ := if x = 1 then p else (x ^ p - 1) / (x - 1)
def phi (p x : ℝ) : ℝ := powSlope p (1 - x)
def tOne (p delta : ℝ) : ℝ :=
  powSlope p (cDelta p delta) * (cDelta p delta - sn p) / (sn p * (cDelta p delta + 1))
def kap (p delta : ℝ) : ℝ :=
  2 * cDelta p delta * sn p ^ (p - 2) * cs p ^ (1 - q p) *
    (cDelta p delta ^ 2 + 1 - delta) ^ (q p - 1)

/-- sec4b_failure.tex:136–137 and sec5f_strip.tex:21–24. Exact removable extension. -/
def g (p delta s : ℝ) : ℝ :=
  (tOne p delta + s * phi p (s * delta)) / (s * (1 - s)) ^ q p - kap p delta

def axisUpper (p lam theta : ℝ) : ℝ :=
  (gk p lam ^ p - (lam + theta * (1 - lam)) ^ p) / (theta * (1 - theta)) ^ q p - kConst p lam

def exprel (x : ℝ) : ℝ := if x = 0 then 1 else (1 - Real.exp (-x)) / x
def eta1 : ℝ := -Real.log (19 / 20)
def sEta (eta sigma : ℝ) : ℝ := sigma * exprel (sigma * eta) / exprel eta
def deltaEta (eta : ℝ) : ℝ := 1 - Real.exp (-eta)
def vWeight (p eta : ℝ) : ℝ :=
  Real.exp ((1 - q p) * eta / 2) * cDelta p (deltaEta eta) ^ (p / 2)
def etilde (p eta sigma : ℝ) : ℝ := g p (deltaEta eta) (sEta eta sigma) / vWeight p eta
def eTwo (p sigma : ℝ) : ℝ := deriv (deriv (fun eta => etilde p eta sigma)) 0 / 2
def cFour (p eta sigma : ℝ) : ℝ :=
  deriv (deriv (deriv (deriv (fun x => etilde p x sigma)))) eta / 24
def lowTail (p delta : ℝ) : ℝ := tOne p delta / (1 / 20 : ℝ) ^ q p - kap p delta
def highTail (p delta : ℝ) : ℝ := (tOne p delta + 19 / 20) / (1 / 20 : ℝ) ^ q p - kap p delta
def a0 : ℝ := 12336025 / 10000000
def b0 : ℝ := 12336027 / 10000000
def b1 : ℝ := 12341027 / 10000000
def bulkDomain (p delta : ℝ) : Prop :=
  (p ∈ Icc a0 (317 / 250) ∧ delta ∈ Icc (1 / 20) 1) ∨
  (p ∈ Icc b1 (317 / 250) ∧ delta ∈ Icc 0 (1 / 20))

def theta (p : ℝ) : ℝ := Real.pi / p
def sigmaContact (p lam : ℝ) : ℝ := (1 + lam) / cs p
def rContact (p lam : ℝ) : ℝ :=
  (sigmaContact p lam + Real.sqrt (sigmaContact p lam ^ 2 - 4 * lam)) / 2
def yContact (p lam : ℝ) : ℝ := Real.log (rContact p lam)
def vContact (p lam : ℝ) : ℝ := rContact p lam - lam / rContact p lam
def dOne (p lam : ℝ) : ℝ :=
  1 - 2 * (lam / rContact p lam) * cs p + (lam / rContact p lam) ^ 2
def mobContact (lam : ℝ) (z : ℂ) : ℂ := (z + (lam : ℂ)) / (z + 1)
def chi (lam y t : ℝ) : ℝ := Real.log ‖zeta y t + (lam : ℂ)‖
def logGap (p lam y t : ℝ) : ℝ := Real.log (gk p lam) - Real.log ‖mobContact lam (zeta y t)‖
def weightP (p lam y t : ℝ) : ℝ := Real.exp (p * chi lam y t)
def dy (f : ℝ → ℝ → ℝ) (y t : ℝ) : ℝ := deriv (fun x => f x t) y
def dt (f : ℝ → ℝ → ℝ) (y t : ℝ) : ℝ := deriv (fun x => f y x) t
def dyy (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := dy (dy f)
def dtt (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := dt (dt f)
def dty (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := dt (dy f)
def gammaGK (p lam : ℝ) : ℝ → ℝ → ℝ := gamma p (gk p lam) lam
/-- Schur complement at the contact. Equality to a true envelope second
derivative requires the branch-existence theorem below. -/
def muSecond (p lam : ℝ) : ℝ :=
  dtt (gammaGK p lam) (yContact p lam) (theta p) -
    dty (gammaGK p lam) (yContact p lam) (theta p) ^ 2 /
      dyy (gammaGK p lam) (yContact p lam) (theta p)
def bZero (p lam : ℝ) : ℝ :=
  (1 - lam) * (1 + lam) ^ 2 / (cs p ^ 3 * sn p ^ 2 * vContact p lam ^ 3)
def signBracket (p lam : ℝ) : ℝ :=
  (p - 1) * (1 - 4 * lam * cs p ^ 4 / (1 + lam) ^ 2) - p ^ 2 * sn p ^ 2 / 4

/-- Elementary angular convexity interface for the HKV source statements.
It is not silently identified with subharmonicity; that bridge is separate. -/
def TrigConvexOn (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, ∀ t ∈ I, x < t → t < y → y - x < Real.pi →
    f t ≤ (f x * Real.sin (y - t) + f y * Real.sin (t - x)) / Real.sin (y - x)
def QTrigConvex (qq : ℝ) (f : ℝ → ℝ) : Prop :=
  TrigConvexOn (fun x => f (x / qq)) univ

end
end GKSharp.Threshold
