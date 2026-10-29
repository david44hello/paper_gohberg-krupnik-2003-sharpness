/- GKSharp/Defs/Threshold.lean - scalar thresholds, with no assumed properties.
Frozen source: short_v0.40/.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.RealLine

namespace GKSharp.Threshold
noncomputable section
open Set

def q (p : ℝ) : ℝ := p / 2
def sn (p : ℝ) : ℝ := Real.sin (Real.pi / p)
def cs (p : ℝ) : ℝ := -Real.cos (Real.pi / p)
def dual (p : ℝ) : ℝ := p / (p - 1)
def aConst (p : ℝ) : ℝ := (1 - sn p) / (2 * sn p)
def bConst (p : ℝ) : ℝ := 1 - q p + 2 * q p * aConst p

/-- sec4a_criterion.tex:38. Stable positive quadratic root; range proved separately. -/
def sStar (p : ℝ) : ℝ :=
  2 * q p * aConst p /
    (bConst p + Real.sqrt (bConst p ^ 2 + 4 * (2 * q p - 1) * q p * aConst p))

def sQuad (p s : ℝ) : ℝ :=
  (2 * q p - 1) * s ^ 2 + bConst p * s - q p * aConst p

def omegaFirst (p s : ℝ) : ℝ := p * (aConst p + s) / (s * (1 - s)) ^ q p
def kappaZero (p : ℝ) : ℝ := 2 ^ q p * sn p ^ (p - 2) * cs p ^ (1 - q p)

/-- sec4a_criterion.tex:39. Exact Omega; no root/sign facts assumed. -/
def omega (p : ℝ) : ℝ := omegaFirst p (sStar p) - kappaZero p
def omegaZeros : Set ℝ := {p | 1 < p ∧ p < 2 ∧ omega p = 0}
/-- sec4a_criterion.tex:41; sec5f_strip.tex:44. IsLeast and existence are theorem targets. -/
def p0 : ℝ := sInf omegaZeros

/-- sec4b_failure.tex:94. -/
def localF (p : ℝ) : ℝ := p * dual p - 4 * (1 + Real.cos (Real.pi / p) ^ 2)
def localZeros : Set ℝ := {p | 1 < p ∧ p < 2 ∧ localF p = 0}
def pc : ℝ := sInf localZeros
def localD2 (p : ℝ) : ℝ :=
  sn p ^ 2 * (p * dual p / 4 - 1 - cs p ^ 2) / cs p ^ 4

/-- sec4b_failure.tex:20–21; P019_paper.tex:139. On 1<p<2.
The F<=0 branch is the paper's clamping at1; prove equivalence to p>=pc separately. -/
def lambdaLoc (p : ℝ) : ℝ :=
  if 0 < localF p then
    (1 - Real.sqrt (localD2 p)) / (1 + Real.sqrt (localD2 p)) else 1

def localTest (p lam : ℝ) : ℝ :=
  p * dual p / 4 * sn p ^ 2 + 4 * lam * cs p ^ 4 / (1 + lam) ^ 2

end
end GKSharp.Threshold
