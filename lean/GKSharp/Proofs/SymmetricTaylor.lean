/- GKSharp/Proofs/SymmetricTaylor.lean — symmetric fourth-order remainder.
Frozen source: short_v0.40/sec4b_failure.tex:36.
Copyright (C) Dave Goel 2026--now. -/
import Mathlib

namespace GKSharp
open Set Filter
open scoped Topology

/-- B:36. A genuine uniform fourth-order bound from local C4 regularity. -/
theorem symmetric_taylor_four_proved (mu : ℝ → ℝ) (tt : ℝ)
    (hmu : ContDiffAt ℝ 4 mu tt) (hz : mu tt = 0) :
    ∃ bound > 0, ∃ eps > 0, ∀ s ∈ Ioo (-eps) eps,
      |mu (tt - s) + mu (tt + s) - deriv (deriv mu) tt * s ^ 2| ≤ bound * s ^ 4 := by
  obtain ⟨U, hU, hC⟩ := hmu.contDiffOn le_rfl (by simp)
  obtain ⟨rr, hrr, hball⟩ := Metric.mem_nhds_iff.mp hU
  let S : Set ℝ := Metric.ball tt rr
  have hmem : tt ∈ S := by simpa [S] using hrr
  have hCS : ContDiffOn ℝ 4 mu S := hC.mono hball
  have hTaylor := taylor_isLittleO (convex_ball tt rr) hmem hCS
  have hB := hTaylor.bound (show (0 : ℝ) < 1 by norm_num)
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds tt hrr)] at hB
  obtain ⟨eps, heps, hB⟩ := Metric.eventually_nhds_iff.mp hB
  have htwo : iteratedDerivWithin 2 mu S tt = deriv (deriv mu) tt := by
    rw [iteratedDerivWithin_eq_iteratedDeriv Metric.isOpen_ball.uniqueDiffOn
      (hmu.of_le (by norm_num)) hmem, iteratedDeriv_eq_iterate]
    rfl
  let coeff : ℝ := iteratedDerivWithin 4 mu S tt / 12
  have hpoly (s : ℝ) :
      taylorWithinEval mu 4 S tt (tt - s) + taylorWithinEval mu 4 S tt (tt + s) -
        deriv (deriv mu) tt * s ^ 2 = coeff * s ^ 4 := by
    dsimp [coeff]
    norm_num [taylor_within_apply, Finset.sum_range_succ, Nat.factorial, hz, htwo]
    <;> ring
  refine ⟨2 + |coeff|, by positivity, eps, heps, ?_⟩
  intro s hs
  have habs : |s| < eps := abs_lt.mpr hs
  have hm := hB (y := tt - s) (by
    simpa [Real.dist_eq, show tt - s - tt = -s by ring] using habs)
  have hp := hB (y := tt + s) (by
    simpa [Real.dist_eq, show tt + s - tt = s by ring] using habs)
  simp only [Real.norm_eq_abs, one_mul] at hm hp
  have hpow : |s ^ 4| = s ^ 4 := abs_of_nonneg (by positivity)
  rw [show (tt - s - tt) ^ 4 = s ^ 4 by ring, hpow] at hm
  rw [show (tt + s - tt) ^ 4 = s ^ 4 by ring, hpow] at hp
  calc
    |mu (tt - s) + mu (tt + s) - deriv (deriv mu) tt * s ^ 2| =
        |(mu (tt - s) - taylorWithinEval mu 4 S tt (tt - s)) +
          (mu (tt + s) - taylorWithinEval mu 4 S tt (tt + s)) + coeff * s ^ 4| := by
      congr 1
      linarith [hpoly s]
    _ ≤ |mu (tt - s) - taylorWithinEval mu 4 S tt (tt - s)| +
          |mu (tt + s) - taylorWithinEval mu 4 S tt (tt + s)| + |coeff| * s ^ 4 := by
      calc
        _ ≤ |mu (tt - s) - taylorWithinEval mu 4 S tt (tt - s)| +
            |mu (tt + s) - taylorWithinEval mu 4 S tt (tt + s)| + |coeff * s ^ 4| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ = _ := by rw [abs_mul, hpow]
    _ ≤ (2 + |coeff|) * s ^ 4 := by linarith

end GKSharp

#print axioms GKSharp.symmetric_taylor_four_proved
