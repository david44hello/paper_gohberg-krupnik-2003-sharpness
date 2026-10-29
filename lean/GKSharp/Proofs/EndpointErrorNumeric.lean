/- exact endpoint remainder arithmetic using finite exponential series.
Frozen source: short_v0.70/endpoint_estimate.tex:65.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential

namespace GKSharp
open Real

theorem endpoint_error_numeric :
    let a : ℝ := 3.2 * 10 ^ (-6 : ℤ)
    sqrt a < 0.001789 ∧ log (8 / sqrt a) < 8.5 ∧ log (1 / a) < 12.66 ∧
      endpointError a < 0.12 := by
  dsimp only
  let a : ℝ := 3.2 * 10 ^ (-6 : ℤ)
  have ha0 : 0 < a := by norm_num [a]
  have hs0 : 0 < sqrt a := sqrt_pos.mpr ha0
  have haeq : a = (1 / 312500 : ℝ) := by norm_num [a]
  have hs2 : sqrt a ^ 2 = (1 / 312500 : ℝ) := (sq_sqrt ha0.le).trans haeq
  have hs : sqrt a < (0.001789 : ℝ) := by nlinarith
  have hexp4 : (54.59 : ℝ) < exp 4 := by
    have hh := sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num) 16
    norm_num [Finset.sum_range_succ, Nat.factorial] at hh
    linarith
  have hexphalf : (1.6 : ℝ) < exp (0.5 : ℝ) := by
    have hh := sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.5 by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at hh
    linarith
  have hexp66 : (1.93 : ℝ) < exp (0.66 : ℝ) := by
    have hh := sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.66 by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at hh
    linarith
  have h85 : (4500 : ℝ) < exp (8.5 : ℝ) := by
    rw [show (8.5 : ℝ) = 4 + 4 + 0.5 by norm_num, exp_add, exp_add]
    have hh : (54.59 : ℝ) * 54.59 * 1.6 < exp 4 * exp 4 * exp (0.5 : ℝ) := by gcongr
    linarith
  have h1266 : (312500 : ℝ) < exp (12.66 : ℝ) := by
    rw [show (12.66 : ℝ) = 4 + 4 + 4 + 0.66 by norm_num, exp_add, exp_add, exp_add]
    have hh : (54.59 : ℝ) * 54.59 * 54.59 * 1.93 < exp 4 * exp 4 * exp 4 * exp (0.66 : ℝ) := by gcongr
    linarith
  have h8 : 8 / sqrt a < (4500 : ℝ) := by
    rw [div_lt_iff₀ hs0]
    have hslow : (8 / 4500 : ℝ) < sqrt a :=
      (lt_sqrt (by norm_num : (0 : ℝ) ≤ 8 / 4500)).mpr (by norm_num [a])
    simpa only [mul_comm] using (div_lt_iff₀ (show (0 : ℝ) < 4500 by norm_num)).mp hslow
  have hlog8 : log (8 / sqrt a) < (8.5 : ℝ) :=
    (log_lt_iff_lt_exp (by positivity)).mpr (h8.trans h85)
  have hlog1 : log (1 / a) < (12.66 : ℝ) := by
    apply (log_lt_iff_lt_exp (by positivity)).mpr
    have hh : 1 / a = (312500 : ℝ) := by norm_num [a]
    rw [hh]
    exact h1266
  refine ⟨hs, hlog8, hlog1, ?_⟩
  change sqrt a * (2 + 16 / 3 * log (8 / sqrt a) + 1.8 + 2 / 3 * log (1 / a) +
    8 + 4 * sqrt a + 4 * a) < 0.12
  have hb : 2 + 16 / 3 * log (8 / sqrt a) + 1.8 + 2 / 3 * log (1 / a) +
      8 + 4 * sqrt a + 4 * a ≤
      2 + 16 / 3 * (8.5 : ℝ) + 1.8 + 2 / 3 * 12.66 + 8 + 4 * 0.001789 + 4 * a := by linarith
  have hm := mul_le_mul_of_nonneg_left hb hs0.le
  have hb0 : 0 < 2 + 16 / 3 * (8.5 : ℝ) + 1.8 + 2 / 3 * 12.66 + 8 + 4 * 0.001789 + 4 * a := by positivity
  have hm' := mul_lt_mul_of_pos_right hs hb0
  have hconst : (0.001789 : ℝ) *
      (2 + 16 / 3 * (8.5 : ℝ) + 1.8 + 2 / 3 * 12.66 + 8 + 4 * 0.001789 + 4 * a) < 0.12 := by norm_num [a]
  exact hm.trans_lt (hm'.trans hconst)

end GKSharp

#print axioms GKSharp.endpoint_error_numeric
