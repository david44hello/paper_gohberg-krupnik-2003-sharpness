/- monotonicity of the analytic endpoint remainder.
Frozen source: short_v0.70/endpoint_estimate.tex:64.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential

namespace GKSharp
open Real Set

theorem sqrt_mul_log_strictMono :
    StrictMonoOn (fun a : ℝ => sqrt a * log (1 / a)) (Ioo 0 (exp (-2))) := by
  have hderiv (a : ℝ) (ha : 0 < a) :
      HasDerivAt (fun x : ℝ => sqrt x * log (1 / x))
        ((-log a - 2) / (2 * sqrt a)) a := by
    have hh := (hasDerivAt_sqrt ha.ne').mul (hasDerivAt_log ha.ne').neg
    have heq : (1 / (2 * sqrt a)) * -log a + sqrt a * -(1 / a) =
        (-log a - 2) / (2 * sqrt a) := by
      have hs := sq_sqrt ha.le
      have hs0 : sqrt a ≠ 0 := (sqrt_pos.mpr ha).ne'
      field_simp
      nlinarith
    have hh' : HasDerivAt (fun x : ℝ => sqrt x * -log x) ((-log a - 2) / (2 * sqrt a)) a := by
      apply hh.congr_deriv
      simpa only [Pi.neg_apply, one_div] using heq
    simpa only [one_div, log_inv] using hh'
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro a ha
    exact (hderiv a ha.1).continuousAt.continuousWithinAt
  · intro a ha
    have ha' : a ∈ Ioo 0 (exp (-2)) := interior_subset ha
    rw [(hderiv a ha'.1).deriv]
    have hl := log_lt_log ha'.1 ha'.2
    rw [log_exp] at hl
    exact div_pos (by linarith) (mul_pos (by norm_num) (sqrt_pos.mpr ha'.1))

theorem endpoint_error_monotone :
    MonotoneOn endpointError (Ioc 0 (3.2 * 10 ^ (-6 : ℤ))) := by
  have hsmall : (3.2 * 10 ^ (-6 : ℤ) : ℝ) < exp (-2) := by
    have hh := exp_bound_div_one_sub_of_interval (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)
    norm_num at hh
    have htwo : exp (2 : ℝ) ≤ 16 := by
      rw [show (2 : ℝ) = 1 / 2 + 1 / 2 + 1 / 2 + 1 / 2 by ring, exp_add, exp_add, exp_add]
      calc
        exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) ≤ (2 : ℝ) * 2 * 2 * 2 := by gcongr
        _ = 16 := by norm_num
    rw [exp_neg]
    apply lt_of_lt_of_le (show (3.2 * 10 ^ (-6 : ℤ) : ℝ) < 1 / 16 by norm_num)
    simpa only [one_div] using one_div_le_one_div_of_le (exp_pos 2) htwo
  have hform (a : ℝ) (ha : 0 < a) : endpointError a =
      ((59 / 5 : ℝ) + 16 / 3 * log 8) * sqrt a +
      (10 / 3 : ℝ) * (sqrt a * log (1 / a)) + 4 * a + 4 * a * sqrt a := by
    unfold endpointError
    rw [log_div (by norm_num : (8 : ℝ) ≠ 0) (sqrt_pos.mpr ha).ne', log_sqrt ha.le,
      one_div, log_inv]
    have hs := sq_sqrt ha.le
    nlinarith
  intro a ha b hb hab
  have hs : sqrt a ≤ sqrt b := sqrt_le_sqrt hab
  have hf : sqrt a * log (1 / a) ≤ sqrt b * log (1 / b) :=
    sqrt_mul_log_strictMono.monotoneOn ⟨ha.1, ha.2.trans_lt hsmall⟩ ⟨hb.1, hb.2.trans_lt hsmall⟩ hab
  have hprod : a * sqrt a ≤ b * sqrt b := mul_le_mul hab hs (sqrt_nonneg _) hb.1.le
  have hc : 0 ≤ (59 / 5 : ℝ) + 16 / 3 * log 8 := by have := log_nonneg (show (1 : ℝ) ≤ 8 by norm_num); positivity
  rw [hform a ha.1, hform b hb.1]
  have hmul := mul_le_mul_of_nonneg_left hs hc
  linarith

end GKSharp

#print axioms GKSharp.sqrt_mul_log_strictMono
#print axioms GKSharp.endpoint_error_monotone
