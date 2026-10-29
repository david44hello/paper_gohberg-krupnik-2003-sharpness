/-
GKSharp/Proofs/StripExtras.lean — paper 019 (sec5f_strip.tex l. 19, 59): two strip steps named by the slice (b)
statement review (S2(a), S2(b)), with the reviewer's proposed types.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
- cDelta_quadratic (l.19): for every δ < 1 (both signs), `C(δ)` is a positive root of `s₀C² - δC - s₀(1-δ) = 0`
  (it is the unique positive root: GKSharp.Strip.cDelta_unique).
- powSlope_exprel (l.59, fifth E-identity): `(x^p - 1)/(x - 1) = p E(-pL)/E(-L)` with `L = log x`, for every `x > 0`
  and every real `p` (removable values at `x = 1` and `p = 0` included).
-/
import GKSharp.Proofs.StripInvolution

namespace GKSharp

open Set GKSharp.Threshold

/-- sec5f l.19 (review S2(a)): `C(δ)` solves the quadratic for every `δ < 1`, and is positive. -/
theorem cDelta_quadratic_proved (p delta : ℝ) (hp : 1 < p) (hd : delta < 1) :
    sn p * cDelta p delta ^ 2 - delta * cDelta p delta - sn p * (1 - delta) = 0 ∧ 0 < cDelta p delta :=
  ⟨(Strip.cDelta_props hp hd).2, (Strip.cDelta_props hp hd).1⟩

/-- sec5f l.59 (review S2(b)): `powSlope p x = p E(-p log x)/E(-log x)` for `x > 0`. -/
theorem powSlope_exprel_proved (p x : ℝ) (hx : 0 < x) :
    powSlope p x = p * exprel (-p * Real.log x) / exprel (-Real.log x) := by
  by_cases h1 : x = 1
  · subst h1
    simp [powSlope, exprel]
  have hL : Real.log x ≠ 0 := fun h => h1 (Real.eq_one_of_pos_of_log_eq_zero hx h)
  by_cases hp0 : p = 0
  · subst hp0
    simp [powSlope, h1]
  have hpL : -p * Real.log x ≠ 0 := mul_ne_zero (neg_ne_zero.2 hp0) hL
  have hL' : -Real.log x ≠ 0 := neg_ne_zero.2 hL
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.2 h1
  have hx1' : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have hxp : Real.exp (p * Real.log x) = x ^ p := by rw [Real.rpow_def_of_pos hx, mul_comm]
  unfold powSlope exprel
  rw [ite_eq_right h1, ite_eq_right hpL, ite_eq_right hL', show -(-p * Real.log x) = p * Real.log x by ring,
    neg_neg, hxp, Real.exp_log hx]
  field_simp
  ring

end GKSharp
