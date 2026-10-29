/- scalar algebra for the local threshold and corner Taylor inference.
These generic lemmas do not assume any analytic claim of this paper or computer check.
Copyright (C) Dave Goel 2026--now. -/
import Mathlib

namespace GKSharp

/-- sec4b_failure.tex:79–80. The rational local-test factor strictly increases. -/
theorem local_factor_strictMono : StrictMonoOn (fun lam : ℝ => 4 * lam / (1 + lam) ^ 2) (Set.Ioo 0 1) := by
  intro aa haa bb hbb hab
  have hda : 0 < (1 + aa) ^ 2 := sq_pos_of_pos (by linarith [haa.1])
  have hdb : 0 < (1 + bb) ^ 2 := sq_pos_of_pos (by linarith [hbb.1])
  apply (div_lt_div_iff₀ hda hdb).2
  have habprod : aa * bb < 1 := by nlinarith [mul_pos haa.1 (sub_pos.mpr hbb.2)]
  have hprod := mul_pos (sub_pos.mpr hab) (sub_pos.mpr habprod)
  nlinarith

/-- sec4b_failure.tex:20–21,79. Exact rational solution of the local inequality.
The derivation of the paper's d² from trig data remains separate. -/
theorem local_factor_threshold_iff (lam dd : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1)
    (hdd : 0 < dd) :
    (1 - dd ^ 2 < 4 * lam / (1 + lam) ^ 2 ↔ (1 - dd) / (1 + dd) < lam) := by
  have hdlam : 0 < 1 + lam := by linarith [hlam.1]
  have hddd : 0 < 1 + dd := by linarith
  have hratio : 0 ≤ (1 - lam) / (1 + lam) := div_nonneg (by linarith [hlam.2]) hdlam.le
  have hid : 1 - 4 * lam / (1 + lam) ^ 2 = ((1 - lam) / (1 + lam)) ^ 2 := by
    field_simp
    ring
  have hsquares : (((1 - lam) / (1 + lam)) ^ 2 < dd ^ 2 ↔ (1 - lam) / (1 + lam) < dd) :=
    sq_lt_sq₀ hratio hdd.le
  have hlinear : ((1 - lam) / (1 + lam) < dd ↔ (1 - dd) / (1 + dd) < lam) := by
    rw [div_lt_iff₀ hdlam, div_lt_iff₀ hddd]
    constructor <;> intro hh <;> nlinarith
  constructor
  · intro hh
    apply hlinear.mp
    apply hsquares.mp
    linarith
  · intro hh
    have hh' := hsquares.mpr (hlinear.mpr hh)
    linarith

/-- sec4b_failure.tex:135. The gap formula and its elementary upper bound. -/
theorem local_threshold_gap (dd : ℝ) (hdd : 0 ≤ dd) :
    1 - (1 - dd) / (1 + dd) = 2 * dd / (1 + dd) ∧
    2 * dd / (1 + dd) ≤ 2 * dd := by
  have hden : 0 < 1 + dd := by linarith
  constructor
  · field_simp
    ring
  · apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg dd]

/-- sec5f_strip.tex:51–52. Pure polynomial positivity inference after Taylor's
theorem and the derivative-margin computer check are separately established. -/
theorem corner_taylor_positive (eta bound value initial e2 c4 tau : ℝ)
    (heta : 0 < eta) (hb : eta ≤ bound) (hi : 0 ≤ initial) (ht : 0 ≤ tau)
    (hc : bound ^ 2 * |c4| ≤ tau)
    (hv : value = initial + e2 * eta ^ 2 + c4 * eta ^ 4)
    (hm : tau < e2 ∨ bound ^ 2 * (max 0 (-e2) + tau) < initial) : 0 < value := by
  have hbs : 0 < bound := lt_of_lt_of_le heta hb
  have hes : 0 < eta ^ 2 := sq_pos_of_pos heta
  have hsquare : eta ^ 2 ≤ bound ^ 2 := by nlinarith
  have habs : |c4| * eta ^ 2 ≤ tau := by
    nlinarith [mul_nonneg (abs_nonneg c4) (sub_nonneg.mpr hsquare)]
  have hrem : -tau ≤ c4 * eta ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right (neg_abs_le c4) (sq_nonneg eta)
    nlinarith
  have hrem4 : -tau * eta ^ 2 ≤ c4 * eta ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_right hrem (sq_nonneg eta)
    nlinarith
  rcases hm with hm | hm
  · have hpos := mul_pos (sub_pos.mpr hm) hes
    nlinarith
  · have hmax : -e2 ≤ max 0 (-e2) := le_max_right _ _
    have hnmax : 0 ≤ max 0 (-e2) := le_max_left _ _
    have hweight := mul_nonneg (show 0 ≤ max 0 (-e2) + tau by linarith)
      (sub_nonneg.mpr hsquare)
    have he2 := mul_nonneg (show 0 ≤ e2 + max 0 (-e2) by linarith) (sq_nonneg eta)
    nlinarith

/-- sec5f_strip.tex:67. Exact rational endpoint comparison. -/
theorem strip_upper_endpoint : 3 - Real.sqrt 3 < (317 / 250 : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

end GKSharp


