/- GKSharp/Proofs/Sec4bLocal.lean - slice (b): the local threshold and the local test (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v0.80, each as `<row>_proved` with the row's exact type.
- local_threshold_iff (B:20-21, 79-80): with `u = (1-λ)/(1+λ)`, `4λ/(1+λ)² = 1 - u²`, so
  `localTest = J + cs⁴(1 - u²)` and `1 < localTest ↔ u² < localD2` (`J + cs⁴ - 1 = sn²(pp'/4 - 1 - cs²)`);
  `localD2 > 0 ↔ localF > 0`; then `u < √localD2 ↔ λ > (1 - √localD2)/(1 + √localD2)`.
- local_witness_iff (B:94, 98-99): a witness exists iff `λ_loc < 1` iff `localF > 0`.
- localF_stable (B:99): `p²/(p-1) - 4 = (p-2)²/(p-1)` and `cos(π/p) = sin(π/2 - π/p)`.
- localF_endpoint_one (B:100): `(p-2)²/(p-1) = (p-1) - 2 + 1/(p-1)`, `sin² ≤ 1`.
- localF_endpoint_two (B:100-101): `x = π(2-p)/(2p) ∈ (0, π/6]`, `sin x ≥ x - x³/6 ≥ x(1 - π²/216)`, `1/(p-1) ≤ 2`,
  `π²/p² ≥ π²/4`; `(π²/4)(1 - π²/216)² > 2` from `π² ∈ (9, 16]`.
-/
import GKSharp.Proofs.Sec4aBasic

namespace GKSharp

open Set GKSharp.Threshold

/-- `cs p = -cos(π/p) > 0` for `1 < p < 2`. -/
lemma sec4b_cs_pos {p : ℝ} (hp : 1 < p) (hp2 : p < 2) : 0 < cs p := by
  have hp0 : 0 < p := by linarith
  have h1 : Real.pi / 2 < Real.pi / p := div_lt_div_of_pos_left Real.pi_pos hp0 hp2
  have h2 : Real.pi / p < Real.pi + Real.pi / 2 := by
    have := div_lt_self Real.pi_pos hp
    linarith [Real.pi_pos]
  unfold cs
  linarith [Real.cos_neg_of_pi_div_two_lt_of_lt h1 h2]

/-- `localD2 = sn² (localF/4) / cs⁴`. -/
lemma sec4b_localD2_eq (p : ℝ) : localD2 p = sn p ^ 2 * (localF p / 4) / cs p ^ 4 := by
  unfold localD2 localF cs
  ring

/-- B:20-21, 79-80, row `local_threshold_iff`. -/
theorem local_threshold_iff_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (0 : ℝ) 1) :
    (1 < localTest p lam ↔ lambdaLoc p < lam) := by
  obtain ⟨hl0, hl1⟩ := hlam
  have hc := sec4b_cs_pos hp hp2
  have hc4 : 0 < cs p ^ 4 := by positivity
  have hsn := sec4a_sn_pos hp
  have hsc : sn p ^ 2 + cs p ^ 2 = 1 := by
    unfold sn cs
    rw [neg_sq]
    exact Real.sin_sq_add_cos_sq _
  have hl1' : 0 < 1 + lam := by linarith
  have hu0 : 0 ≤ (1 - lam) / (1 + lam) := div_nonneg (by linarith) hl1'.le
  have h4 : 4 * lam / (1 + lam) ^ 2 = 1 - ((1 - lam) / (1 + lam)) ^ 2 := by
    field_simp
    ring
  -- `1 < localTest ↔ u² < localD2`
  have hkey : 1 < localTest p lam ↔ ((1 - lam) / (1 + lam)) ^ 2 < localD2 p := by
    have ht : localTest p lam = p * dual p / 4 * sn p ^ 2 + cs p ^ 4 * (1 - ((1 - lam) / (1 + lam)) ^ 2) := by
      unfold localTest
      rw [← h4]
      ring
    have hD : localD2 p = (p * dual p / 4 * sn p ^ 2 + cs p ^ 4 - 1) / cs p ^ 4 := by
      unfold localD2
      congr 1
      have : sn p ^ 2 = 1 - cs p ^ 2 := by linarith
      rw [this]
      ring
    rw [ht, hD, lt_div_iff₀ hc4]
    constructor <;> intro h <;> linarith
  rw [hkey]
  by_cases hF : 0 < localF p
  · have hDpos : 0 < localD2 p := by
      rw [sec4b_localD2_eq]
      positivity
    have hk0 : 0 < Real.sqrt (localD2 p) := Real.sqrt_pos.2 hDpos
    have hlam : lambdaLoc p = (1 - Real.sqrt (localD2 p)) / (1 + Real.sqrt (localD2 p)) := by
      unfold lambdaLoc
      rw [ite_eq_left hF]
    rw [hlam, ← Real.lt_sqrt hu0, div_lt_iff₀ hl1', div_lt_iff₀ (by linarith)]
    constructor <;> intro h <;> linarith
  · have hlam : lambdaLoc p = 1 := by
      unfold lambdaLoc
      rw [ite_eq_right hF]
    have hD0 : localD2 p ≤ 0 := by
      rw [sec4b_localD2_eq]
      push Not at hF
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
        (by positivity)
    rw [hlam]
    constructor
    · intro h
      nlinarith [sq_nonneg ((1 - lam) / (1 + lam))]
    · intro h
      linarith

/-- B:94, 98-99, row `local_witness_iff`. -/
theorem local_witness_iff_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    (∃ lam ∈ Ioo (0 : ℝ) 1, 1 < localTest p lam) ↔ 0 < localF p := by
  constructor
  · rintro ⟨lam, hlam, h⟩
    rw [local_threshold_iff_proved p lam hp hp2 hlam] at h
    by_contra hF
    have : lambdaLoc p = 1 := by
      unfold lambdaLoc
      rw [ite_eq_right hF]
    linarith [hlam.2]
  · intro hF
    have hk0 : 0 < Real.sqrt (localD2 p) := by
      apply Real.sqrt_pos.2
      rw [sec4b_localD2_eq]
      have := sec4a_sn_pos hp
      have := sec4b_cs_pos hp hp2
      positivity
    have hlt : lambdaLoc p < 1 := by
      unfold lambdaLoc
      rw [ite_eq_left hF, div_lt_one (by linarith)]
      linarith
    have hm1 : max (lambdaLoc p) 0 < 1 := max_lt hlt one_pos
    have hm0 : 0 ≤ max (lambdaLoc p) 0 := le_max_right _ _
    refine ⟨(max (lambdaLoc p) 0 + 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [local_threshold_iff_proved p _ hp hp2 ⟨by linarith, by linarith⟩]
    linarith [le_max_left (lambdaLoc p) 0]

/-- B:99, row `localF_stable`. -/
theorem localF_stable_proved (p : ℝ) (hp : 1 < p) :
    localF p = (p - 2) ^ 2 / (p - 1) -
      4 * Real.sin (Real.pi * (p - 2) / (2 * p)) ^ 2 := by
  have hp0 : p ≠ 0 := by positivity
  have hp1 : p - 1 ≠ 0 := sub_ne_zero.2 (ne_of_gt hp)
  have hang : Real.pi * (p - 2) / (2 * p) = Real.pi / 2 - Real.pi / p := by
    field_simp
  rw [hang, Real.sin_pi_div_two_sub]
  unfold localF dual
  field_simp
  ring

/-- B:100, row `localF_endpoint_one`. -/
theorem localF_endpoint_one_proved (p : ℝ) (hp : 1 < p) (hhi : p ≤ 1000001 / 1000000) :
    1 / (p - 1) - 8 ≤ localF p ∧ 0 < localF p := by
  have he : 0 < p - 1 := by linarith
  have hs := Real.sin_sq_le_one (Real.pi * (p - 2) / (2 * p))
  have hst := localF_stable_proved p hp
  have h1 : (p - 2) ^ 2 / (p - 1) = (p - 1) - 2 + 1 / (p - 1) := by
    field_simp
    ring
  have hbig : 1000000 ≤ 1 / (p - 1) := by
    rw [le_div_iff₀ he]
    linarith
  rw [hst, h1]
  constructor <;> linarith

/-- B:100-101, row `localF_endpoint_two`. -/
theorem localF_endpoint_two_proved (p : ℝ) (hp : 3 / 2 ≤ p) (hp2 : p < 2) :
    localF p / (2 - p) ^ 2 ≤
      2 - (Real.pi ^ 2 / 4) * (1 - Real.pi ^ 2 / 216) ^ 2 ∧ localF p < 0 := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have he : 0 < 2 - p := by linarith
  have hE : 0 < (2 - p) ^ 2 := by positivity
  have hpi0 := Real.pi_pos
  have ht9 : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have ht16 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four]
  set x := Real.pi * (2 - p) / (2 * p) with hx
  have hx0 : 0 < x := div_pos (mul_pos hpi0 he) (by linarith)
  have hxle : x ≤ Real.pi / 6 := by
    rw [hx, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith [mul_nonneg hpi0.le (show 0 ≤ 8 * p - 12 by linarith)]
  set m := 1 - Real.pi ^ 2 / 216 with hm
  have hm0 : 0 < m := by
    rw [hm]
    linarith
  have hx2 : x ^ 2 ≤ Real.pi ^ 2 / 36 := by
    have := mul_le_mul hxle hxle hx0.le (by positivity)
    linarith
  have hsin : x * m ≤ Real.sin x := by
    have h1 := Real.sin_ge_sub_cube hx0.le
    rw [hm]
    linarith [mul_nonneg hx0.le (sub_nonneg.2 hx2)]
  have hsq : (x * m) ^ 2 ≤ Real.sin x ^ 2 := by
    have := mul_self_le_mul_self (mul_pos hx0 hm0).le hsin
    linarith
  have hst := localF_stable_proved p hp1
  have hneg : Real.pi * (p - 2) / (2 * p) = -x := by
    rw [hx]
    ring
  rw [hneg, Real.sin_neg, neg_sq] at hst
  have h1 : (p - 2) ^ 2 / (p - 1) ≤ 2 * (2 - p) ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith [mul_nonneg hE.le (show 0 ≤ 2 * p - 3 by linarith)]
  have h2 : 4 * (x * m) ^ 2 = (2 - p) ^ 2 * (Real.pi ^ 2 / p ^ 2) * m ^ 2 := by
    rw [hx]
    ring
  have h3 : (2 - p) ^ 2 * (Real.pi ^ 2 / 4) * m ^ 2 ≤ (2 - p) ^ 2 * (Real.pi ^ 2 / p ^ 2) * m ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg m)
    apply mul_le_mul_of_nonneg_left _ hE.le
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  have hF : localF p ≤ (2 - p) ^ 2 * (2 - Real.pi ^ 2 / 4 * m ^ 2) := by
    rw [hst]
    linarith
  have hneg2 : 2 - Real.pi ^ 2 / 4 * m ^ 2 < 0 := by
    rw [hm]
    have hq : 0 ≤ (Real.pi ^ 2 - 9) * (Real.pi ^ 2 * Real.pi ^ 2 - 423 * Real.pi ^ 2 + 42849) :=
      mul_nonneg (by linarith) (by linarith [sq_nonneg (Real.pi ^ 2)])
    linarith
  have hprod := mul_neg_of_pos_of_neg hE hneg2
  refine ⟨?_, by linarith⟩
  rw [div_le_iff₀ hE]
  linarith

end GKSharp
