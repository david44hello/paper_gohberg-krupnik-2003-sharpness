/- complete analytic endpoint estimate for Proposition edge.
Frozen source: short_v0.70/endpoint_estimate.tex:59–65.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.EndpointTerms
import GKSharp.Proofs.EndpointKLower
import GKSharp.Proofs.EndpointErrorNumeric
import GKSharp.Proofs.EndpointErrorMonotone

namespace GKSharp
open Real

theorem endpoint_remainder_bound {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    axisGap p (endpointLambda p) ≤ -2 + endpointError (endpointA p) := by
  let a := endpointA p
  let lam := endpointLambda p
  let Q := (1 - lam) / sin a
  let C := gk p (lam : ℂ)
  let d := endpointD p
  let L := log (8 / sqrt a)
  let B := a / 6 * log (1 / a) + a ^ 2 + a * sqrt a + 2 * a
  have ha0 : 0 < a := (endpoint_a_range hp hp1).1
  have ha1 : a < 1 := by
    have hh := (endpoint_a_range hp hp1).2.1
    norm_num at hh
    dsimp only [a]
    linarith
  have hs0 : 0 < sqrt a := sqrt_pos.mpr ha0
  have hs2 : sqrt a ^ 2 = a := sq_sqrt ha0.le
  have hs3 : sqrt a ^ 3 = a * sqrt a := by rw [pow_succ, hs2]
  have hl := (endpoint_d_basic hp hp1).2.2.2.2
  have hsin : 0 < sin a := sin_pos_of_pos_of_lt_pi ha0 (by linarith [pi_gt_three])
  have hQ0 : 0 < Q := div_pos (by dsimp only [lam]; linarith [hl.2]) hsin
  have hscale := endpoint_scale_bounds hp hp1
  dsimp only at hscale
  have hpow : a ^ (-(1 / 2 : ℝ)) = 1 / sqrt a := by rw [rpow_neg ha0.le, ← sqrt_eq_rpow, one_div]
  have hQlo : 1 / sqrt a ≤ Q := by
    have hh := hscale.2.2.1
    change a ^ (-(1 / 2 : ℝ)) ≤ Q at hh
    rwa [hpow] at hh
  have hQup : Q ≤ 2 / sqrt a := by
    have hh := hscale.2.2.2.1
    change Q ≤ 2 * a ^ (-(1 / 2 : ℝ)) at hh
    rw [hpow] at hh
    simpa only [mul_one_div] using hh
  have hInv : 1 / Q ≤ sqrt a := by
    apply (div_le_iff₀ hQ0).mpr
    have hh := (div_le_iff₀ hs0).mp hQlo
    nlinarith
  have hInv2 : 2 / Q ≤ 2 * sqrt a := by
    convert mul_le_mul_of_nonneg_left hInv (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;> ring
  have hd : 2 * d ≤ (1.8 : ℝ) * sqrt a := hscale.2.2.2.2
  have hB0 : 0 ≤ B := by
    have hh := log_nonneg ((le_div_iff₀ ha0).mpr (by linarith : 1 * a ≤ 1))
    dsimp only [B]
    positivity
  have hL0 : 0 ≤ L := by
    apply log_nonneg
    rw [le_div_iff₀ hs0]
    have hh : sqrt a < 1 := by nlinarith [sqrt_nonneg a]
    linarith
  have hterms := endpoint_term_bounds hp hp1
  have hmid := endpoint_midpoint_bound hp hp1
  have hK := (endpoint_k_lower_bounds hp hp1).2
  have hE := (endpoint_k_error_bounds hp hp1).1
  have hthree : a ^ (3 / 2 : ℝ) = a * sqrt a := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add ha0, rpow_one, ← sqrt_eq_rpow]
  rw [hthree] at hE
  have hKb : 2 * Q * (1 - B) ≤ kConst p lam := by
    have hh := mul_le_mul_of_nonneg_left (sub_le_sub_left hE 1) (show 0 ≤ 2 * Q by positivity)
    exact hh.trans hK
  have hraw : axisGap p lam ≤ -2 + 2 / Q + 8 / 3 * Q * a * L + 2 * d + 2 * Q * B := by
    have hT1 := hterms.1
    have hT2 := hterms.2.1
    have hT2eq := hterms.2.2.1
    have hT2lo := hterms.2.2.2
    change (2 * C) ^ p ≤ 2 * Q + 2 / Q + 8 / 3 * Q * a * L at hT1
    change axisGap p lam ≤ (2 * C) ^ p - (2 * ((1 + lam) / 2)) ^ p - kConst p lam at hmid
    change 2 * ((1 + lam) / 2) ≤ (2 * ((1 + lam) / 2)) ^ p at hT2
    change 2 * ((1 + lam) / 2) = 2 / (1 + d) at hT2eq
    change 2 - 2 * d ≤ 2 / (1 + d) at hT2lo
    nlinarith only [hT1, hT2, hT2eq, hT2lo, hKb, hmid]
  have hlogterm : 8 / 3 * Q * a * L ≤ 16 / 3 * sqrt a * L := by
    have hh := mul_le_mul_of_nonneg_right hQup (show 0 ≤ 8 / 3 * a * L by positivity)
    have heq : (2 / sqrt a) * (8 / 3 * a * L) = 16 / 3 * sqrt a * L := by
      field_simp <;> ring_nf <;> simp only [hs2, hs3] <;> ring
    rw [heq] at hh
    nlinarith only [hh]
  have herror : 2 * Q * B ≤ sqrt a * (2 / 3 * log (1 / a) + 4 * a + 4 * sqrt a + 8) := by
    have hh := mul_le_mul_of_nonneg_right hQup (show 0 ≤ 2 * B by positivity)
    have heq : (2 / sqrt a) * (2 * B) = sqrt a *
        (2 / 3 * log (1 / a) + 4 * a + 4 * sqrt a + 8) := by
      dsimp only [B]
      field_simp <;> ring_nf <;> simp only [hs2, hs3] <;> ring
    rw [heq] at hh
    nlinarith only [hh]
  change axisGap p lam ≤ -2 + endpointError a
  unfold endpointError
  change axisGap p lam ≤ -2 + sqrt a * (2 + 16 / 3 * L + 1.8 + 2 / 3 * log (1 / a) + 8 + 4 * sqrt a + 4 * a)
  nlinarith only [hraw, hInv2, hd, hlogterm, herror]

/-- The full analytic endpoint lemma, at the actual global lambdaLoc; no Check hypothesis. -/
theorem endpoint_estimate_proved {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    axisGap p (Threshold.lambdaLoc p) < -(1.88 : ℝ) ∧ axisGap p (Threshold.lambdaLoc p) < 0 := by
  have ha := endpoint_a_range hp hp1
  have hm := endpoint_error_monotone ⟨ha.1, ha.2.1.le⟩
    (show (3.2 * 10 ^ (-6 : ℤ) : ℝ) ∈ Set.Ioc 0 (3.2 * 10 ^ (-6 : ℤ)) by constructor <;> norm_num) ha.2.1.le
  have hn := endpoint_error_numeric
  dsimp only at hn
  have hh := endpoint_remainder_bound hp hp1
  have hhi : p ≤ (1000001 : ℝ) / 1000000 := by norm_num at hp1; linarith
  rw [endpointLambda_eq_lambdaLoc hp hhi] at hh
  constructor <;> linarith [hn.2.2.2]

end GKSharp

#print axioms GKSharp.endpoint_remainder_bound
#print axioms GKSharp.endpoint_estimate_proved
