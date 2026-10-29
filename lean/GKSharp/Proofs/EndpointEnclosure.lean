/- analytic endpoint threshold and its squared-root enclosures.
Frozen source: short_v0.70/endpoint_estimate.tex:9–22.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.EndpointElementary
import GKSharp.Proofs.EndpointBridge
import GKSharp.Proofs.Sec4bChecks

namespace GKSharp
open Real Threshold Set

theorem endpoint_d_basic {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    0 < endpointD p ∧ endpointD p < 1 ∧
    endpointD p ^ 2 = sin (endpointA p) ^ 2 / cos (endpointA p) ^ 4 *
      (p * Real.pi / (4 * endpointA p) - 1 - cos (endpointA p) ^ 2) ∧
    1 - endpointLambda p = 2 * endpointD p / (1 + endpointD p) ∧
    endpointLambda p ∈ Ioo (0 : ℝ) 1 := by
  have hhi : p ≤ (1000001 : ℝ) / 1000000 := by norm_num at hp1; linarith
  have hp2 : p < 2 := by linarith
  have hF := localF_positive_endpoint hp hhi
  have hd := sec4b_localD2_pos hp hp2 hF
  have hd1 := sec4b_localD2_lt_one hp hp2
  have hd0 : 0 < endpointD p := by rw [endpointD_eq_sqrt_localD2 hp]; exact sqrt_pos.mpr hd
  have hdlt : endpointD p < 1 := by
    rw [endpointD_eq_sqrt_localD2 hp]
    nlinarith [sq_sqrt hd.le, sqrt_nonneg (localD2 p)]
  refine ⟨hd0, hdlt, ?_, ?_, ?_⟩
  · have hs : endpointD p ^ 2 = localD2 p := by
      rw [endpointD_eq_sqrt_localD2 hp, sq_sqrt hd.le]
    have hnonneg : 0 ≤ sin (endpointA p) ^ 2 / cos (endpointA p) ^ 4 *
        (p * Real.pi / (4 * endpointA p) - 1 - cos (endpointA p) ^ 2) := by
      have he : localD2 p = sin (endpointA p) ^ 2 / cos (endpointA p) ^ 4 *
          (p * Real.pi / (4 * endpointA p) - 1 - cos (endpointA p) ^ 2) := by
        have hh := endpointD_eq_sqrt_localD2 hp
        have ha : endpointA p = Real.pi - Real.pi / p := by
          unfold endpointA; field_simp <;> ring
        have ht : p * Real.pi / (4 * endpointA p) = p * dual p / 4 := by
          unfold endpointA dual
          field_simp [ne_of_gt hp, sub_ne_zero.mpr (ne_of_gt hp), Real.pi_ne_zero]
          <;> ring
        rw [ht, ha, sin_pi_sub, cos_pi_sub]
        unfold localD2 sn cs
        ring
      rw [← he]
      exact hd.le
    exact sq_sqrt hnonneg
  · unfold endpointLambda
    field_simp
    <;> ring
  · rw [endpointLambda_eq_lambdaLoc hp hhi]
    exact (sec4b_lambdaLoc_mem hp hp2 hF).2

/-- The complete d² enclosure printed in the analytic appendix. -/
theorem endpoint_d_squared_bounds {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    Real.pi * endpointA p / 4 * (1 - 3 * endpointA p) ≤ endpointD p ^ 2 ∧
      endpointD p ^ 2 ≤ Real.pi * endpointA p / 4 * (1 + endpointA p) := by
  let a := endpointA p
  have ha0 : 0 < a := (endpoint_a_range hp hp1).1
  have ha1 : a ≤ 1 / 100000 := by
    have hh := (endpoint_a_range hp hp1).2.1
    norm_num at hh
    dsimp only [a]
    linarith
  have ha10 : a ≤ 1 / 10 := by linarith
  have hc : 0 < cos a := by nlinarith [one_sub_sq_div_two_le_cos (x := a)]
  have hc4 : 0 < cos a ^ 4 := pow_pos hc _
  have hc41 : cos a ^ 4 ≤ 1 := by nlinarith [cos_sq_le_one a, sq_nonneg (cos a ^ 2 - 1)]
  have hpbd : p ≤ 1 + a / 3 := by have := endpoint_p_sub_one hp hp1; linarith
  have hsq := (endpoint_d_basic hp hp1).2.2.1
  change endpointD p ^ 2 = sin a ^ 2 / cos a ^ 4 *
    (p * Real.pi / (4 * a) - 1 - cos a ^ 2) at hsq
  have htlo : Real.pi / (4 * a) - 2 ≤ p * Real.pi / (4 * a) - 1 - cos a ^ 2 :=
    (endpoint_enclosure_ingredients hp hp1).2.1
  have ht0 : 0 ≤ Real.pi / (4 * a) - 2 := by
    have hh : 8 * a ≤ Real.pi := by nlinarith [Real.pi_gt_d2]
    have hh' : 2 ≤ Real.pi / (4 * a) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    linarith
  have hsin := small_angle_sin_square ha0.le ha10
  have hsinupper : sin a ^ 2 ≤ a ^ 2 := by
    exact (sq_le_sq₀ (sin_nonneg_of_nonneg_of_le_pi ha0.le (by linarith [Real.pi_gt_d2])) ha0.le).mpr
      (sin_le ha0.le)
  have ha2 : a ^ 2 ≤ (1 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ ha0.le ha1 2
  constructor
  · have hfrac : a ^ 2 * (1 - a ^ 2 / 3) ≤ sin a ^ 2 / cos a ^ 4 := by
      have hs : sin a ^ 2 ≤ sin a ^ 2 / cos a ^ 4 := by
        rw [le_div_iff₀ hc4]
        exact mul_le_of_le_one_right (sq_nonneg _) hc41
      exact hsin.trans hs
    have hlo := mul_le_mul hfrac htlo ht0 (div_nonneg (sq_nonneg _) hc4.le)
    have hcancel : (a ^ 2 * (1 - a ^ 2 / 3)) * (Real.pi / (4 * a) - 2) =
        Real.pi * a / 4 - 2 * a ^ 2 - Real.pi * a ^ 3 / 12 + 2 * a ^ 4 / 3 := by
      field_simp
      <;> ring
    rw [hcancel, ← hsq] at hlo
    have hapos := mul_nonneg (sq_nonneg a) (show 0 ≤ (1 : ℝ) / 10 - a by linarith)
    have hpi : Real.pi * a ^ 3 ≤ 4 * a ^ 3 :=
      mul_le_mul_of_nonneg_right Real.pi_le_four (by positivity)
    have hpilo : 3 * a ^ 2 ≤ Real.pi * a ^ 2 :=
      mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg a)
    nlinarith [sq_nonneg (a ^ 2)]
  · have hfrac : sin a ^ 2 / cos a ^ 4 ≤ a ^ 2 * (1 + 3 * a ^ 2) := by
      calc
        sin a ^ 2 / cos a ^ 4 ≤ a ^ 2 / cos a ^ 4 := div_le_div_of_nonneg_right hsinupper hc4.le
        _ = a ^ 2 * (1 / cos a ^ 4) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (small_angle_inv_cos_four ha0.le ha10) (sq_nonneg a)
    have htup : p * Real.pi / (4 * a) - 1 - cos a ^ 2 ≤ p * Real.pi / (4 * a) := by nlinarith [sq_nonneg (cos a)]
    have hbound := mul_le_mul hfrac htup (ht0.trans htlo) (by positivity)
    have hcancel : a ^ 2 * (1 + 3 * a ^ 2) * (p * Real.pi / (4 * a)) =
        Real.pi * a / 4 * (p * (1 + 3 * a ^ 2)) := by field_simp <;> ring
    rw [hcancel, ← hsq] at hbound
    have hpcomp := mul_le_mul_of_nonneg_right hpbd (show 0 ≤ 1 + 3 * a ^ 2 by positivity)
    have hprod := hpcomp.trans (small_angle_product ha0.le ha10)
    exact hbound.trans (mul_le_mul_of_nonneg_left hprod (by positivity))

end GKSharp

#print axioms GKSharp.endpoint_d_basic
#print axioms GKSharp.endpoint_d_squared_bounds
