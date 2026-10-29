/- complete lower estimates for K at the analytic endpoint.
Frozen source: short_v0.70/endpoint_estimate.tex:46–58.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.EndpointContactK
import GKSharp.Proofs.EndpointKError

namespace GKSharp
open Real Set

private theorem mul_lower_error {a b f g : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b < 1) (hf : 1 - a ≤ f) (hg : 1 - b ≤ g) :
    1 - (a + b) ≤ f * g := by
  have hh := mul_le_mul hf hg (show 0 ≤ 1 - b by linarith) (show 0 ≤ f by linarith)
  nlinarith [mul_nonneg ha hb]

private theorem product4_lower_error {a b c d f g h k : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : a + b + c + d < 1) (hf : 1 - a ≤ f) (hg : 1 - b ≤ g)
    (hh : 1 - c ≤ h) (hk : 1 - d ≤ k) :
    1 - (a + b + c + d) ≤ f * g * h * k := by
  have hfg := mul_lower_error ha hb (by linarith) hf hg
  have hhk := mul_lower_error hc hd (by linarith) hh hk
  have hh := mul_lower_error (show 0 ≤ a + b by positivity) (show 0 ≤ c + d by positivity)
    (by linarith) hfg hhk
  nlinarith

theorem endpoint_k_lower_bounds {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let lam := endpointLambda p
    let eps := 1 - lam
    let Q := eps / sin a
    let E := (p - 1) * log (1 / eps) + a ^ 2 + sin a ^ 2 / eps + 2 * sin a ^ 2 / eps ^ 2
    2 * Q * (cos a ^ 2 * eps ^ (p - 1) /
      ((1 + sin a ^ 2 / eps) * (1 + 2 * sin a ^ 2 / eps ^ 2))) ≤ kConst p lam ∧
      2 * Q * (1 - E) ≤ kConst p lam := by
  dsimp only
  let a := endpointA p
  let lam := endpointLambda p
  let eps := 1 - lam
  let Q := eps / sin a
  let r := contactRadius p lam
  let v := r - lam / r
  let N := ‖(r : ℂ) * unitPoint (Real.pi / p) + (lam : ℂ)‖
  let A := 1 + sin a ^ 2 / eps
  let B := 1 + 2 * sin a ^ 2 / eps ^ 2
  let L := (p - 1) * log (1 / eps)
  have hhi : p ≤ (1000001 : ℝ) / 1000000 := by norm_num at hp1; linarith
  have hp2 : p < 2 := by linarith
  have hl := (endpoint_d_basic hp hp1).2.2.2.2
  have he0 : 0 < eps := by dsimp only [eps, lam]; linarith [hl.2]
  have ha0 : 0 < a := (endpoint_a_range hp hp1).1
  have ha1 : a < 1 := by
    have hh := (endpoint_a_range hp hp1).2.1
    norm_num at hh
    dsimp only [a]
    linarith
  have hc : 0 < cos a := by
    nlinarith [one_sub_sq_div_two_le_cos (x := a)]
  have hs : 0 < sin a := sin_pos_of_pos_of_lt_pi ha0 (by linarith [pi_gt_three])
  have hQ : 0 < Q := div_pos he0 hs
  obtain ⟨_, _, hrlo, hrup, hvup, hepsr, hN⟩ := endpoint_contact_bounds hp hp1
  have hr1 : 1 ≤ r := by
    have hh : 1 ≤ 1 / cos a := (le_div_iff₀ hc).mpr (by simpa using cos_le_one a)
    exact hh.trans hrlo
  have hr0 : 0 < r := by linarith
  have hv0 : 0 < v := by
    dsimp only [v]
    have hh : lam / r < r := (div_lt_iff₀ hr0).mpr (by nlinarith [hl.2])
    linarith
  have hNlo : eps ≤ N := hepsr.trans hN
  have hN0 : 0 < N := he0.trans_le hNlo
  have hA0 : 0 < A := by dsimp only [A]; positivity
  have hB0 : 0 < B := by dsimp only [B]; positivity
  have hinv : cos a / A ≤ 1 / r := by
    rw [div_le_div_iff₀ hA0 hr0]
    have hh := (le_div_iff₀ hc).mp hrup
    change r * cos a ≤ A at hh
    nlinarith
  have hrpow : 1 / r ≤ r ^ (-(p / 2)) := by
    rw [one_div, ← rpow_neg_one]
    exact rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have hnum : 2 * Q * (cos a / A) * eps ^ p ≤ 2 * Q * r ^ (-(p / 2)) * N ^ p := by
    gcongr <;> first | exact hinv.trans hrpow | exact hNlo
  have hden : v ≤ eps * B / cos a := hvup
  have hratio : (2 * Q * (cos a / A) * eps ^ p) / (eps * B / cos a) ≤
      (2 * Q * r ^ (-(p / 2)) * N ^ p) / v := by
    calc
      _ ≤ (2 * Q * (cos a / A) * eps ^ p) / v :=
        div_le_div_of_nonneg_left (by positivity) hv0 hden
      _ ≤ _ := div_le_div_of_nonneg_right hnum hv0.le
  have hpeps : eps ^ p = eps ^ (p - 1) * eps := by
    calc
      eps ^ p = eps ^ ((p - 1) + 1) := by congr 1; ring
      _ = eps ^ (p - 1) * eps ^ (1 : ℝ) := rpow_add he0 _ _
      _ = _ := by rw [rpow_one]
  have halg : (2 * Q * (cos a / A) * eps ^ p) / (eps * B / cos a) =
      2 * Q * (cos a ^ 2 * eps ^ (p - 1) / (A * B)) := by
    rw [hpeps]
    field_simp
    <;> ring
  have hK := endpoint_contact_k_identity hp hp1
  change kConst p lam = 2 * Q * r ^ (-(p / 2)) * N ^ p / v at hK
  rw [halg, ← hK] at hratio
  refine ⟨hratio, ?_⟩
  have herr := endpoint_k_error_bounds hp hp1
  dsimp only at herr
  have hL0 : 0 ≤ L := by
    apply mul_nonneg (by linarith)
    exact log_nonneg ((le_div_iff₀ he0).mpr (by dsimp only [eps, lam]; linarith [hl.1]))
  have hU0 : 0 ≤ sin a ^ 2 / eps := by positivity
  have hV0 : 0 ≤ 2 * sin a ^ 2 / eps ^ 2 := by positivity
  have hsum : a ^ 2 + L + sin a ^ 2 / eps + 2 * sin a ^ 2 / eps ^ 2 < 1 := by
    have hh := herr.2.2.2.1
    change L + a ^ 2 + sin a ^ 2 / eps + 2 * sin a ^ 2 / eps ^ 2 < 1 at hh
    linarith
  have hprod := product4_lower_error (sq_nonneg a) hL0 hU0 hV0 hsum
    herr.2.2.1 herr.2.1
    (herr.2.2.2.2 (sin a ^ 2 / eps) hU0)
    (herr.2.2.2.2 (2 * sin a ^ 2 / eps ^ 2) hV0)
  have hprod' : 1 - (L + a ^ 2 + sin a ^ 2 / eps + 2 * sin a ^ 2 / eps ^ 2) ≤
      cos a ^ 2 * eps ^ (p - 1) / (A * B) := by
    convert hprod using 1 <;> simp only [A, B, div_eq_mul_inv, mul_inv_rev] <;> ring
  exact (mul_le_mul_of_nonneg_left hprod' (show 0 ≤ 2 * Q by positivity)).trans hratio

end GKSharp

#print axioms GKSharp.endpoint_k_lower_bounds
