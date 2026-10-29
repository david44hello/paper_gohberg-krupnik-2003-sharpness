/- GKSharp/Proofs/EndpointBridge.lean - endpoint/global-threshold and K bridges.
Frozen source: short_v0.40/.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Threshold
import GKSharp.Defs.Potential

namespace GKSharp
open GKSharp.Threshold

/-- endpoint_estimate.tex:9–14 and sec4b_failure.tex:21: the two printed
radicands are identical, before any threshold-equation theorem is used. -/
theorem endpointD_eq_sqrt_localD2 {p : ℝ} (hp : 1 < p) :
    endpointD p = Real.sqrt (localD2 p) := by
  have hp0 : p ≠ 0 := by linarith
  have hpm : p - 1 ≠ 0 := by linarith
  have ha : endpointA p = Real.pi - Real.pi / p := by
    unfold endpointA
    field_simp
    <;> ring
  have hterm : p * Real.pi / (4 * endpointA p) = p * dual p / 4 := by
    unfold endpointA dual
    field_simp [hp0, hpm, Real.pi_ne_zero]
    <;> ring
  dsimp only [endpointD]
  rw [hterm, ha, Real.sin_pi_sub, Real.cos_pi_sub]
  unfold localD2 sn cs
  congr 1
  ring

/-- sec4b_failure.tex:100: explicit analytic near-one sign of F. -/
theorem localF_positive_endpoint {p : ℝ} (hp : 1 < p) (hhi : p ≤ 1000001 / 1000000) :
    0 < localF p := by
  have hden : 0 < p - 1 := by linarith
  have hquot : 8 < p * dual p := by
    unfold dual
    rw [← mul_div_assoc, lt_div_iff₀ hden]
    nlinarith
  have hcos : Real.cos (Real.pi / p) ^ 2 ≤ 1 := Real.cos_sq_le_one _
  unfold localF
  linarith

/-- endpoint_estimate.tex:9–14, sec4b_failure.tex:20–21. This identifies the
endpoint author's object with the actual global piecewise threshold definition. -/
theorem endpointLambda_eq_lambdaLoc {p : ℝ} (hp : 1 < p) (hhi : p ≤ 1000001 / 1000000) :
    endpointLambda p = lambdaLoc p := by
  simp [endpointLambda, lambdaLoc, localF_positive_endpoint hp hhi, endpointD_eq_sqrt_localD2 hp]

/-- sec2_obstacle.tex:145: abs(cos) and the paper's −cos agree on1<p<2.
This is the exact contactK/kConst bridge requested by the endpoint interface. -/
theorem contactK_eq_kConst {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (lam : ℝ) :
    contactK p lam = kConst p lam := by
  have hp0 : 0 < p := by linarith
  have hcos : Real.cos (Real.pi / p) < 0 := by
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · rw [lt_div_iff₀ hp0]
      nlinarith [Real.pi_pos]
    · have hpi : Real.pi / p < Real.pi := by
        rw [div_lt_iff₀ hp0]
        nlinarith [Real.pi_pos]
      linarith [Real.pi_pos]
  simp only [contactK, kConst, abs_of_neg hcos]

/-- sec4b_failure.tex:135 and calculation_certificates.tex:31. A clipped
square-root gap bound reduces exactly to a rational bound on its radicand. -/
theorem clipped_sqrt_gap_iff (xx : ℝ) :
    (2 * Real.sqrt (max xx 0) ≤ 3 / 100 ↔ xx ≤ 9 / 40000) := by
  have hmax : 0 ≤ max xx 0 := le_max_right _ _
  have hs := Real.sq_sqrt hmax
  have hn := Real.sqrt_nonneg (max xx 0)
  constructor
  · intro hh
    have hprod := mul_nonneg (show 0 ≤ 3 / 100 - 2 * Real.sqrt (max xx 0) by linarith)
      (show 0 ≤ 3 / 100 + 2 * Real.sqrt (max xx 0) by positivity)
    nlinarith [le_max_left xx 0]
  · intro hh
    have hle : max xx 0 ≤ 9 / 40000 := max_le hh (by norm_num)
    nlinarith

end GKSharp

#print axioms GKSharp.endpointD_eq_sqrt_localD2
#print axioms GKSharp.localF_positive_endpoint
#print axioms GKSharp.endpointLambda_eq_lambdaLoc
#print axioms GKSharp.contactK_eq_kConst
#print axioms GKSharp.clipped_sqrt_gap_iff
