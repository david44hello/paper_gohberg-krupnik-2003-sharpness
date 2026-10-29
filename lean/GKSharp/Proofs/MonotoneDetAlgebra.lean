/- determinant algebra certificate, frozen sec5d:28.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneLogM

namespace GKSharp

private def detPolynomial (e sma spa smb spb cma cpa cmb cpb s2a s2b c2a c2b : ℝ) : ℝ :=
  4*c2a*cma*e*s2b*smb*spa*spb - 4*c2a*cmb*e*s2b*sma*spa*spb - 4*c2a*cpa*e*s2b*sma*smb*spb + 4*c2a*cpb*e*s2b*sma*smb*spa - 4*c2b*cma*e*s2a*smb*spa*spb + 4*c2b*cmb*e*s2a*sma*spa*spb + 4*c2b*cpa*e*s2a*sma*smb*spb - 4*c2b*cpb*e*s2a*sma*smb*spa + cma*cmb*e^2*s2a*s2b*spa*spb - 2*cma*cmb*e*s2a*s2b*spa*spb + cma*cmb*s2a*s2b*spa*spb - 4*cma*cpa*e*s2a*s2b*smb*spb + cma*cpb*e^2*s2a*s2b*smb*spa + 2*cma*cpb*e*s2a*s2b*smb*spa + cma*cpb*s2a*s2b*smb*spa + cmb*cpa*e^2*s2a*s2b*sma*spb + 2*cmb*cpa*e*s2a*s2b*sma*spb + cmb*cpa*s2a*s2b*sma*spb - 4*cmb*cpb*e*s2a*s2b*sma*spa + cpa*cpb*e^2*s2a*s2b*sma*smb - 2*cpa*cpb*e*s2a*s2b*sma*smb + cpa*cpb*s2a*s2b*sma*smb

set_option maxHeartbeats 2000000 in
private theorem det_cancel (e sma spa smb spb cma cpa cmb cpb s2a s2b c2a c2b : ℝ)
    (hma : sma ≠ 0) (hpa : spa ≠ 0) (hmb : smb ≠ 0) (hpb : spb ≠ 0)
    (ha : s2a ≠ 0) (hb : s2b ≠ 0) :
    2 * s2a * s2b * ((-(1 - (e + 1) / 2) * e * (cmb / smb) + ((e + 1) / 2) * e * (cpb / spb) + 2 * e * (c2a / s2a) - e * (cpa / spa) - 2 * e * (c2b / s2b)) *
      ((cma / sma) + (cpb / spb) - (cpa / spa) - (cmb / smb)) -
    ((1 - (e + 1) / 2) * (cmb / smb) + ((e + 1) / 2) * (cpb / spb) - e * (cpa / spa)) *
      (-(cma / sma) + e * (cpb / spb) - (cpa / spa) + e * (cmb / smb))) * (sma * spa * smb * spb) =
      detPolynomial e sma spa smb spb cma cpa cmb cpb s2a s2b c2a c2b := by
  unfold detPolynomial
  field_simp [hma,hpa,hmb,hpb,ha,hb]
  <;> ring

set_option maxHeartbeats 2000000 in
private theorem det_polynomial_certificate (e SA CA SB CB SG CG : ℝ)
    (ha : CA ^ 2 + SA ^ 2 = 1) (hb : CB ^ 2 + SB ^ 2 = 1) (hg : CG ^ 2 + SG ^ 2 = 1) :
    detPolynomial e (SG*CA-CG*SA) (SG*CA+CG*SA) (SG*CB-CG*SB) (SG*CB+CG*SB) (CG*CA+SG*SA) (CG*CA-SG*SA) (CG*CB+SG*SB) (CG*CB-SG*SB) (2*SA*CA) (2*SB*CB) (CA^2-SA^2) (CB^2-SB^2) =
    -8*CA*CB*SA*SB*e*((CA*CB + SA*SB)^2 - (-CA*SB + CB*SA)^2) - 4*CA*CB*SA*SB*(1 - e)^2*(CG^2 - SG^2)^2 + 4*CA*CB*SA*SB*(e^2 + 1) + 2*e*(CG^2 - SG^2)*(CA*CB + SA*SB)*(2*CA*SA - 2*CB*SB)*(-2*CA*SB + 2*CB*SA) - 2*e*(CA*CB + SA*SB)^2*(-2*CA*SB + 2*CB*SA)^2 := by
  unfold detPolynomial
  linear_combination (4*(-4*CA^4*CB^2*SB^2*SG^2*e + 4*CA^3*CB^3*SA*SB*SG^2*e^2 + 4*CA^3*CB^3*SA*SB*SG^2 + 4*CA^3*CB*SA*SB^3*SG^2*e^2 - 8*CA^3*CB*SA*SB^3*SG^2*e + 4*CA^3*CB*SA*SB^3*SG^2 + 2*CA^3*CB*SA*SB*e - 4*CA^2*CB^4*SA^2*SG^2*e - 2*CA^2*CB^2*SA^2*e - 2*CA^2*CB^2*SB^2*e - 4*CA^2*CG^2*SA^2*SB^4*e - 4*CA^2*SA^2*SB^4*e + 2*CA^2*SA^2*SB^2*e + 4*CA*CB^3*SA^3*SB*SG^2*e^2 - 8*CA*CB^3*SA^3*SB*SG^2*e + 4*CA*CB^3*SA^3*SB*SG^2 + 2*CA*CB^3*SA*SB*e + 8*CA*CB*CG^2*SA^3*SB^3*e + CA*CB*CG^2*SA*SB*e^2 - 2*CA*CB*CG^2*SA*SB*e + CA*CB*CG^2*SA*SB + 4*CA*CB*SA^3*SB^3*SG^2*e^2 - 8*CA*CB*SA^3*SB^3*SG^2*e + 4*CA*CB*SA^3*SB^3*SG^2 + 8*CA*CB*SA^3*SB^3*e - 2*CA*CB*SA^3*SB*e - 2*CA*CB*SA*SB^3*e - 3*CA*CB*SA*SB*SG^2*e^2 + 6*CA*CB*SA*SB*SG^2*e - 3*CA*CB*SA*SB*SG^2 + CA*CB*SA*SB*e^2 - 2*CA*CB*SA*SB*e + CA*CB*SA*SB - 4*CB^2*CG^2*SA^4*SB^2*e - 4*CB^2*SA^4*SB^2*e + 2*CB^2*SA^2*SB^2*e)) * hg +
    (-8*(2*CA^2*CB^2*SB^2*SG^2*e - CA^2*CB^2*SB^2*e + 2*CA*CB^3*SA*SB*SG^4*e^2 - 4*CA*CB^3*SA*SB*SG^4*e + 2*CA*CB^3*SA*SB*SG^4 - 2*CA*CB^3*SA*SB*SG^2*e^2 - 2*CA*CB^3*SA*SB*SG^2 + CA*CB^3*SA*SB*e + 2*CA*CB*SA*SB^3*SG^4*e^2 - 4*CA*CB*SA*SB^3*SG^4*e + 2*CA*CB*SA*SB^3*SG^4 - 2*CA*CB*SA*SB^3*SG^2*e^2 + 4*CA*CB*SA*SB^3*SG^2*e - 2*CA*CB*SA*SB^3*SG^2 - CA*CB*SA*SB^3*e + 2*CA*CB*SA*SB*SG^2*e - CA*CB*SA*SB*e + 2*CB^4*SA^2*SG^2*e - CB^4*SA^2*e - 2*CB^2*SA^2*SB^2*SG^2*e + CB^2*SA^2*SB^2*e - 2*CB^2*SA^2*SG^2*e + CB^2*SA^2*e - 2*SA^2*SB^4*SG^2*e + SA^2*SB^4*e + 2*SA^2*SB^2*SG^2*e - SA^2*SB^2*e)) * ha +
    (-8*SA*(4*CA*CB*SA^2*SB*SG^2*e - 2*CA*CB*SA^2*SB*e + 2*CA*CB*SB*SG^4*e^2 - 4*CA*CB*SB*SG^4*e + 2*CA*CB*SB*SG^4 - 2*CA*CB*SB*SG^2*e^2 + 2*CA*CB*SB*SG^2*e - 2*CA*CB*SB*SG^2 - 2*CB^2*SA^3*SG^2*e + CB^2*SA^3*e + 2*CB^2*SA*SG^2*e - CB^2*SA*e + 2*SA^3*SB^2*SG^2*e - SA^3*SB^2*e - 2*SA*SB^2*SG^2*e + SA*SB^2*e)) * hb

set_option maxHeartbeats 2000000 in
theorem determinant_trigonometric (e a b g : ℝ)
    (hma : Real.sin (g - a) ≠ 0) (hpa : Real.sin (g + a) ≠ 0)
    (hmb : Real.sin (g - b) ≠ 0) (hpb : Real.sin (g + b) ≠ 0)
    (ha : Real.sin (2 * a) ≠ 0) (hb : Real.sin (2 * b) ≠ 0) :
    2 * Real.sin (2 * a) * Real.sin (2 * b) * ((-(1 - (e + 1) / 2) * e * (Real.cot (g - b)) + ((e + 1) / 2) * e * (Real.cot (g + b)) + 2 * e * (Real.cot (2 * a)) - e * (Real.cot (g + a)) - 2 * e * (Real.cot (2 * b))) *
      ((Real.cot (g - a)) + (Real.cot (g + b)) - (Real.cot (g + a)) - (Real.cot (g - b))) -
    ((1 - (e + 1) / 2) * (Real.cot (g - b)) + ((e + 1) / 2) * (Real.cot (g + b)) - e * (Real.cot (g + a))) *
      (-(Real.cot (g - a)) + e * (Real.cot (g + b)) - (Real.cot (g + a)) + e * (Real.cot (g - b)))) *
      (Real.sin (g - a) * Real.sin (g + a) * Real.sin (g - b) * Real.sin (g + b)) =
    -(1 - e) ^ 2 * Real.sin (2 * a) * Real.sin (2 * b) * Real.cos (2 * g) ^ 2 +
      2 * e * Real.sin (2 * (a - b)) * (Real.sin (2 * a) - Real.sin (2 * b)) * Real.cos (2 * g) +
      (1 + e ^ 2) * Real.sin (2 * a) * Real.sin (2 * b) -
      2 * e * Real.sin (2 * a) * Real.sin (2 * b) * Real.cos (2 * (a - b)) -
      2 * e * Real.sin (2 * (a - b)) ^ 2 := by
  calc
    _ = detPolynomial e (Real.sin (g - a)) (Real.sin (g + a)) (Real.sin (g - b)) (Real.sin (g + b))
        (Real.cos (g - a)) (Real.cos (g + a)) (Real.cos (g - b)) (Real.cos (g + b))
        (Real.sin (2 * a)) (Real.sin (2 * b)) (Real.cos (2 * a)) (Real.cos (2 * b)) := by
      simp only [Real.cot_eq_cos_div_sin]
      exact det_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ hma hpa hmb hpb ha hb
    _ = _ := by
      have hp := det_polynomial_certificate e (Real.sin a) (Real.cos a) (Real.sin b) (Real.cos b)
        (Real.sin g) (Real.cos g)
        (by nlinarith [Real.sin_sq_add_cos_sq a])
        (by nlinarith [Real.sin_sq_add_cos_sq b])
        (by nlinarith [Real.sin_sq_add_cos_sq g])
      convert hp using 1 <;>
        simp only [detPolynomial,Real.sin_add,Real.sin_sub,Real.cos_add,Real.cos_sub,
          Real.sin_two_mul,Real.cos_two_mul'] <;> ring

end GKSharp

