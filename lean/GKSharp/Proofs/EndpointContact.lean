/- actual contact-radius inequalities in the analytic endpoint appendix.
Frozen source: short_v0.70/endpoint_estimate.tex:39–45.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.EndpointScale
import GKSharp.Proofs.LemmaEContact
import GKSharp.Proofs.ContactScalar

namespace GKSharp
open Real Threshold Set

private theorem endpoint_contact_scalar {lam c s r : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (hsc : s ^ 2 + c ^ 2 = 1) (hr1 : 1 < r)
    (hv : 0 < r - lam / r) (hroot : r + lam / r = (1 + lam) / c) :
    r - lam / r = sqrt ((1 - lam) ^ 2 + 4 * lam * s ^ 2) / c ∧
      1 / c ≤ r ∧ r ≤ (1 + s ^ 2 / (1 - lam)) / c ∧
      r - lam / r ≤ (1 - lam) * (1 + 2 * s ^ 2 / (1 - lam) ^ 2) / c := by
  have hr0 : 0 < r := by linarith
  have he0 : 0 < 1 - lam := by linarith
  have hrpoly : c * r ^ 2 - (1 + lam) * r + c * lam = 0 := by
    have hh := hroot
    field_simp at hh
    nlinarith
  have hX0 : 0 ≤ c * r - 1 := by
    have hh : (c * r - 1) * r = lam * (r - c) := by linear_combination hrpoly
    have hn := mul_nonneg hl0.le (show 0 ≤ r - c by linarith)
    nlinarith
  have hX : (c * r - 1) ^ 2 + (1 - lam) * (c * r - 1) = lam * s ^ 2 := by
    linear_combination c * hrpoly - lam * hsc
  have hXup : c * r - 1 ≤ s ^ 2 / (1 - lam) := by
    rw [le_div_iff₀ he0]
    have hh := mul_le_mul_of_nonneg_right hl1.le (sq_nonneg s)
    nlinarith [sq_nonneg (c * r - 1)]
  have hrad0 : 0 ≤ (1 - lam) ^ 2 + 4 * lam * s ^ 2 := by positivity
  have hvsq : (c * (r - lam / r)) ^ 2 = (1 - lam) ^ 2 + 4 * lam * s ^ 2 := by
    have hdiff : (r - lam / r) ^ 2 = (r + lam / r) ^ 2 - 4 * lam := by
      field_simp
      <;> ring
    have hh : c ^ 2 * (r + lam / r) ^ 2 = (1 + lam) ^ 2 := by
      rw [hroot]
      field_simp
    linear_combination c ^ 2 * hdiff + hh - 4 * lam * hsc
  have hvformula : r - lam / r = sqrt ((1 - lam) ^ 2 + 4 * lam * s ^ 2) / c := by
    apply (eq_div_iff hc.ne').mpr
    have hh := sq_sqrt hrad0
    have hn := sqrt_nonneg ((1 - lam) ^ 2 + 4 * lam * s ^ 2)
    have hcv := mul_pos hc hv
    nlinarith
  have hsup : sqrt ((1 - lam) ^ 2 + 4 * lam * s ^ 2) ≤
      (1 - lam) + 2 * s ^ 2 / (1 - lam) := by
    have hn : 0 ≤ (1 - lam) + 2 * s ^ 2 / (1 - lam) := by positivity
    have hh := sq_sqrt hrad0
    have hcancel : (1 - lam) * (2 * s ^ 2 / (1 - lam)) = 2 * s ^ 2 := by field_simp
    have hmul := mul_le_mul_of_nonneg_right hl1.le (sq_nonneg s)
    nlinarith [sqrt_nonneg ((1 - lam) ^ 2 + 4 * lam * s ^ 2), sq_nonneg (2 * s ^ 2 / (1 - lam))]
  refine ⟨hvformula, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hc]
    linarith
  · rw [le_div_iff₀ hc]
    linarith
  · rw [hvformula]
    have hh := div_le_div_of_nonneg_right hsup hc.le
    have heq : ((1 - lam) + 2 * s ^ 2 / (1 - lam)) / c =
        (1 - lam) * (1 + 2 * s ^ 2 / (1 - lam) ^ 2) / c := by field_simp <;> ring
    rwa [heq] at hh

theorem endpoint_contact_bounds {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let lam := endpointLambda p
    let eps := 1 - lam
    let r := contactRadius p lam
    let v := r - lam / r
    v = sqrt (eps ^ 2 + 4 * lam * sin a ^ 2) / cos a ∧
    r + lam / r = (1 + lam) / cos a ∧
    1 / cos a ≤ r ∧ r ≤ (1 + sin a ^ 2 / eps) / cos a ∧
    v ≤ eps * (1 + 2 * sin a ^ 2 / eps ^ 2) / cos a ∧
    eps ≤ r - lam ∧ r - lam ≤ ‖(r : ℂ) * unitPoint (Real.pi / p) + (lam : ℂ)‖ := by
  dsimp only
  let a := endpointA p
  let lam := endpointLambda p
  have hhi : p ≤ (1000001 : ℝ) / 1000000 := by norm_num at hp1; linarith
  have hp2 : p < 2 := by linarith
  have hl := (endpoint_d_basic hp hp1).2.2.2.2
  have hl' : lam ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hl.1], hl.2⟩
  have ha : a = Real.pi - Real.pi / p := by dsimp only [a]; unfold endpointA; field_simp <;> ring
  have hcs : cs p = cos a := by rw [ha, cos_pi_sub]; rfl
  have hsn : sn p = sin a := by rw [ha, sin_pi_sub]; rfl
  have hc := sec4b_cs_pos hp hp2
  rw [hcs] at hc
  have hsc : sin a ^ 2 + cos a ^ 2 = 1 := sin_sq_add_cos_sq a
  have hrad := ContactLower.contactRadius_interior p lam hp hp2 hl'
  rw [hrad]
  let r := rContact p lam
  obtain ⟨hr, -, hv, hsum⟩ := contact_root_properties hp hp2 hl'
  have hsum' : r + lam / r = (1 + lam) / cos a := by simpa only [sigmaContact, hcs] using hsum
  have hscalar := endpoint_contact_scalar hl.1 hl.2 hc (cos_le_one a) hsc hr hv hsum'
  refine ⟨hscalar.1, hsum', hscalar.2.1, hscalar.2.2.1, hscalar.2.2.2, by linarith, ?_⟩
  have hn : ‖(r : ℂ) * unitPoint (Real.pi / p)‖ = r := by
    rw [norm_mul, norm_unitPoint, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ r)]
  have hh := norm_sub_norm_le ((r : ℂ) * unitPoint (Real.pi / p)) (-(lam : ℂ))
  rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hl.1.le, hn, sub_neg_eq_add] at hh
  exact hh

end GKSharp

#print axioms GKSharp.endpoint_contact_bounds
