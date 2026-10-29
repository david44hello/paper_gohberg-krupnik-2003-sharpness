/- GKSharp/Proofs/LocalGapCertificate.lean — uniform kernel certificate.
Frozen source: short_v0.40/sec4b_failure.tex:135, calculation_certificates.tex:31.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.LocalFCertificate
import GKSharp.Proofs.EndpointBridge
import GKSharp.ComputerChecked

namespace GKSharp
open Threshold Set

private theorem jordan_quotient_antitone {lo p : ℝ} (hlo : 1 < lo)
    (hlo2 : lo ≤ 2) (hp : lo ≤ p) (hp2 : p ≤ 2) :
    p * dual p ≤ lo ^ 2 / (lo - 1) := by
  have ha : 0 ≤ p - lo := sub_nonneg.mpr hp
  have hb : (p - 1) * (lo - 1) ≤ 1 := calc
    _ ≤ 1 * (lo - 1) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    _ ≤ 1 := by linarith
  have hprod := mul_nonneg ha (sub_nonneg.mpr hb)
  unfold dual
  rw [← mul_div_assoc, div_le_div_iff₀ (by linarith : 0 < p - 1) (by linarith : 0 < lo - 1)]
  nlinarith [hprod]

private theorem cs_lower_of_upper {p hi low : ℝ} (hp : 1 < p) (hh : p ≤ hi)
    (hlow : low ≤ Real.cos (Real.pi * (hi - 1) / hi)) : low ≤ cs p := by
  have hp0 : 0 < p := by linarith
  have hhi0 : 0 < hi := by linarith
  have hap : Real.pi * (p - 1) / p = Real.pi - Real.pi / p := by field_simp
  have hahi : Real.pi * (hi - 1) / hi = Real.pi - Real.pi / hi := by field_simp
  have hang : Real.pi * (p - 1) / p ≤ Real.pi * (hi - 1) / hi := by
    rw [hap, hahi]
    linarith [div_le_div_of_nonneg_left Real.pi_pos.le hp0 hh]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ Real.pi * (p - 1) / p by positivity)
    (show Real.pi * (hi - 1) / hi ≤ Real.pi by
      rw [hahi]
      linarith [div_pos Real.pi_pos hhi0])
    hang
  rw [hap, Real.cos_pi_sub] at hcos
  exact hlow.trans hcos

private theorem cosine_mid_lower :
    851159170 / 1000000000 ≤ Real.cos (Real.pi * ((12134452 / 10000000 : ℝ) - 1) /
      (12134452 / 10000000 : ℝ)) := by
  let aa : ℝ := Real.pi * ((533613 / 3033613 : ℚ) : ℝ)
  have hpi : Real.pi ∈ Icc (3.14159265358979323846 : ℝ) 3.14159265358979323847 :=
    ⟨Real.pi_gt_d20.le, Real.pi_lt_d20.le⟩
  have ha : |aa| ≤ 1 := by
    dsimp [aa]
    rw [abs_of_pos (by positivity)]
    nlinarith [hpi.1, hpi.2]
  have hpoly : ((8511591701 / 10000000000 : ℚ) : ℝ) ≤ cosTaylor12 aa := by
    unfold cosTaylor12 aa
    dyadic_interval [prec := 100]
  norm_num at hpoly
  have hb := (abs_le.mp (cosTaylor12_bound aa ha)).1
  have he : Real.pi * ((12134452 / 10000000 : ℝ) - 1) /
      (12134452 / 10000000 : ℝ) = aa := by dsimp [aa]; ring
  rw [he]
  linarith

private theorem cosine_high_lower :
    851108547 / 1000000000 ≤ Real.cos (Real.pi * ((12134904 / 10000000 : ℝ) - 1) /
      (12134904 / 10000000 : ℝ)) := by
  let aa : ℝ := Real.pi * ((266863 / 1516863 : ℚ) : ℝ)
  have hpi : Real.pi ∈ Icc (3.14159265358979323846 : ℝ) 3.14159265358979323847 :=
    ⟨Real.pi_gt_d20.le, Real.pi_lt_d20.le⟩
  have ha : |aa| ≤ 1 := by
    dsimp [aa]
    rw [abs_of_pos (by positivity)]
    nlinarith [hpi.1, hpi.2]
  have hpoly : ((8511085471 / 10000000000 : ℚ) : ℝ) ≤ cosTaylor12 aa := by
    unfold cosTaylor12 aa
    dyadic_interval [prec := 100]
  norm_num at hpoly
  have hb := (abs_le.mp (cosTaylor12_bound aa ha)).1
  have he : Real.pi * ((12134904 / 10000000 : ℝ) - 1) /
      (12134904 / 10000000 : ℝ) = aa := by dsimp [aa]; ring
  rw [he]
  linarith

private theorem radicand_bound_of_scalar {p low aa : ℝ}
    (hlow : 0 < low) (_hsmall : low ≤ 1) (hc : low ≤ cs p)
    (ha : p * dual p ≤ aa) (he : 0 ≤ aa / 4 - 1 - low ^ 2)
    (hcert : (1 - low ^ 2) * (aa / 4 - 1 - low ^ 2) ≤ (9 / 40000 : ℝ) * low ^ 4) :
    localD2 p ≤ 9 / 40000 := by
  have hc0 : 0 < cs p := lt_of_lt_of_le hlow hc
  have hsq : low ^ 2 ≤ cs p ^ 2 := (sq_le_sq₀ hlow.le hc0.le).mpr hc
  have hfour : low ^ 4 ≤ cs p ^ 4 := pow_le_pow_left₀ hlow.le hc 4
  have htrig : sn p ^ 2 + cs p ^ 2 = 1 := by simp [sn, cs]
  have hs : sn p ^ 2 ≤ 1 - low ^ 2 := by linarith
  have hE : p * dual p / 4 - 1 - cs p ^ 2 ≤ aa / 4 - 1 - low ^ 2 := by linarith
  have hnum := mul_le_mul_of_nonneg_left hE (sq_nonneg (sn p))
  have hnum2 := mul_le_mul_of_nonneg_right hs he
  unfold localD2
  rw [div_le_iff₀ (pow_pos hc0 4)]
  nlinarith [hnum, hnum2]

/-- B:135,V:31. The whole compact local-gap radicand bound, using two p boxes.
PROVED in Lean, with no numerical replay or CheckLocalGap hypothesis. -/
theorem localD2_uniform_bound (p : ℝ)
    (hp : p ∈ Icc (6067 / 5000 : ℝ) (12134904 / 10000000)) :
    localD2 p ≤ 9 / 40000 := by
  have hp1 : 1 < p := by linarith [hp.1]
  have hp2 : p ≤ 2 := by linarith [hp.2]
  by_cases hmid : p ≤ 12134452 / 10000000
  · apply radicand_bound_of_scalar
      (low := 851159170 / 1000000000)
      (aa := (6067 / 5000 : ℝ) ^ 2 / ((6067 / 5000 : ℝ) - 1))
    · norm_num
    · norm_num
    · exact cs_lower_of_upper hp1 hmid cosine_mid_lower
    · exact jordan_quotient_antitone (by norm_num) (by norm_num) hp.1 hp2
    · norm_num
    · norm_num
  · apply radicand_bound_of_scalar
      (low := 851108547 / 1000000000)
      (aa := (12134452 / 10000000 : ℝ) ^ 2 / ((12134452 / 10000000 : ℝ) - 1))
    · norm_num
    · norm_num
    · exact cs_lower_of_upper hp1 hp.2 cosine_high_lower
    · exact jordan_quotient_antitone (by norm_num) (by norm_num) (le_of_not_ge hmid) hp2
    · norm_num
    · norm_num

/-- Exact discharge of the previously external local-gap Check Prop. -/
theorem checkLocalGap_proved : ComputerChecked.CheckLocalGap := by
  intro p hp
  exact (clipped_sqrt_gap_iff (localD2 p)).mpr (localD2_uniform_bound p hp)

end GKSharp

#print axioms GKSharp.localD2_uniform_bound
#print axioms GKSharp.checkLocalGap_proved
