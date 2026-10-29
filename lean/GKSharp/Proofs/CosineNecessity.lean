/- elementary cosine support and tangency for Proposition Q.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.Sec4aArch

namespace GKSharp
open Set Filter Threshold
open scoped Topology

/-- An arch cosine supports the minorant on the entire positive half-circle.
The three-point inequality at 0, theta, t suffices for the exterior arc. -/
theorem cosine_support_of_arch {qq tt AA : ℝ} {ff : ℝ → ℝ}
    (hq0 : 0 < qq) (hq1 : qq < 1) (htt0 : 0 < tt) (httpi : tt < Real.pi)
    (hqtt : qq * tt = Real.pi / 2) (hconv : QTrigConvex qq ff)
    (harch : ∀ t ∈ Icc (-tt) tt, ff t = AA * Real.cos (qq * t)) :
    ∀ t ∈ Icc (0 : ℝ) Real.pi, AA * Real.cos (qq * t) ≤ ff t := by
  intro t ht
  by_cases htle : t ≤ tt
  · exact (harch t ⟨by linarith [ht.1], htle⟩).ge
  · have htt : tt < t := lt_of_not_ge htle
    have hmid : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
    have hright : Real.pi / 2 < qq * t := by nlinarith
    have hlength : qq * t - 0 < Real.pi := by
      have hqt := mul_le_mul_of_nonneg_left ht.2 hq0.le
      have hqp := mul_lt_mul_of_pos_right hq1 Real.pi_pos
      linarith
    have hh := sec4a_trig_three hconv (x := 0) (t := Real.pi / 2) (y := qq * t)
      hmid hright hlength
    have hzero : ff 0 = AA := by simpa using harch 0 ⟨by linarith, by linarith⟩
    have hcontact : ff tt = 0 := by
      rw [harch tt ⟨by linarith, le_rfl⟩, hqtt, Real.cos_pi_div_two, mul_zero]
    have hscale : Real.pi / 2 / qq = tt := (div_eq_iff hq0.ne').mpr (by linarith)
    change ff (Real.pi / 2 / qq) * Real.sin (qq * t - 0) ≤
      ff (0 / qq) * Real.sin (qq * t - Real.pi / 2) +
        ff (qq * t / qq) * Real.sin (Real.pi / 2 - 0) at hh
    rw [hscale, hcontact, zero_mul, zero_div, hzero, mul_div_cancel_left₀ t hq0.ne',
      sub_zero, Real.sin_pi_div_two, mul_one, Real.sin_sub_pi_div_two] at hh
    linarith

/-- Smooth tangency fixes the arch amplitude, without any assumed right derivative of ff. -/
theorem cosine_minorant_of_arch {qq tt AA KK : ℝ} {ff mm : ℝ → ℝ}
    (hq0 : 0 < qq) (hq1 : qq < 1) (htt0 : 0 < tt) (httpi : tt < Real.pi)
    (hqtt : qq * tt = Real.pi / 2) (hconv : QTrigConvex qq ff)
    (harch : ∀ t ∈ Icc (-tt) tt, ff t = AA * Real.cos (qq * t))
    (hminor : ∀ t, ff t ≤ mm t) (hmeven : Function.Even mm) (hmzero : mm tt = 0)
    (hmderiv : HasDerivAt mm (-qq * KK) tt) :
    AA = KK ∧ ∀ t ∈ Icc (-Real.pi) Real.pi, KK * Real.cos (qq * |t|) ≤ mm t := by
  have hs := cosine_support_of_arch hq0 hq1 htt0 httpi hqtt hconv harch
  have hbound : ∀ t ∈ Icc (0 : ℝ) Real.pi, AA * Real.cos (qq * t) ≤ mm t :=
    fun t ht => (hs t ht).trans (hminor t)
  have hmin : IsLocalMin (fun t => mm t - AA * Real.cos (qq * t)) tt := by
    filter_upwards [Ioo_mem_nhds htt0 httpi] with t ht
    rw [hmzero, hqtt, Real.cos_pi_div_two, mul_zero, sub_zero]
    exact sub_nonneg.mpr (hbound t ⟨ht.1.le, ht.2.le⟩)
  have hc : HasDerivAt (fun t => AA * Real.cos (qq * t)) (-AA * qq) tt := by
    convert (((Real.hasDerivAt_cos (qq * tt)).comp tt
      ((hasDerivAt_id tt).const_mul qq)).const_mul AA) using 1 <;>
      simp [hqtt] <;> ring
  have hz := hmin.hasDerivAt_eq_zero (hmderiv.sub hc)
  have heq : AA = KK := by nlinarith
  refine ⟨heq, fun t ht => ?_⟩
  have habs : |t| ∈ Icc (0 : ℝ) Real.pi := ⟨abs_nonneg t, abs_le.mpr ht⟩
  have hh := hbound |t| habs
  rw [heq] at hh
  rcases le_total 0 t with hpos | hneg
  · simpa only [abs_of_nonneg hpos] using hh
  · simpa only [abs_of_nonpos hneg, hmeven t] using hh

/-- Two differentiable barriers with the same value and derivative force the middle derivative. -/
theorem hasDerivAt_of_sandwich {lo ff hi : ℝ → ℝ} {tt dd : ℝ}
    (hlo : HasDerivAt lo dd tt) (hhi : HasDerivAt hi dd tt)
    (hvalue1 : lo tt = ff tt) (hvalue2 : hi tt = ff tt)
    (hbound : ∀ᶠ t in 𝓝 tt, lo t ≤ ff t ∧ ff t ≤ hi t) :
    HasDerivAt ff dd tt := by
  apply HasDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro eps heps
  filter_upwards [hlo.isLittleO.bound heps, hhi.isLittleO.bound heps, hbound]
    with t hlt hgt hbt
  simp only [Real.norm_eq_abs, smul_eq_mul] at hlt hgt ⊢
  rw [abs_le]
  rw [hvalue1] at hlt
  rw [hvalue2] at hgt
  constructor
  · linarith [(abs_le.mp hlt).1, hbt.1]
  · linarith [(abs_le.mp hgt).2, hbt.2]

/-- The minorant has the actual contact derivative, in fact on both sides. -/
theorem cosine_tangent_derivative_of_arch {qq tt AA KK : ℝ} {ff mm : ℝ → ℝ}
    (hq0 : 0 < qq) (hq1 : qq < 1) (htt0 : 0 < tt) (httpi : tt < Real.pi)
    (hqtt : qq * tt = Real.pi / 2) (hconv : QTrigConvex qq ff)
    (harch : ∀ t ∈ Icc (-tt) tt, ff t = AA * Real.cos (qq * t))
    (hminor : ∀ t, ff t ≤ mm t) (hmeven : Function.Even mm) (hmzero : mm tt = 0)
    (hmderiv : HasDerivAt mm (-qq * KK) tt) :
    AA = KK ∧ HasDerivAt ff (-KK * qq) tt := by
  have heq := (cosine_minorant_of_arch hq0 hq1 htt0 httpi hqtt hconv harch
    hminor hmeven hmzero hmderiv).1
  have hlow := cosine_support_of_arch hq0 hq1 htt0 httpi hqtt hconv harch
  have hfzero : ff tt = 0 := by
    rw [harch tt ⟨by linarith, le_rfl⟩, hqtt, Real.cos_pi_div_two, mul_zero]
  have hc : HasDerivAt (fun t => AA * Real.cos (qq * t)) (-KK * qq) tt := by
    convert (((Real.hasDerivAt_cos (qq * tt)).comp tt
      ((hasDerivAt_id tt).const_mul qq)).const_mul AA) using 1 <;>
      simp [hqtt, heq] <;> ring
  refine ⟨heq, hasDerivAt_of_sandwich (hi := mm) hc ?_ ?_ ?_ ?_⟩
  · convert hmderiv using 1 <;> ring
  · rw [hqtt, Real.cos_pi_div_two, mul_zero, hfzero]
  · rw [hmzero, hfzero]
  · filter_upwards [Ioo_mem_nhds htt0 httpi] with t ht
    exact ⟨hlow t ⟨ht.1.le, ht.2.le⟩, hminor t⟩

end GKSharp

#print axioms GKSharp.cosine_support_of_arch
#print axioms GKSharp.cosine_minorant_of_arch
#print axioms GKSharp.cosine_tangent_derivative_of_arch

