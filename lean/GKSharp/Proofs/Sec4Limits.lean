/- GKSharp/Proofs/Sec4Limits.lean - slice (b): endpoint divergence of Omega's first term, first axis zero.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v0.80, each as `<row>_proved` with the row's exact type.
- omegaFirst_endpoints (A:51-52): `ω₁ = p(a + s) · ((s(1-s))^q)⁻¹`; the first factor tends to `pa > 0` (at 0) or
  `p(a + 1) > 0` (at 1), the second to `+∞` since `(s(1-s))^q → 0⁺`.
- first_axis_zero_of (B:112): the zeros of `h` in `[0, λ_loc]` form a closed set (continuity), nonempty (intermediate
  value theorem, `h(0) > 0 > h(λ_loc)`), missing both end points; its infimum is its least element.
-/
import GKSharp.Defs.ThresholdAnalysis
import GKSharp.Proofs.Sec4aOmega

namespace GKSharp

open Set Filter GKSharp.Threshold
open scoped Topology

/-- `(s(1-s))^q → 0⁺` at an end point `e` of `(0, 1)`, approached from inside. -/
lemma sec4a_den_tendsto {p : ℝ} (hq : 0 < q p) {e : ℝ} {l : Filter ℝ} (hl : Tendsto id l (𝓝 e))
    (he : e * (1 - e) = 0) (hev : Ioo (0 : ℝ) 1 ∈ l) :
    Tendsto (fun s : ℝ => (s * (1 - s)) ^ q p) l (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc : Continuous fun s : ℝ => (s * (1 - s)) ^ q p :=
      (continuous_id.mul (continuous_const.sub continuous_id)).rpow_const fun _ => Or.inr hq.le
    have := (hc.tendsto e).comp hl
    simpa [he, Real.zero_rpow hq.ne'] using this
  · filter_upwards [hev] with s hs
    exact Real.rpow_pos_of_pos (mul_pos hs.1 (by linarith [hs.2])) _

/-- A:51-52, row `omegaFirst_endpoints`. -/
theorem omegaFirst_endpoints_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    Tendsto (omegaFirst p) (nhdsWithin 0 (Ioi 0)) atTop ∧
    Tendsto (omegaFirst p) (nhdsWithin 1 (Iio 1)) atTop := by
  have ha := sec4a_aConst_pos hp hp2
  have hp0 : 0 < p := by linarith
  have hq : 0 < q p := by unfold q; linarith
  have hω : omegaFirst p = fun s => p * (aConst p + s) * ((fun s : ℝ => (s * (1 - s)) ^ q p) s)⁻¹ := by
    funext s
    simp only [omegaFirst, div_eq_mul_inv]
  have hnum : ∀ (e : ℝ) (l : Filter ℝ), Tendsto id l (𝓝 e) →
      Tendsto (fun s => p * (aConst p + s)) l (𝓝 (p * (aConst p + e))) := fun e l hl =>
    ((continuous_const.mul (continuous_const.add continuous_id)).tendsto e).comp hl
  rw [hω]
  constructor
  · have hl : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    exact (hnum 0 _ hl).pos_mul_atTop (mul_pos hp0 (by linarith))
      (sec4a_den_tendsto hq hl (by ring) (Ioo_mem_nhdsGT one_pos)).inv_tendsto_nhdsGT_zero
  · have hl : Tendsto id (𝓝[<] (1 : ℝ)) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
    exact (hnum 1 _ hl).pos_mul_atTop (mul_pos hp0 (by linarith))
      (sec4a_den_tendsto hq hl (by ring) (Ioo_mem_nhdsLT one_pos)).inv_tendsto_nhdsGT_zero

/-- B:112, row `first_axis_zero_of`. -/
theorem first_axis_zero_of_proved (p : ℝ) (hpos : 0 < Threshold.h p 0) (hloc : 0 < lambdaLoc p)
    (hcont : ContinuousOn (Threshold.h p) (Icc 0 (lambdaLoc p))) (hedge : Threshold.h p (lambdaLoc p) < 0) :
    IsLeast (axisZeros p) (lambda0 p) ∧ 0 < lambda0 p ∧ lambda0 p < lambdaLoc p := by
  have hZ : axisZeros p = Icc 0 (lambdaLoc p) ∩ Threshold.h p ⁻¹' {0} := by
    ext x
    constructor
    · rintro ⟨h0, hL, hx⟩
      exact ⟨⟨h0.le, hL.le⟩, hx⟩
    · rintro ⟨⟨h0, hL⟩, hx⟩
      refine ⟨lt_of_le_of_ne h0 ?_, lt_of_le_of_ne hL ?_, hx⟩
      · rintro rfl
        have : Threshold.h p 0 = 0 := hx
        linarith
      · rintro rfl
        have : Threshold.h p (lambdaLoc p) = 0 := hx
        linarith
  have hclosed : IsClosed (axisZeros p) := by
    rw [hZ]
    exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hne : (axisZeros p).Nonempty := by
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hloc.le hcont ⟨hedge.le, hpos.le⟩
    exact ⟨c, by rw [hZ]; exact ⟨hc, hc0⟩⟩
  have hbdd : BddBelow (axisZeros p) := ⟨0, fun x hx => hx.1.le⟩
  have hmem : lambda0 p ∈ axisZeros p := hclosed.csInf_mem hne hbdd
  exact ⟨⟨hmem, fun x hx => csInf_le hbdd hx⟩, hmem.1, hmem.2.1⟩

end GKSharp
