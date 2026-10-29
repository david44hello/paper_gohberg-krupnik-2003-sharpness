/-
GKSharp/Proofs/TheoremCstar.lean — Theorem C*, short v0.70 P019_paper.tex l.137-140, proof sec5e_cstar.tex l.7-26: for
1 < p < 2 and 0 < λ < 1, ‖P₊ + λP₋‖_p = GK_p(λ) iff h(λ, p) ≥ 0 and λ < λ_loc(p). Assembly of the delivered inputs;
the inputs still open are explicit hypotheses of `thm_Cstar_of`: the slope K_f′(θ₀) < 0 (`KfSlopeHyp`, the second
conjunct of the row sec5e_Kf_slope) and h(λ_loc, p) < 0 for p < p_c (first conjunct of Proposition edge).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.Reduction
import GKSharp.Proofs.PropositionQFull
import GKSharp.Proofs.CstarCurve
import GKSharp.Proofs.CstarSegment
import GKSharp.Proofs.CstarKfBelow
import GKSharp.Proofs.LocalConsequences
import GKSharp.Proofs.CstarSlope

namespace GKSharp.Proofs.TheoremCstar

open GKSharp ComplexConjugate Filter Topology Set GKSharp.ComputerChecked

/-- "If" (l.12-23): `h ≥ 0` and `λ < λ_loc` give (*) on all of `ℂ`, so Proposition Q gives equality. -/
theorem cstar_if (slope : KfSlopeHyp) {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp1 : 1 < p) (hp2 : p < 2)
    (P : RieszProjection p) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (hh : kConst p lam ≤ obstacle p (gk p lam) lam 0) (hloc : lam < Threshold.lambdaLoc p) :
    pencilNorm P lam = gk p lam := by
  have hl : -1 ≤ lam := by linarith
  have hA2 := sec5_A2_proved hp1 hp2 hl hl1
  have hρ0 : 0 ≤ (1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) :=
    hA2.2.2.2.2.1
  have hA3 : ∀ ρ : ℝ, 0 < ρ → _ := fun ρ hρ =>
    Proofs.SharpA3.sec5_A3_of_A1_A2 hp1 hp2 hl hl1 hρ (sec5_A1_proved hp1 hp2 hl hl1 hρ) hA2
  have hzero := CstarCurve.sec5e_Lambda_zero_proved hp1 hp2 hl0 hl1
  dsimp only at hzero
  have hcurve := CstarCurve.cstar_curve_nonneg_proved hp1 hp2 hl0 hl1
    (sec5e_Kf_below_proved slope hp1 hp2 hl0 hl1 hh hloc).2 (hzero.2 hh)
  have hw := Proofs.Reduction.reduction_step3_nonneg_of (Proofs.Reduction.kConst_pos hp1 hp2 hl hl1)
    (fun ρ hgt => by
      have h := hA3 ρ (hρ0.trans_lt hgt)
      dsimp only at h
      obtain ⟨φc, -, θ, hθ, -, hpt, -, -, hmax⟩ := h.1 hgt
      exact ⟨φc, θ, hθ, hpt, hmax⟩)
    (fun ρ hρ hle hlam => by
      have h := hA3 ρ hρ
      dsimp only at h
      exact (h.2 hle hlam).2)
    hcurve (CstarSegment.cstar_real_segment_proved hp1 hp2 hl0 hl1 hh)
  exact (sec4_prop_Q_proved p P hp1 hp2 lam ⟨hl, hl1⟩).2.mpr
    (Proofs.Reduction.critD_nonneg_of_step3 hp1 hp2 hl hl1 hw)

/-- The slope K_f′(θ₀) < 0 (sec5e_cstar.tex l.12-15), from the proof of the row sec5e_Kf_slope. -/
theorem kf_slope : KfSlopeHyp := fun hp1 hp2 hl0 hl1 hh hloc =>
  (Proofs.CstarSlope.sec5e_Kf_slope_proved hp1 hp2 hl0 hl1 hh hloc).2

/-- "If" of Theorem C*, with every input proved: `h ≥ 0` and `λ < λ_loc` give `N_p(λ) = GK_p(λ)`. -/
theorem cstar_if_proved {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp1 : 1 < p) (hp2 : p < 2) (P : RieszProjection p)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (hh : kConst p lam ≤ obstacle p (gk p lam) lam 0) (hloc : lam < Threshold.lambdaLoc p) :
    pencilNorm P lam = gk p lam :=
  cstar_if kf_slope hp1 hp2 P hl0 hl1 hh hloc

/-- "Only if" (l.25-26): equality gives `h ≥ 0` (Proposition Q at the positive axis, `t = 0`), and `λ < λ_loc`
(`λ > λ_loc`: Theorem L; `λ = λ_loc < 1`: `h < 0` by Proposition edge; `p ≥ p_c`: `λ_loc = 1`). -/
theorem cstar_only_if (hc : CheckLocalF) {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp1 : 1 < p) (hp2 : p < 2)
    (P : RieszProjection p) (hedge : p < Threshold.pc → Threshold.h p (Threshold.lambdaLoc p) < 0)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (hN : pencilNorm P lam = gk p lam) :
    kConst p lam ≤ obstacle p (gk p lam) lam 0 ∧ lam < Threshold.lambdaLoc p := by
  have hQ := sec4_prop_Q_proved p P hp1 hp2 lam ⟨by linarith, hl1⟩
  have hK : kConst p lam ≤ obstacle p (gk p lam) lam 0 := by
    have h0 := (hQ.1.mp hN) 0 ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
    simpa [Threshold.obstacle] using h0
  refine ⟨hK, ?_⟩
  by_contra hge
  rw [not_lt] at hge
  rcases eq_or_lt_of_le hge with heq | hlt
  · rcases lt_or_ge p Threshold.pc with hpc | hpc
    · have hneg := hedge hpc
      rw [heq] at hneg
      simp only [Threshold.h, axisGap] at hneg
      linarith
    · have h1 := (lambdaLoc_spec_proved hc).2 p ⟨hpc, hp2⟩
      linarith
  · have hT := (local_threshold_iff_proved p lam hp1 hp2 ⟨hl0, hl1⟩).mpr hlt
    have hlt' := sec4_thm_L_proved p P hp1 hp2 lam ⟨hl0, hl1⟩ hT
    rw [hN] at hlt'
    exact lt_irrefl _ hlt'

/-- Theorem C* from the two open inputs (the slope and the edge value at `λ_loc`). -/
theorem thm_Cstar_of (slope : KfSlopeHyp) (hc : CheckLocalF)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp1 : 1 < p) (hp2 : p < 2) (P : RieszProjection p)
    (hedge : p < Threshold.pc → Threshold.h p (Threshold.lambdaLoc p) < 0)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    pencilNorm P lam = gk p lam ↔
      kConst p lam ≤ obstacle p (gk p lam) lam 0 ∧ lam < Threshold.lambdaLoc p :=
  ⟨cstar_only_if hc hp1 hp2 P hedge hl0 hl1, fun h => cstar_if slope hp1 hp2 P hl0 hl1 h.1 h.2⟩

end GKSharp.Proofs.TheoremCstar
