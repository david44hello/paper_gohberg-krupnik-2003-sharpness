/-
GKSharp/Proofs/StripCriterion.lean — the strip criterion, sec5f_strip.tex l.12-13 (short v0.70): "By Theorem C*, for
p ≥ p_c (where λ_loc = 1) the bound is sharp at λ ∈ (0,1) exactly when h(λ, p) = m_GK(0) − K ≥ 0". Theorem C*
(`thm_Cstar_of` with the proved slope) at λ_loc(p) = 1 (`lambdaLoc_spec_proved`); its edge input is empty for p ≥ p_c.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.TheoremCstar
import GKSharp.Proofs.Sec4bChecks

namespace GKSharp.Proofs.StripCriterion

open GKSharp GKSharp.ComputerChecked

/-- For `p_c ≤ p < 2` and `0 < λ < 1`: `‖P₊ + λP₋‖_p = GK_p(λ)` iff `h(λ, p) ≥ 0`, given `CheckLocalF`. -/
theorem sec5_strip_criterion_proved (hc : CheckLocalF) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p)
    (hp : Threshold.pc ≤ p) (hp2 : p < 2) (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) :
    pencilNorm P lam = gk p lam ↔ 0 ≤ Threshold.h p lam := by
  have hpc := (GKSharp.pc_spec_proved hc).2.1.1
  have hp1 : 1 < p := by linarith
  have hloc : Threshold.lambdaLoc p = 1 := (GKSharp.lambdaLoc_spec_proved hc).2 p ⟨hp, hp2⟩
  rw [TheoremCstar.thm_Cstar_of TheoremCstar.kf_slope hc hp1 hp2 P (fun hlt => absurd hp (not_le.mpr hlt))
    hlam.1 hlam.2, hloc]
  unfold Threshold.h GKSharp.axisGap
  constructor
  · rintro ⟨hK, -⟩
    linarith
  · intro hh
    exact ⟨by linarith, hlam.2⟩

end GKSharp.Proofs.StripCriterion
