/- GKSharp/Proofs/PropS.lean - Proposition S (the strip), sec5f_strip.tex l.38-40 and l.67-68: h > 0 on the strip
(installed strip_h_positive) and, for p0 ≤ p < 3 - √3, ‖P₊ + λP₋‖_p = GK_p(λ) for every real λ (Theorem C* "if" half
for λ ∈ (0, 1) with λ_loc = 1 as p_c < p0; Theorem C1 for λ ∈ [-1, 0]; λ = 1; the symmetry λ ↦ 1/λ).
20261028.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.StripAssembly
import GKSharp.Proofs.Sec4bChecks
import GKSharp.Proofs.TheoremC1
import GKSharp.Proofs.GKSymm
import GKSharp.Proofs.PencilSymm
import GKSharp.Proofs.NormReduce

namespace GKSharp.PropS

open Set GKSharp.Threshold GKSharp.ComputerChecked

/-- The "if" half of Theorem C* (sec5e_cstar.tex l.12-23) in the exact form of `cstar_if` without its open slope input:
`h ≥ 0` (as `K ≤ m_C(0)`) and `λ < λ_loc` give `‖P₊ + λP₋‖_p = GK_p(λ)` for `1 < p < 2`, `0 < λ < 1`. -/
def CstarIf : Prop :=
  ∀ {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)], 1 < p → p < 2 → ∀ (P : RieszProjection p) {lam : ℝ}, 0 < lam → lam < 1 →
    kConst p lam ≤ GKSharp.obstacle p (gk p lam) lam 0 → lam < Threshold.lambdaLoc p → pencilNorm P lam = gk p lam

/-- sec5f_strip.tex l.67 (`strip_endpoint_compare`): `3 - √3 < 1.268`, as `1.732² < 3`. -/
theorem endpoint_lt : 3 - Real.sqrt 3 < (317 / 250 : ℝ) := by
  have h : (433 / 250 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  linarith

/-- The operator half (sec5f_strip.tex l.67-68) on the strip `p0 ≤ p < 3 - √3`: `λ ∈ (0, 1)` by C* "if" with
`h > 0` (strip_h_positive) and `λ_loc = 1` (`p_c < p0`); `λ ∈ [-1, 0]` by C1; `λ = 1` trivially; `|λ| > 1` by
`N_p(λ) = |λ| N_p(1/λ)` and `GK_p(λ) = |λ| GK_p(1/λ)`. -/
theorem operator_of_cstarIf (hCif : CstarIf) (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hcd : CheckCornerDerivatives) (hct : CheckCornerTails) (hbm : CheckStripBulkMiddle)
    (hbt : CheckStripBulkTails) (hc : CheckLocalF) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p)
    (hp : p ∈ Ico p0 (3 - Real.sqrt 3)) (lam : ℝ) : pencilNorm P lam = gk p lam := by
  obtain ⟨-, ha0, -⟩ := p0_spec_proved hn hr
  unfold a0 at ha0
  have hend := endpoint_lt
  have hp1 : 1 < p := by linarith [hp.1]
  have hp2 : p < 2 := by linarith [hp.2]
  have hloc : lambdaLoc p = 1 :=
    (lambdaLoc_spec_proved hc).2 p ⟨((pc_lt_p0_proved hn hr hc).trans_le hp.1).le, hp2⟩
  have hmid : ∀ μ : ℝ, 0 < μ → μ < 1 → pencilNorm P μ = gk p μ := by
    intro μ h0 h1
    have hh := strip_h_positive_proved hn hr hcd hct hbm hbt p μ ⟨hp.1, by linarith [hp.2]⟩ ⟨h0, h1⟩
    unfold Threshold.h GKSharp.axisGap at hh
    exact hCif hp1 hp2 P h0 h1 (by linarith) (by rw [hloc]; exact h1)
  have hneg : ∀ μ : ℝ, -1 ≤ μ → μ ≤ 0 → pencilNorm P μ = gk p μ := fun μ hm h0 =>
    GKSharp.Proofs.TheoremC1.thm_C1_lt_two_of_onevar GKSharp.Proofs.TheoremC1.onevar_hyp hp1 hp2 P hm h0
  have hinv : ∀ μ : ℝ, μ ≠ 0 → pencilNorm P (1 / μ : ℝ) = gk p (1 / μ : ℝ) → pencilNorm P μ = gk p μ := by
    intro μ hμ heq
    have hne : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ
    rw [pencilNorm_inv P _ hne, gk_inv p hne]
    have e : (1 : ℂ) / (μ : ℂ) = ((1 / μ : ℝ) : ℂ) := by push_cast; ring
    rw [e, heq]
  rcases lt_trichotomy lam 1 with hl | rfl | hl
  · rcases le_or_gt lam 0 with h0 | h0
    · rcases le_or_gt (-1) lam with hm | hm
      · exact hneg lam hm h0
      · have hl0 : lam < 0 := by linarith
        refine hinv lam hl0.ne (hneg _ ?_ (one_div_neg.mpr hl0).le)
        rw [le_div_iff_of_neg hl0]
        linarith
    · exact hmid lam h0 hl
  · rw [Complex.ofReal_one, pencilNorm_one, gk_one]
  · have hl0 : 0 < lam := by linarith
    exact hinv lam hl0.ne' (hmid _ (one_div_pos.mpr hl0) ((div_lt_one hl0).mpr hl))

/-- Proposition S (sec5f_strip.tex l.38-40), the row `sec5_prop_S` with its seven explicit checks (six strip checks and
`CheckLocalF` for `λ_loc = 1`), from the C* "if" half as an explicit input (`CstarIf`). -/
theorem sec5_prop_S_of_cstarIf (hCif : CstarIf) (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hcd : CheckCornerDerivatives) (hct : CheckCornerTails) (hbm : CheckStripBulkMiddle)
    (hbt : CheckStripBulkTails) (hc : CheckLocalF) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) :
    (p ∈ Icc p0 (317 / 250 : ℝ) → ∀ lam ∈ Ioo (0 : ℝ) 1, 0 < h p lam) ∧
    (p ∈ Ico p0 (3 - Real.sqrt 3) → ∀ lam : ℝ, pencilNorm P lam = gk p lam) :=
  ⟨fun hp lam hlam => strip_h_positive_proved hn hr hcd hct hbm hbt p lam hp hlam,
    fun hp lam => operator_of_cstarIf hCif hn hr hcd hct hbm hbt hc p P hp lam⟩

end GKSharp.PropS
