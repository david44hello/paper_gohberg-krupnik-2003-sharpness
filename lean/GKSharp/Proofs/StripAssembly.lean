/-
GKSharp/Proofs/StripAssembly.lean — the strip assembly of paper 019 (sec5f_strip.tex l. 38-40, 68):
rows `strip_h_positive` and `pc_lt_p0`, with the exact types of the statement draft.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Route: `δ = 1 - λ`; the strip cover puts `(p, δ)` in the corner (`g > 0` by the corner Taylor inference, using
`0 ≤ Ω(p)` on `[p0, 1.268]` from p0_spec) or in the bulk (`g > 0` by the bulk checks); then the attained minimum
gives `h(λ) = δ g(δ, s*) > 0`. For `pc < p0`: `pc < 1.213490305 < a0 < p0`.
-/
import GKSharp.Proofs.StripMinimum
import GKSharp.Proofs.StripCornerPos
import GKSharp.Proofs.Sec4aEndpoint
import GKSharp.Proofs.Sec4bChecks

namespace GKSharp

open Set GKSharp.Threshold GKSharp.ComputerChecked

/-- S:38–40, row `strip_h_positive`. -/
theorem strip_h_positive_proved (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hc : CheckCornerDerivatives) (ht : CheckCornerTails)
    (hb : CheckStripBulkMiddle) (hbt : CheckStripBulkTails)
    (p lam : ℝ) (hp : p ∈ Icc p0 (317 / 250)) (hlam : lam ∈ Ioo (0 : ℝ) 1) :
    0 < h p lam := by
  obtain ⟨-, ha0, -, -, -, hnonneg⟩ := p0_spec_proved hn hr
  have hp1 : 1 < p := by
    have := hp.1
    unfold a0 at ha0
    linarith
  have hp2 : p < 2 := by linarith [hp.2]
  have hd : 1 - lam ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hlam.2], by linarith [hlam.1]⟩
  have hg : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < g p (1 - lam) s := by
    intro s hs
    rcases strip_cover_proved p (1 - lam) hp ha0 hd with ⟨hpc, hdc⟩ | hbulk
    · exact corner_positive_proved hc ht p (1 - lam) s hpc (hnonneg p hp) hdc hs
    · exact bulk_positive_proved hb hbt p (1 - lam) s hbulk hs
  have hpos := h_positive_of_g_proved p (1 - lam) hp1 hp2 hd hg
  rwa [sub_sub_cancel] at hpos

/-- S:68, row `pc_lt_p0`. -/
theorem pc_lt_p0_proved (hn : CheckOmegaNeg) (hr : CheckOmegaRoot) (hc : CheckLocalF) : pc < p0 := by
  obtain ⟨-, hpc, -⟩ := pc_spec_proved hc
  obtain ⟨-, ha0, -⟩ := p0_spec_proved hn hr
  unfold a0 at ha0
  linarith [hpc.2]

end GKSharp
