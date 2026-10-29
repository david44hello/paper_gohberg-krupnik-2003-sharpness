/-
GKSharp/Proofs/StripCorner.lean — corner rows of paper 019 (sec5f_strip.tex l. 46-51): the value of `Ẽ` at `η = 0` and
its domination by `Ω`, with the exact type of the draft row `etilde_zero_minimum`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.StripLeaves
import GKSharp.Proofs.Sec4aOmega

namespace GKSharp

open Set GKSharp.Threshold GKSharp.Strip

theorem etilde_zero_minimum_proved (p sigma : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hs : sigma ∈ Ioo (0 : ℝ) 1) :
    etilde p 0 sigma = g p 0 sigma ∧ omega p ≤ etilde p 0 sigma := by
  have h0 : etilde p 0 sigma = g p 0 sigma := by
    have hd : deltaEta 0 = 0 := by simp [deltaEta]
    have hse : sEta 0 sigma = sigma := by simp [sEta, exprel]
    have hv : vWeight p 0 = 1 := by simp [vWeight, hd, cDelta_zero]
    rw [etilde, hd, hse, hv, div_one]
  refine ⟨h0, ?_⟩
  rw [h0, g_zero_proved p sigma hp hp2, omega]
  linarith [(sStar_spec_proved p hp hp2).2.2.2.1 sigma hs]

end GKSharp
