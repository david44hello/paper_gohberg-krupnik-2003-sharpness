/-
GKSharp/Proofs/StripCornerPos.lean — the corner of the strip of paper 019 (sec5f_strip.tex l. 46-60,
calculation_certificates.tex l. 24): `g > 0` on `p ∈ [a0, b1]`, `0 < δ ≤ 1/20`, with the exact type of the draft
row `corner_positive` (PROVED-GIVEN the two corner Check Props, as hypotheses).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.StripAnalytic
import GKSharp.Proofs.StripCorner
import GKSharp.Proofs.ThresholdAlgebra

namespace GKSharp

open Set GKSharp.Threshold GKSharp.ComputerChecked GKSharp.Strip

theorem corner_positive_proved (hc : CheckCornerDerivatives) (ht : CheckCornerTails)
    (p delta s : ℝ) (hp : p ∈ Icc a0 b1) (ho : 0 ≤ omega p)
    (hd : delta ∈ Ioc (0 : ℝ) (1 / 20)) (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < g p delta s := by
  have hp1 : 1 < p := by
    have := hp.1
    unfold a0 at this
    linarith
  have hp2 : p < 2 := by
    have := hp.2
    unfold b1 at this
    linarith
  obtain ⟨hd0, hd1⟩ := hd
  obtain ⟨hlow, hhigh⟩ := ht p hp delta ⟨hd0.le, hd1⟩
  have htail := g_tail_bounds_proved p delta s hp1 hp2 ⟨hd0.le, by linarith⟩ hs
  by_cases hs1 : s ≤ 1 / 20
  · linarith [htail.1 hs1]
  by_cases hs2 : 19 / 20 ≤ s
  · linarith [htail.2 hs2]
  have hs1' : 1 / 20 < s := lt_of_not_ge hs1
  have hs2' : s < 19 / 20 := lt_of_not_ge hs2
  -- the coordinates `δ = 1 - e^{-η}`, `1 - sδ = e^{-ση}`
  have hl : 0 < 1 - delta := by linarith
  have hρ : 0 < 1 - s * delta := by nlinarith [hs.2]
  obtain ⟨eta, heta⟩ : ∃ e : ℝ, e = -Real.log (1 - delta) := ⟨_, rfl⟩
  have heta0 : 0 < eta := by
    rw [heta]
    linarith [Real.log_neg hl (by linarith)]
  have heta1 : eta ≤ eta1 := by
    rw [heta, eta1]
    linarith [Real.log_le_log (by norm_num) (show (19 / 20 : ℝ) ≤ 1 - delta by linarith)]
  have hexp_eta : Real.exp (-eta) = 1 - delta := by rw [heta, neg_neg, Real.exp_log hl]
  obtain ⟨sigma, hsig⟩ : ∃ t : ℝ, t = -Real.log (1 - s * delta) / eta := ⟨_, rfl⟩
  have hexp_sig : Real.exp (-(sigma * eta)) = 1 - s * delta := by
    rw [hsig, div_mul_cancel₀ _ heta0.ne', neg_neg, Real.exp_log hρ]
  have hsig0 : 0 < sigma := by
    rw [hsig]
    exact div_pos (by linarith [Real.log_neg hρ (by nlinarith [hs.1])]) heta0
  have hsig1 : sigma < 1 := by
    rw [hsig, div_lt_one heta0, heta]
    linarith [Real.log_lt_log hl (show 1 - delta < 1 - s * delta by nlinarith [hs.2])]
  have hdE : deltaEta eta = delta := by
    rw [deltaEta, hexp_eta]
    ring
  have hsE : sEta eta sigma = s := by
    rw [sEta_of_ne heta0.ne' hsig0.ne', hexp_sig, hexp_eta, sub_sub_cancel, sub_sub_cancel, mul_div_assoc,
      div_self hd0.ne', mul_one]
  -- the Taylor inference on the core `σ ∈ [0.045, 0.95]`
  obtain ⟨-, -, hcore⟩ := sigma_core_cover_proved eta sigma ⟨heta0.le, heta1⟩
    (by rw [hsE]; exact ⟨hs1'.le, hs2'.le⟩) ⟨hsig0, hsig1⟩
  obtain ⟨tau, htau, hc4, hm⟩ := hc p hp sigma hcore
  obtain ⟨xi, hxi, hT⟩ := etilde_taylor_proved p sigma eta hp1 hp2 ⟨hsig0, hsig1⟩ ⟨heta0, heta1⟩
  have hinit := (etilde_zero_minimum_proved p sigma hp1 hp2 ⟨hsig0, hsig1⟩).2
  have hpos : 0 < etilde p eta sigma :=
    corner_taylor_positive eta eta1 (etilde p eta sigma) (etilde p 0 sigma) (eTwo p sigma) (cFour p xi sigma) tau
      heta0 heta1 (by linarith) htau.1 (hc4 xi ⟨hxi.1.le, by linarith [hxi.2]⟩) hT hm
  -- back to `g = Ẽ · V`
  have hdl : deltaEta eta < 1 := by rw [hdE]; linarith
  have hV : 0 < vWeight p eta := by
    unfold vWeight
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (cDelta_props hp1 hdl).1 _)
  have hE : etilde p eta sigma = g p delta s / vWeight p eta := by rw [etilde, hdE, hsE]
  rw [hE] at hpos
  exact (div_pos_iff_of_pos_right hV).1 hpos

end GKSharp
