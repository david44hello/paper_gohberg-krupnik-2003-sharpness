/- GKSharp/Proofs/Sec4Limsup.lean - slice (b): the printed limsup bound on the axis, epsilon form (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v1.30, each as `<row>_proved` with the row's exact type.
- sec4_limsup_axis (sec4a l.49): `obstacle(1 - δ, 0) = h(1 - δ) + K(1 - δ)` and `h(1 - δ) ≤ δ g(δ, s*)` (row h_le_delta_g,
  with the installed row cDelta_eq_gk), so `obstacle(1 - δ, 0)/δ ≤ g(δ, s*) + K(1 - δ)/δ`. As `δ → 0+`,
  `g(δ, s*) → g(0, s*) = ω₁(s*) - κ₀` (continuity, row g_zero) and `K(1 - δ)/δ → κ₀` (row near_identity_limits),
  so the right side tends to `ω₁(s*)` and is eventually `< ω₁(s*) + ε`. The direct witness route, no limsup object.
-/
import GKSharp.Proofs.Sec4Near

namespace GKSharp

open Set Filter GKSharp.Threshold
open scoped Topology

/-- sec4a_criterion.tex:49, row `sec4_limsup_axis`. -/
theorem sec4_limsup_axis_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ∀ eps > 0, ∀ᶠ delta in 𝓝[>] (0 : ℝ),
      Threshold.obstacle p (1 - delta) 0 / delta ≤ omegaFirst p (sStar p) + eps := by
  intro eps heps
  obtain ⟨⟨hs0, hs1⟩, -⟩ := sStar_spec_proved p hp hp2
  obtain ⟨-, -, hK⟩ := near_identity_limits_proved p hp hp2
  have hg : Tendsto (fun d => g p d (sStar p)) (𝓝[>] (0 : ℝ))
      (𝓝 (omegaFirst p (sStar p) - kappaZero p)) := by
    rw [← GKSharp.g_zero_proved p (sStar p) hp hp2]
    exact (sec4a_g_continuousAt hp (sStar p)).tendsto.mono_left nhdsWithin_le_nhds
  have hsum := hg.add hK
  rw [sub_add_cancel] at hsum
  have hev : ∀ᶠ d in 𝓝[>] (0 : ℝ), g p d (sStar p) + kConst p (1 - d) / d < omegaFirst p (sStar p) + eps :=
    (tendsto_order.1 hsum).2 _ (lt_add_of_pos_right _ heps)
  filter_upwards [hev, Ioo_mem_nhdsGT zero_lt_one] with d hlt hd
  have hle := h_le_delta_g_proved GKSharp.cDelta_eq_gk_proved p d (sStar p) hp hp2 hd ⟨hs0, hs1⟩
  have hob : Threshold.obstacle p (1 - d) 0 = Threshold.h p (1 - d) + kConst p (1 - d) := by
    simp only [Threshold.h, GKSharp.axisGap, Threshold.obstacle]
    ring
  have hhd : Threshold.h p (1 - d) / d ≤ g p d (sStar p) := by
    rw [div_le_iff₀ hd.1, mul_comm]
    exact hle
  rw [hob, add_div]
  linarith

end GKSharp
