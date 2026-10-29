/- O23 (sec2_obstacle.tex l.81-85, short v0.40) assembled: part 1 = NearMinSelect.exists_near_min,
part 2 = Fejer.fejerMean_abs_le + Fejer.tendsto_of_lebesgue_point at the Lebesgue points of u. No cited input.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.NearMinSelect
import GKSharp.Proofs.FejerLimit
import GKSharp.Proofs.FejerLebesgue

namespace GKSharp

namespace SliceO23

open Real MeasureTheory Filter Topology

/-- The Lebesgue-point statement for bounded measurable `u` (Mathlib's Lebesgue differentiation theorem). -/
def LebesguePointAE : Prop :=
  ∀ {u : ℝ → ℝ}, Measurable u → ∀ {Y : ℝ}, (∀ t, |u t| ≤ Y) →
    ∀ᵐ t ∂(volume : Measure ℝ), Tendsto (fun r : ℝ => (∫ x in (-r)..r, |u (t - x) - u t|) / r) (𝓝[>] 0) (𝓝 0)

/-- O23 from the Lebesgue-point statement, with `fejerMean` = `Fejer.fejerMean` (the frozen body). -/
theorem slice_O23_of (hLeb : LebesguePointAE) {p : ℝ} (hp : 1 < p) (C : ℝ) (ρ : ℂ) (hC : max 1 ‖ρ‖ < C) :
    (∀ ε : ℝ, 0 < ε → ∃ (Y : ℝ) (u : ℝ → ℝ), 0 ≤ Y ∧ Measurable u ∧
      Function.Periodic u (2 * Real.pi) ∧ (∀ t, |u t| ≤ Y) ∧
      (∀ t, gamma p C ρ (u t) t < obstacle p C ρ t + ε)) ∧
    (∀ (u : ℝ → ℝ) (Y : ℝ), Measurable u → Function.Periodic u (2 * Real.pi) →
      (∀ t, |u t| ≤ Y) → (∀ N t, |Fejer.fejerMean u N t| ≤ Y) ∧
        ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))),
          Tendsto (fun N => Fejer.fejerMean u N t) atTop (𝓝 (u t))) := by
  refine ⟨fun ε hε => NearMinSelect.exists_near_min hp C ρ hC ε hε, fun u Y hu hper hY => ⟨?_, ?_⟩⟩
  · exact fun N t => Fejer.fejerMean_abs_le hu hY N t
  · refine ae_restrict_of_ae ?_
    filter_upwards [hLeb hu hY] with t ht
    exact Fejer.tendsto_of_lebesgue_point hu hper hY ht

/-- O23, sec2_obstacle.tex l.81-85 (v0.40), with `fejerMean` = `Fejer.fejerMean` (the frozen body). -/
theorem slice_O23_proved {p : ℝ} (hp : 1 < p) (C : ℝ) (ρ : ℂ) (hC : max 1 ‖ρ‖ < C) :
    (∀ ε : ℝ, 0 < ε → ∃ (Y : ℝ) (u : ℝ → ℝ), 0 ≤ Y ∧ Measurable u ∧
      Function.Periodic u (2 * Real.pi) ∧ (∀ t, |u t| ≤ Y) ∧
      (∀ t, gamma p C ρ (u t) t < obstacle p C ρ t + ε)) ∧
    (∀ (u : ℝ → ℝ) (Y : ℝ), Measurable u → Function.Periodic u (2 * Real.pi) →
      (∀ t, |u t| ≤ Y) → (∀ N t, |Fejer.fejerMean u N t| ≤ Y) ∧
        ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))),
          Tendsto (fun N => Fejer.fejerMean u N t) atTop (𝓝 (u t))) :=
  slice_O23_of (fun {_u} hu {_Y} hY => FejerLebesgue.lebesgue_point_ae hu hY) hp C ρ hC

end SliceO23

end GKSharp
