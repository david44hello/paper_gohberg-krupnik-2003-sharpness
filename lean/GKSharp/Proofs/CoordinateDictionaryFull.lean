/- GKSharp/Proofs/CoordinateDictionaryFull.lean - slice (d): the full frozen coordinate dictionary (short v0.70).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
sec5d_monotone.tex l.11, 40, 58. The frozen slice (d) target strengthened the coordinate row by five identities;
sec5d_coordinate_dictionary_proved (MonotoneElementary) states the first six, and is kept unchanged because
MonotonePiPsi destructures it. The last five are field identities, valid since 2 - p ≠ 0 and 1 - p / 2 ≠ 0. -/
import GKSharp.Proofs.MonotoneElementary

namespace GKSharp

theorem sec5d_coordinate_dictionary_full_proved (p θ : ℝ) (hp : 1 < p ∧ p < 2)
    (hθ : 0 < θ ∧ θ < Real.pi) :
    1 < p / (2 - p) ∧
    0 < (1 - p / 2) * θ ∧
    (1 - p / 2) * θ < Real.pi / (p / (2 - p) + 1) ∧
    (p / (2 - p) + 1) * ((1 - p / 2) * θ) = θ ∧
    (p / (2 - p) - 1) * ((1 - p / 2) * θ) = (p - 1) * θ ∧
      (p - 1) = (p / (2 - p) - 1) / (p / (2 - p) + 1) ∧
    p / 2 * θ = (p / (2 - p)) * ((1 - p / 2) * θ) ∧
    p / (2 - p) = (p / 2) / (1 - p / 2) ∧
    (1 - (p - 1)) * θ = 2 * ((1 - p / 2) * θ) ∧
    θ / 2 + (p - 1) * (θ / 2) = p / 2 * θ ∧
    θ / 2 - (p - 1) * (θ / 2) = (1 - p / 2) * θ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sec5d_coordinate_dictionary_proved p θ hp hθ
  have hd : 2 - p ≠ 0 := (show (0 : ℝ) < 2 - p by linarith [hp.2]).ne'
  have hd2 : 1 - p / 2 ≠ 0 := (show (0 : ℝ) < 1 - p / 2 by linarith [hp.2]).ne'
  have hA : (2 - p) * (2 - p)⁻¹ = 1 := mul_inv_cancel₀ hd
  have hB : (1 - p / 2) * (1 - p / 2)⁻¹ = 1 := mul_inv_cancel₀ hd2
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, by ring, by ring, by ring⟩
  · linear_combination (-(p * θ / 2)) * hA
  · linear_combination (p / 2 * (1 - p / 2)⁻¹) * hA - (p * (2 - p)⁻¹) * hB

end GKSharp
