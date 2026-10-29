/- literal determinant identity, frozen short v0.70 sec5d:28.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotonePartials
import GKSharp.Proofs.MonotoneDetAlgebra

namespace GKSharp

theorem sec5d_E_identity_proved {p θ g : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2) (hga : g ≠ θ / 2) :
    2 * Real.sin θ * Real.sin ((p - 1) * θ) * monoE p (θ / 2) g * monoS p (θ / 2) g =
      monoPi (p - 1) θ (Real.cos (2 * g)) := by
  let a := θ / 2
  let b := (p - 1) * a
  have hab : 0 < b ∧ b < a ∧ a < Real.pi / 2 := by
    dsimp [a,b]
    refine ⟨mul_pos (by linarith) (half_pos hθ0), ?_, by linarith⟩
    nlinarith
  have hg' : b < g ∧ g < Real.pi / 2 := hg
  have hg0 : 0 < g := lt_trans hab.1 hg'.1
  obtain ⟨hpb,hpa,hmb,-,-⟩ := sec5d_gamma_denominators_proved a b g hab hg'
  have hma : Real.sin (g - a) ≠ 0 := by
    have hh := Real.sin_eq_zero_iff_of_lt_of_lt (x := g - a)
      (by linarith [hab.2.2,Real.pi_pos]) (by linarith [hg'.2,hab.1,hab.2.1,Real.pi_pos])
    exact fun hz => hga (sub_eq_zero.mp (hh.mp hz))
  have hθeq : θ = 2 * a := by dsimp [a]; ring
  have hεeq : (p - 1) * θ = 2 * b := by dsimp [a,b]; ring
  have hueq : (1 - (p - 1)) * θ = 2 * (a - b) := by dsimp [a,b]; ring
  have h2a : Real.sin (2 * a) ≠ 0 := by
    rw [← hθeq]
    exact (Real.sin_pos_of_pos_of_lt_pi hθ0 hθ).ne'
  have h2b : Real.sin (2 * b) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hab.1]) (by linarith [hab.2.1,hab.2.2])).ne'
  obtain ⟨hLa,hLg,hMa,hMg⟩ := mono_log_partials p a g hma hpa.ne' hmb.ne' hpb.ne' h2a h2b
  have halg := determinant_trigonometric (p - 1) a b g hma hpa.ne' hmb.ne' hpb.ne' h2a h2b
  rw [show (p - 1) + 1 = p by ring] at halg
  change 2 * Real.sin θ * Real.sin ((p - 1) * θ) * monoE p a g * monoS p a g = _
  unfold monoE monoS monoPi
  rw [hLa.deriv,hLg.deriv,hMa.deriv,hMg.deriv,hεeq,hueq,hθeq]
  exact halg

end GKSharp
