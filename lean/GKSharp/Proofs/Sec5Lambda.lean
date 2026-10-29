/-
Sec5Lambda.lean — the normalized critical-curve identity, project 019, Section 5.2.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.MobiusDict

namespace GKSharp.Proofs.Sec5Lambda

open GKSharp

lemma normalized_dictionary (p C K lam : ℝ) (hl1 : lam < 1) {z : ℂ} (hz : z ≠ -1) :
    mobPhi p C K lam (mobW lam z) / (1 - lam) ^ p =
      C ^ p - ‖mobW lam z‖ ^ p - K * reQPow z (p / 2) / ‖1 + z‖ ^ p ∧
    mobPhi p C K lam (mobW lam z) / (1 - lam) ^ p = critD p C K lam z / ‖1 + z‖ ^ p := by
  have positive : 0 < (1 - lam) ^ p := Real.rpow_pos_of_pos (by linarith) p
  have norm_positive : 0 < ‖(1 : ℂ) + z‖ ^ p :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (GKSharp.one_add_ne_zero hz)) p
  constructor
  · rw [mobPhi, GKSharp.reQPow_mobQ p hl1 hz]
    field_simp
    <;> ring
  · rw [GKSharp.critD_eq_mobPhi p C K hl1 hz]
    field_simp

theorem sec5_Lambda_proved {p C K lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    mobPhi p C K lam (mobW lam (curveZ p lam θ)) / (1 - lam) ^ p =
        C ^ p - ‖mobW lam (curveZ p lam θ)‖ ^ p -
          K * reQPow (curveZ p lam θ) (p / 2) / ‖1 + curveZ p lam θ‖ ^ p ∧
    mobPhi p C K lam (mobW lam (curveZ p lam θ)) / (1 - lam) ^ p =
        critD p C K lam (curveZ p lam θ) / ‖1 + curveZ p lam θ‖ ^ p := by
  have radius := (GKSharp.curve_root_formula hp1 hp2 hθ0 hθ hl hl1).2.2.1
  have nonzero : (1 : ℂ) + curveZ p lam θ ≠ 0 :=
    GKSharp.polar_one_add_ne_zero radius hθ0 hθ
  have pole : curveZ p lam θ ≠ -1 := by
    intro equal
    apply nonzero
    rw [equal]
    ring
  exact normalized_dictionary p C K lam hl1 pole

end GKSharp.Proofs.Sec5Lambda

#print axioms GKSharp.Proofs.Sec5Lambda.sec5_Lambda_proved
