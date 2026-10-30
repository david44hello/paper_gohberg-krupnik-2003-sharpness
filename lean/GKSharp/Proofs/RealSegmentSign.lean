/-
RealSegmentSign.lean — strict sign below the midpoint, Section5.3.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.MobiusDict

namespace GKSharp.Proofs.RealSegmentSign

theorem reduction_phi_neg_below_mid_proved {p C K lam ρ : ℝ}
    (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hρ0 : 0 < ρ) (hQ : 0 < (ρ - lam) * (1 - ρ))
    (hK : 0 ≤ K) (hρ1 : ρ ≤ (1 + lam) / 2) :
    -(1 - lam) ^ p * p * ρ ^ (p - 1) -
      K * (p / 2) * ((ρ - lam) * (1 - ρ)) ^ (p / 2 - 1) * (1 + lam - 2 * ρ) < 0 := by
  have hp : 0 < p := by linarith
  have first : 0 < (1 - lam) ^ p * p * ρ ^ (p - 1) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos (sub_pos.mpr hl1) p) hp)
      (Real.rpow_pos_of_pos hρ0 (p - 1))
  have second : 0 ≤ K * (p / 2) * ((ρ - lam) * (1 - ρ)) ^ (p / 2 - 1) * (1 + lam - 2 * ρ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hK (by linarith))
      (Real.rpow_nonneg hQ.le _)) (by linarith)
  linarith

end GKSharp.Proofs.RealSegmentSign

#print axioms GKSharp.Proofs.RealSegmentSign.reduction_phi_neg_below_mid_proved
