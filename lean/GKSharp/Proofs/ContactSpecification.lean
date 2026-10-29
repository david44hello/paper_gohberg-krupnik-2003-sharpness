/- GKSharp/Proofs/ContactSpecification.lean — complete actual contact data.
Frozen source: short_v0.70/sec4b_failure.tex:23–27; former v0.40:28–32.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactScalar
import GKSharp.Proofs.Sec4aArch
import GKSharp.Proofs.Sec4bContactDeriv

namespace GKSharp
open Threshold Set

/-- The whole contact_spec row, including actual Gamma derivatives. -/
theorem contact_spec_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    1 < rContact p lam ∧ |lam| < rContact p lam ∧ 0 < vContact p lam ∧
    rContact p lam + lam / rContact p lam = sigmaContact p lam ∧
    gammaGK p lam (yContact p lam) (theta p) = 0 ∧
    dy (gammaGK p lam) (yContact p lam) (theta p) = 0 ∧
    0 < dyy (gammaGK p lam) (yContact p lam) (theta p) := by
  obtain ⟨hr, habs, hv, hsum⟩ := contact_root_properties hp hp2 hlam
  have hvalue : gammaGK p lam (yContact p lam) (theta p) = 0 := by
    change GKSharp.gamma p (gk p lam) (lam : ℂ) (Real.log (rContact p lam)) (theta p) = 0
    exact sec4a_gamma_contact hp hp2 hlam rfl
  have hzero := sec4b_contact_dy_gammaGK_zero p lam hp hp2 hlam
  obtain ⟨_, _, _, _, _, hpositive⟩ := contact_derivative_values_proved p lam hp hp2 hlam
  exact ⟨hr, habs, hv, hsum, hvalue, hzero, hpositive⟩

end GKSharp

#print axioms GKSharp.contact_spec_proved

