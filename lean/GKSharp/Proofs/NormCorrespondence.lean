/- equality of the actual real-line and three circle norms, assembled from the two inequalities.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.RealLineFourier

namespace GKSharp.Proofs.NormCorrespondence

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

theorem norm_equalities_of_bounds (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β)
    (hforward : ‖pencil P α β‖ ≤ ‖T.map‖ ∧ functionNorm (circleMinus P α β) ≤ ‖T.map‖ ∧
      functionNorm (circleMid P α β) ≤ ‖T.map‖)
    (hreverse : ‖T.map‖ ≤ ‖pencil P α β‖ ∧ ‖T.map‖ ≤ functionNorm (circleMinus P α β) ∧
      ‖T.map‖ ≤ functionNorm (circleMid P α β)) :
    ‖pencil P α β‖ = functionNorm (circleMinus P α β) ∧
    ‖pencil P α β‖ = functionNorm (circleMid P α β) ∧
    ‖pencil P α β‖ = ‖T.map‖ := by
  have hpencil := le_antisymm hforward.1 hreverse.1
  have hminus := le_antisymm hreverse.2.1 hforward.2.1
  have hmid := le_antisymm hreverse.2.2 hforward.2.2
  exact ⟨hpencil.trans hminus, hpencil.trans hmid, hpencil⟩

theorem slice_N02_given
    (hN06 : ∀ (_hp : 1 < p) (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β),
      ‖pencil P α β‖ ≤ ‖T.map‖ ∧ functionNorm (circleMinus P α β) ≤ ‖T.map‖ ∧
        functionNorm (circleMid P α β) ≤ ‖T.map‖)
    (hN11 : ∀ (_hp : 1 < p) (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β),
      ‖T.map‖ ≤ ‖pencil P α β‖ ∧ ‖T.map‖ ≤ functionNorm (circleMinus P α β) ∧
        ‖T.map‖ ≤ functionNorm (circleMid P α β))
    (hp : 1 < p) (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β) :
    ‖pencil P α β‖ = functionNorm (circleMinus P α β) ∧
    ‖pencil P α β‖ = functionNorm (circleMid P α β) ∧
    ‖pencil P α β‖ = ‖T.map‖ :=
  norm_equalities_of_bounds P α β T (hN06 hp P α β T) (hN11 hp P α β T)

end GKSharp.Proofs.NormCorrespondence

#print axioms GKSharp.Proofs.NormCorrespondence.slice_N02_given
