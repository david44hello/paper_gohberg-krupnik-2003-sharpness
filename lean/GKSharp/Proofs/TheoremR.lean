/- finite angular profile and full Theorem R for the actual complex projection pencil.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.HomogeneousFiniteCore
import GKSharp.Proofs.SectorGK
import GKSharp.Proofs.TheoremRIf
import GKSharp.Proofs.NormDisc
import GKSharp.Proofs.ColeEnvelope
import GKSharp.Proofs.PencilModes

open Real Set Filter Topology
namespace GKSharp

/-- Corrected O27 on the paper's standing range q=p/2>1/2, with no continuity or finiteness premise. -/
theorem slice_O27_proved (q : ℝ) (hq : 1 / 2 < q) (V : ℂ → EReal) (hV : IsSubharmonic V)
    (h0 : 0 ≤ V 0)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z) :
    (∀ t : ℝ, V (unitPoint t) ≠ ⊥) ∧ ∃ phi : ℝ → ℝ, Continuous phi ∧ QSubtrig q phi ∧
      ∀ z : ℂ, V z = (angularPotential q phi z : EReal) := by
  have hq0 : 0 < q := by linarith
  have hVOn : IsSubharmonicOn ({0}ᶜ : Set ℂ) V :=
    ⟨fun z _ => hV.1 z, hV.2.1.upperSemicontinuousOn _, fun n c r hr _ => hV.2.2 n c r hr⟩
  have hCmp : ProfileCore.AngularComparison q V := by
    intro x y a b hxy hlen ha hb t ht ht'
    exact SectorGK.sector_comparison_punct hq hVOn (fun r z hr _ => hhom r z hr) hxy hlen ha hb t ht ht'
  have hfin := ProfileCore.homogeneous_finite_of_comparison hq0 hV h0 hhom hCmp
  obtain ⟨phi, hphi, hrep, _⟩ := ProfileCore.profile_of_comparison hq0 hV h0 hhom hCmp
  exact ⟨hfin, phi, SectorGK.qsubtrig_continuous hq hphi, hphi, hrep⟩

theorem periodic_arg_unitPoint {phi : ℝ → ℝ} (hper : Function.Periodic phi (2 * π)) (t : ℝ) :
    phi (Complex.arg (unitPoint t)) = phi t := by
  rw [unitPoint, Complex.arg_exp_mul_I, toIocMod]
  have h := hper.int_mul (-toIocDiv Real.two_pi_pos (-π) t) t
  simpa [zsmul_eq_mul, sub_eq_add_neg] using h

theorem angularPotential_unitPoint (q : ℝ) {phi : ℝ → ℝ}
    (hper : Function.Periodic phi (2 * π)) (t : ℝ) : angularPotential q phi (unitPoint t) = phi t := by
  unfold angularPotential
  rw [norm_unitPoint, one_rpow, one_mul, periodic_arg_unitPoint hper t]

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- Theorem R only-if, every complex ratio and every p>1; only the exact Cole existence input is cited. -/
theorem thmR_only_if (hp : 1 < p) (P : RieszProjection p) (rho : ℂ) {C : ℝ}
    (hC : max 1 ‖rho‖ < C) (hbound : pencilNorm P rho ≤ C) :
    ∃ phi : ℝ → ℝ, QSubtrig (p / 2) phi ∧ ∀ t, phi t ≤ obstacle p C rho t := by
  obtain ⟨hMc, _, hdisc⟩ := slice_O24_proved hp P C rho hC hbound
  obtain ⟨V, hV, hVM, h0, hhom, _⟩ := slice_O26_proved (p / 2) (homogeneousObstacle p C rho) hMc
    (fun r hr z => PotentialCoordinates.homogeneousObstacle_homogeneous p C rho r hr z) hdisc
  obtain ⟨_, phi, _, hphi, hrep⟩ := slice_O27_proved (p / 2) (by linarith) V hV h0 hhom
  refine ⟨phi, hphi, fun t => ?_⟩
  have h := hVM (unitPoint t)
  rw [hrep] at h
  change (angularPotential (p / 2) phi (unitPoint t) : EReal) ≤
    (angularPotential (p / 2) (obstacle p C rho) (unitPoint t) : EReal) at h
  rw [angularPotential_unitPoint _ hphi.1, angularPotential_unitPoint _ (obstacle_periodic p C rho)] at h
  exact EReal.coe_le_coe_iff.mp h

/-- The complete all-p, all-complex-ratio equivalence in Theorem R. -/
theorem thmR_iff (hp : 1 < p) (P : RieszProjection p) (rho : ℂ) (C : ℝ)
    (hC : max 1 ‖rho‖ < C) :
    pencilNorm P rho ≤ C ↔ ∃ phi : ℝ → ℝ, QSubtrig (p / 2) phi ∧ ∀ t, phi t ≤ obstacle p C rho t :=
  ⟨thmR_only_if hp P rho hC, TheoremRIf.thmR_if hp P rho hC⟩

/-- O28: exact real-infimum assembly, including N=max(1,normrho). -/
theorem slice_O28_proved (P : RieszProjection p) (rho : ℂ)
    (hlo : max 1 ‖rho‖ ≤ pencilNorm P rho)
    (hiff : ∀ C : ℝ, max 1 ‖rho‖ < C → (pencilNorm P rho ≤ C ↔
      ∃ phi : ℝ → ℝ, QSubtrig (p / 2) phi ∧ ∀ t, phi t ≤ obstacle p C rho t)) :
    pencilNorm P rho = sInf {C : ℝ | max 1 ‖rho‖ < C ∧ ∃ phi : ℝ → ℝ,
      QSubtrig (p / 2) phi ∧ ∀ t, phi t ≤ obstacle p C rho t} := by
  let S : Set ℝ := {C : ℝ | max 1 ‖rho‖ < C ∧ ∃ phi : ℝ → ℝ,
    QSubtrig (p / 2) phi ∧ ∀ t, phi t ≤ obstacle p C rho t}
  have hlow : ∀ C ∈ S, pencilNorm P rho ≤ C := fun C h => (hiff C h.1).mpr h.2
  have hmem : ∀ eps : ℝ, 0 < eps → pencilNorm P rho + eps ∈ S := by
    intro eps heps
    have hstrict : max 1 ‖rho‖ < pencilNorm P rho + eps := by linarith
    exact ⟨hstrict, (hiff _ hstrict).mp (by linarith)⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hb : BddBelow S := ⟨pencilNorm P rho, hlow⟩
  apply le_antisymm (le_csInf hne hlow)
  apply le_of_forall_pos_le_add
  intro eps heps
  exact csInf_le hb (hmem eps heps)

/-- Full corrected O18: equivalence and exact infimum formula, with no missing internal analytic premise. -/
theorem slice_O18_proved (hp : 1 < p) (P : RieszProjection p) (rho : ℂ) (C : ℝ)
    (hC : max 1 ‖rho‖ < C) :
    (pencilNorm P rho ≤ C ↔ ∃ phi : ℝ → ℝ, QSubtrig (p / 2) phi ∧ ∀ t, phi t ≤ obstacle p C rho t) ∧
    pencilNorm P rho = sInf {D : ℝ | max 1 ‖rho‖ < D ∧ ∃ phi : ℝ → ℝ,
      QSubtrig (p / 2) phi ∧ ∀ t, phi t ≤ obstacle p D rho t} :=
  ⟨thmR_iff hp P rho C hC,
    slice_O28_proved P rho (max_one_le_pencilNorm P rho) (fun D hD => thmR_iff hp P rho D hD)⟩

end GKSharp

#print axioms GKSharp.slice_O27_proved
#print axioms GKSharp.thmR_only_if
#print axioms GKSharp.slice_O28_proved
#print axioms GKSharp.slice_O18_proved
