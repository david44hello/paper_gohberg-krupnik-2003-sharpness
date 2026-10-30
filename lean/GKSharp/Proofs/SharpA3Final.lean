/-
SharpA3Final.lean — Section5 (A3), final dependency assembly.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.SharpA3
import GKSharp.Proofs.A1
import GKSharp.Proofs.SharpA2

namespace GKSharp

open ComplexConjugate Filter Topology
open GKSharp.Proofs.SharpA3

theorem sec5_A3_proved {p lam ρ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) (hρ : 0 < ρ) :
    let r0 := curveRoot lam (1 - p / 2) (p / 2)
    let ρ0 := (1 + lam * r0) / (1 + r0)
    (ρ0 < ρ → ∃ φc ∈ Set.Ioo 0 Real.pi, ∃ θ ∈ Set.Ioo 0 Real.pi,
      rhoCurve p lam θ = ρ ∧ (ρ : ℂ) * Complex.exp ((φc : ℂ) * Complex.I) = mobW lam (curveZ p lam θ) ∧
      (∀ φ ∈ Set.Ioo 0 φc, 0 < deriv (fun x => fRho p lam ρ x) φ) ∧
      (∀ φ ∈ Set.Ioo φc Real.pi, deriv (fun x => fRho p lam ρ x) φ < 0) ∧
      ∀ φ ∈ Set.Icc 0 Real.pi, φ ≠ φc → fRho p lam ρ φ < fRho p lam ρ φc) ∧
    (ρ ≤ ρ0 → (0 < lam → Real.sqrt lam ≤ ρ) →
      (MonotoneOn (fun x => fRho p lam ρ x) (Set.Icc 0 Real.pi) ∨
        AntitoneOn (fun x => fRho p lam ρ x) (Set.Icc 0 Real.pi)) ∧
      ∀ φ ∈ Set.Icc 0 Real.pi, fRho p lam ρ φ ≤ fRho p lam ρ 0) :=
  GKSharp.Proofs.SharpA3.sec5_A3_of_A1_A2 hp1 hp2 hl hl1 hρ
    (GKSharp.sec5_A1_proved hp1 hp2 hl hl1 hρ) (GKSharp.sec5_A2_proved hp1 hp2 hl hl1)

end GKSharp

#print axioms GKSharp.sec5_A3_proved
