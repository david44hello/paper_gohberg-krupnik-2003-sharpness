/- GKSharp/Proofs/ContactDerivativeFull.lean — full printed contact derivative row O35.
Frozen source: short_v0.70/sec2_obstacle.tex:133–134; approved original O35 target.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactObstacleSmooth
import GKSharp.Proofs.ContactDtGamma
import GKSharp.Proofs.LemmaEContact

namespace GKSharp
open Threshold ContactCalc Set Filter
open scoped Topology ContDiff

/-- Full O35, with actual derivatives at log of the canonical matrix contact radius. -/
theorem slice_O35_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (lam : ℝ)
    (hlam : -1 ≤ lam ∧ lam < 1) :
    DifferentiableAt ℝ (GKSharp.obstacle p (gk p (lam : ℂ)) (lam : ℂ)) (Real.pi / p) ∧
    DifferentiableAt ℝ (fun t => GKSharp.gamma p (gk p (lam : ℂ)) (lam : ℂ)
      (Real.log (contactRadius p lam)) t) (Real.pi / p) ∧
    kConst p lam = -(deriv (fun t => GKSharp.gamma p (gk p (lam : ℂ)) (lam : ℂ)
      (Real.log (contactRadius p lam)) t) (Real.pi / p)) / (p / 2) ∧
    kConst p lam = -(deriv (GKSharp.obstacle p (gk p (lam : ℂ)) (lam : ℂ)) (Real.pi / p)) / (p / 2) := by
  have hfull := obstacle_smooth_contact_of_dt p lam hp hp2 hlam
    (fun hl => contact_dt_gamma p lam hp hp2 hl)
    (fun heq => by subst lam; exact endpoint_dt_gamma p hp hp2)
  obtain ⟨eps, heps, hreg, hobs⟩ := hfull
  have htheta : theta p ∈ Ioo (theta p - eps) (theta p + eps) := ⟨by linarith, by linarith⟩
  have hobsDiff : DifferentiableAt ℝ (Threshold.obstacle p lam) (theta p) :=
    (hreg.contDiffAt (isOpen_Ioo.mem_nhds htheta)).differentiableAt (by simp)
  let y := Real.log (contactRadius p lam)
  have hs := sec4a_sn_pos hp
  have hQ (c : ℝ) : 0 < Q c y (theta p) := by
    rw [Q_sos]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _)
      (sq_pos_of_pos (mul_pos (Real.exp_pos y) hs))
  have hG2 := ContactSmooth.gamma_contDiffAt p lam y (theta p) hp ⟨hQ 1, hQ lam⟩
  have hpair : ContDiffAt ℝ ω (fun t : ℝ => (t, y)) (theta p) :=
    contDiffAt_id.prodMk contDiffAt_const
  have hG : ContDiffAt ℝ ω (fun t => gammaGK p lam y t) (theta p) :=
    ContDiffAt.comp (theta p) (f := fun t : ℝ => (t, y))
      (g := fun u : ℝ × ℝ => gammaGK p lam u.2 u.1) hG2 hpair
  have hdt : dt (gammaGK p lam) y (theta p) = -q p * kConst p lam := by
    dsimp only [y]
    by_cases heq : lam = -1
    · subst lam
      rw [ContactLower.contactRadius_endpoint p hp hp2, Real.log_one]
      exact endpoint_dt_gamma p hp hp2
    · have hl : lam ∈ Ioo (-1 : ℝ) 1 := ⟨by by_contra hh; exact heq (by linarith [hlam.1]), hlam.2⟩
      rw [ContactLower.contactRadius_interior p lam hp hp2 hl]
      exact contact_dt_gamma p lam hp hp2 hl
  have hq : p / 2 ≠ 0 := by linarith
  refine ⟨hobsDiff, hG.differentiableAt (by simp), ?_, ?_⟩
  · apply (eq_div_iff hq).mpr
    change kConst p lam * (p / 2) = -dt (gammaGK p lam) y (theta p)
    rw [hdt]
    unfold q
    ring
  · apply (eq_div_iff hq).mpr
    change kConst p lam * (p / 2) = -deriv (Threshold.obstacle p lam) (theta p)
    rw [hobs]
    unfold q
    ring

end GKSharp

#print axioms GKSharp.contact_dt_gamma
#print axioms GKSharp.endpoint_dt_gamma
#print axioms GKSharp.slice_O35_proved
