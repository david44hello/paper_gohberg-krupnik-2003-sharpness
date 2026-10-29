/- GKSharp/Proofs/LocalConsequences.lean — full local failure and axis consequences of Q.
Frozen source: short_v0.70/sec4a_criterion.tex:40 and sec4b_failure.tex:12,17–22,108–109.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactOperator
import GKSharp.Proofs.PropositionQFull
import GKSharp.Proofs.Sec4Dual
import GKSharp.Proofs.Sec4Near
import GKSharp.Proofs.PencilDual
import GKSharp.Cited.HV2000

namespace GKSharp
open Threshold Set

theorem sec4_thm_L_proved (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) :
    1 < p → p < 2 → ∀ lam ∈ Ioo (0 : ℝ) 1,
      1 < localTest p lam → gk p lam < pencilNorm P lam := by
  intro hp hp2 lam hlam hlocal
  have hl : lam ∈ Ico (-1 : ℝ) 1 := ⟨by linarith [hlam.1], hlam.2⟩
  exact local_failure_of_cosine_criterion p P hp hp2 lam hlam hlocal
    (fun heq => (sec4_prop_Q_proved p P hp hp2 lam hl).1.mp heq)

theorem sec4_thm_L_dual_proved (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (P : RieszProjection p) (hp : 2 < p) :
    ∀ lam ∈ Ioo (0 : ℝ) 1, 1 < localTest p lam → gk p lam < pencilNorm P lam := by
  intro lam hlam htest
  have hp1 : 1 < p := by linarith
  letI := fact_conjExp hp1
  obtain ⟨Q, _⟩ := Cited.hv2000_riesz_norm (p / (p - 1)) (one_lt_conjExp hp1)
  have htest' : 1 < localTest (p / (p - 1)) lam := by
    change 1 < localTest (dual p) lam
    rw [(sec4_conditions_dual_proved p lam hp1).1]
    exact htest
  have hh := sec4_thm_L_proved (p / (p - 1)) Q (one_lt_conjExp hp1) (conjExp_lt_two hp) lam hlam htest'
  have hN : pencilNorm P (lam : ℂ) = pencilNorm Q (lam : ℂ) := by
    simpa only [Complex.star_def, Complex.conj_ofReal] using pencilNorm_dual hp1 P Q (lam : ℂ)
  rw [hN, ← gk_dual p hp1 (lam : ℂ)]
  exact hh

theorem sec4_axis_negative_fails_proved (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (P : RieszProjection p) (hp : 1 < p) (hp2 : p < 2) (lam : ℝ)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) (hh : h p lam < 0) : gk p lam < pencilNorm P lam := by
  have hge := gk_le_pencilNorm_real p P hp hp2 lam hlam
  by_contra hn
  have heq : pencilNorm P lam = gk p lam := le_antisymm (le_of_not_gt hn) hge
  have hminor := ((sec4_prop_Q_proved p P hp hp2 lam hlam).1.mp heq) 0
    ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
  simp only [abs_zero, mul_zero, Real.cos_zero, mul_one] at hminor
  change Threshold.obstacle p lam 0 - kConst p lam < 0 at hh
  linarith

theorem sec4_prop_F_proved (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) :
    1 < p → p < 2 → omega p < 0 →
      ∃ eps > 0, ∀ lam : ℝ, 1 - eps < lam → lam < 1 → gk p lam < pencilNorm P lam := by
  intro hp hp2 homega
  obtain ⟨eps, heps, hnegative⟩ := omega_negative_eventual_h_proved p hp hp2 homega
  refine ⟨min eps 1, lt_min heps zero_lt_one, ?_⟩
  intro lam hclose hlam
  have hclose' : 1 - eps < lam := by linarith [min_le_left eps 1]
  have h0 : 0 < lam := by linarith [min_le_right eps 1]
  exact sec4_axis_negative_fails_proved p P hp hp2 lam ⟨by linarith, hlam⟩ (hnegative lam hclose' hlam)

end GKSharp

#print axioms GKSharp.sec4_thm_L_proved
#print axioms GKSharp.sec4_thm_L_dual_proved
#print axioms GKSharp.sec4_axis_negative_fails_proved
#print axioms GKSharp.sec4_prop_F_proved
