/- GKSharp/Proofs/ContactNegativePair.lean — negative symmetric obstacle pair.
Frozen source: short_v0.70/sec4b_failure.tex:31–32.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactEnvelope
import GKSharp.Proofs.SymmetricTaylor

namespace GKSharp
open Threshold Set Filter
open scoped Topology ContDiff

/-- Negative Schur curvature produces the actual symmetric negative obstacle pair. -/
theorem negative_pair_of_muSecond_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) (hmu : muSecond p lam < 0) :
    ∃ eps > 0, ∀ s ∈ Ioo (0 : ℝ) eps,
      Threshold.obstacle p lam (theta p - s) + Threshold.obstacle p lam (theta p + s) < 0 := by
  obtain ⟨branch, radius, hradius, hpoint, hb, hstat, hcurv⟩ := contact_envelope_proved p lam hp hp2 hlam
  let mu : ℝ → ℝ := fun t => gammaGK p lam (branch t) t
  have ht : theta p ∈ Ioo (theta p - radius) (theta p + radius) := ⟨by linarith, by linarith⟩
  have hba : ContDiffAt ℝ ∞ branch (theta p) := hb.contDiffAt (isOpen_Ioo.mem_nhds ht)
  have hf := ContactSmooth.gamma_contDiffAt p lam _ _ hp
    (ContactSmooth.contact_positiveBases p lam hp hp2 hlam)
  have hma : ContDiffAt ℝ 4 mu (theta p) := by
    have hf' : ContDiffAt ℝ 4 (fun u : ℝ × ℝ => gammaGK p lam u.2 u.1)
        (theta p, branch (theta p)) := by simpa only [hpoint] using hf.of_le (show (4 : ℕ∞ω) ≤ ω by simp)
    exact hf'.comp (theta p) (contDiffAt_id.prodMk (hba.of_le (by norm_num)))
  have hm0 : mu (theta p) = 0 := by
    dsimp only [mu]
    rw [hpoint]
    exact (contact_spec_proved p lam hp hp2 hlam).2.2.2.2.1
  obtain ⟨B, hB, delta, hdelta, hTaylor⟩ := symmetric_taylor_four_proved mu (theta p) hma hm0
  let eps : ℝ := min radius (min delta (min 1 (-muSecond p lam / B)))
  have heps : 0 < eps := lt_min hradius (lt_min hdelta (lt_min zero_lt_one (div_pos (by linarith) hB)))
  refine ⟨eps, heps, ?_⟩
  intro s hs
  have hs0 := hs.1
  have hsr : s < radius := hs.2.trans_le (min_le_left _ _)
  have hsd : s < delta := hs.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs1 : s < 1 := hs.2.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsq : s < -muSecond p lam / B := hs.2.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hq : B * s ^ 2 < -muSecond p lam := by
    have hs2 : s ^ 2 < s := by nlinarith
    have h1 := mul_lt_mul_of_pos_left hs2 hB
    have h2 := (lt_div_iff₀ hB).mp hsq
    nlinarith
  have hbound := hTaylor s ⟨by linarith, hsd⟩
  change |mu (theta p - s) + mu (theta p + s) -
    deriv (deriv mu) (theta p) * s ^ 2| ≤ B * s ^ 4 at hbound
  change deriv (deriv mu) (theta p) = muSecond p lam at hcurv
  rw [hcurv] at hbound
  have hnegative : mu (theta p - s) + mu (theta p + s) < 0 := by
    have hh := (le_abs_self _).trans hbound
    have hproduct : (muSecond p lam + B * s ^ 2) * s ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hs0)
    nlinarith
  have hm := (hstat (theta p - s) ⟨by linarith, by linarith⟩).2
  have hp' := (hstat (theta p + s) ⟨by linarith, by linarith⟩).2
  exact lt_of_le_of_lt (add_le_add hm hp') hnegative

end GKSharp

#print axioms GKSharp.negative_pair_of_muSecond_proved

