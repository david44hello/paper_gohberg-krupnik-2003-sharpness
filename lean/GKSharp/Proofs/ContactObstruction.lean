/- GKSharp/Proofs/ContactObstruction.lean — the local obstruction to the cosine criterion.
Frozen source: short_v0.70/sec4b_failure.tex:31–32.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactNegativePair
import GKSharp.Proofs.ContactSign

namespace GKSharp
open Threshold Set

/-- Analytic obstruction used to turn Proposition Q into strict operator failure. -/
theorem negative_pair_excludes_cosine_minorant (p lam KK : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) (hmu : muSecond p lam < 0) :
    ¬ ∀ t ∈ Icc (-Real.pi) Real.pi,
      KK * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t := by
  intro hminor
  obtain ⟨eps, heps, hnegative⟩ := negative_pair_of_muSecond_proved p lam hp hp2 hlam hmu
  have ht0 : 0 < theta p := div_pos Real.pi_pos (by linarith)
  have htpi : theta p < Real.pi := div_lt_self Real.pi_pos hp
  let rr := min eps (min (theta p) (Real.pi - theta p))
  have hr : 0 < rr := lt_min heps (lt_min ht0 (by linarith))
  have hre : rr ≤ eps := min_le_left _ _
  have hrt : rr ≤ theta p := (min_le_right _ _).trans (min_le_left _ _)
  have hrp : rr ≤ Real.pi - theta p := (min_le_right _ _).trans (min_le_right _ _)
  let s := rr / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hse : s < eps := by dsimp [s]; linarith
  have hst : s < theta p := by dsimp [s]; linarith
  have hsp : s < Real.pi - theta p := by dsimp [s]; linarith
  have hm := hminor (theta p - s) ⟨by linarith [Real.pi_pos], by linarith⟩
  have hp' := hminor (theta p + s) ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [abs_of_nonneg (by linarith : 0 ≤ theta p - s)] at hm
  rw [abs_of_nonneg (by linarith : 0 ≤ theta p + s)] at hp'
  have hcenter : q p * theta p = Real.pi / 2 := by
    unfold q theta
    field_simp
  have hcos : KK * Real.cos (q p * (theta p - s)) +
      KK * Real.cos (q p * (theta p + s)) = 0 := by
    rw [show q p * (theta p - s) = q p * theta p - q p * s by ring,
      show q p * (theta p + s) = q p * theta p + q p * s by ring,
      Real.cos_sub, Real.cos_add, hcenter, Real.cos_pi_div_two]
    ring
  have hsum := add_le_add hm hp'
  rw [hcos] at hsum
  exact not_lt_of_ge hsum (hnegative s ⟨hs, hse⟩)

theorem localTest_excludes_cosine_minorant (p lam KK : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hlocal : 1 < localTest p lam) :
    ¬ ∀ t ∈ Icc (-Real.pi) Real.pi,
      KK * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t := by
  have hl : lam ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hlam.1], hlam.2⟩
  exact negative_pair_excludes_cosine_minorant p lam KK hp hp2 hl
    ((contact_sign_factorization_proved p lam hp hp2 hl).2.2.mpr hlocal)

end GKSharp

#print axioms GKSharp.negative_pair_excludes_cosine_minorant
#print axioms GKSharp.localTest_excludes_cosine_minorant
