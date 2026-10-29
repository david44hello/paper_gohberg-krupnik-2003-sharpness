/- GKSharp/Proofs/ContactSign.lean — complete actual Schur sign factorization.
Frozen source: short_v0.70/sec4b_failure.tex:53–85; former v0.40:58–90.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactSchur
import GKSharp.Proofs.ContactExpanded
import GKSharp.Proofs.ContactK
import GKSharp.Proofs.Sec4aBasic

namespace GKSharp
open Threshold Set

theorem contact_schur_expanded_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let r := rContact p lam
    let v := vContact p lam
    Real.exp (q p * y) * muSecond p lam / (p * weightP p lam y (theta p)) =
      2 * p * lam * (1 - lam) / (r * v * dOne p lam) +
        p * (1 - lam) ^ 2 / (sn p ^ 2 * v ^ 2) -
        (1 - lam) * cs p / (sn p ^ 2 * v) -
        (1 - lam) / (cs p * v) *
          (sigmaContact p lam / v - p * dy (chi lam) y (theta p) + p / 2) ^ 2 := by
  dsimp only
  obtain ⟨hr, _, hv, _⟩ := contact_root_properties hp hp2 hlam
  have hs := sec4a_sn_pos hp
  have hc : 0 < cs p := neg_pos.mpr (cos_theta_negative hp hp2)
  have htrig : sn p ^ 2 + cs p ^ 2 = 1 := by simp [sn, cs]
  have hD : 0 < dOne p lam := by
    unfold dOne
    nlinarith only [sq_nonneg (lam / rContact p lam - cs p), sq_pos_of_pos hs, htrig]
  have hl : 1 - lam ≠ 0 := by linarith [hlam.2]
  obtain ⟨hLt, hLyy, hLty, _, hCt, _⟩ := contact_derivative_values_proved p lam hp hp2 hlam
  rw [contact_schur_identity_proved p lam hp hp2 hlam, hLt, hLyy, hLty, hCt]
  unfold q
  field_simp [ne_of_gt hs, ne_of_gt hc, ne_of_gt hv, ne_of_gt hD,
    show rContact p lam ≠ 0 by linarith, hl]
  <;> ring

theorem contact_sign_factorization_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    0 < bZero p lam ∧
    Real.exp (q p * yContact p lam) * muSecond p lam /
      (p * weightP p lam (yContact p lam) (theta p)) = bZero p lam * signBracket p lam ∧
    (muSecond p lam < 0 ↔ 1 < localTest p lam) := by
  have hb := contact_bZero_pos hp hp2 hlam
  have hnorm : Real.exp (q p * yContact p lam) * muSecond p lam /
      (p * weightP p lam (yContact p lam) (theta p)) = bZero p lam * signBracket p lam := by
    have hh := contact_schur_expanded_proved p lam hp hp2 hlam
    have hchi := (contact_derivative_values_proved p lam hp hp2 hlam).2.2.2.1
    dsimp only at hh
    rw [hchi] at hh
    exact hh.trans (contact_expanded_factorization p lam hp hp2 hlam)
  have hP : 0 < p * weightP p lam (yContact p lam) (theta p) :=
    mul_pos (by linarith) (Real.exp_pos _)
  have hiff : muSecond p lam < 0 ↔ signBracket p lam < 0 := by
    constructor
    · intro hh
      have hn := div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (Real.exp_pos (q p * yContact p lam)) hh) hP
      rw [hnorm] at hn
      by_contra hnot
      have hnonneg := mul_nonneg hb.le (le_of_not_gt hnot)
      linarith only [hn, hnonneg]
    · intro hh
      have hn : Real.exp (q p * yContact p lam) * muSecond p lam /
          (p * weightP p lam (yContact p lam) (theta p)) < 0 := by
        rw [hnorm]
        exact mul_neg_of_pos_of_neg hb hh
      by_contra hnot
      have hnonneg := div_nonneg
        (mul_nonneg (Real.exp_pos (q p * yContact p lam)).le (le_of_not_gt hnot)) hP.le
      linarith only [hn, hnonneg]
  exact ⟨hb, hnorm, hiff.trans (contact_signBracket_negative_iff hp hlam.1)⟩

theorem corollary_L0_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioc (-1 : ℝ) 0) : 0 < muSecond p lam := by
  have hl : lam ∈ Ioo (-1 : ℝ) 1 := ⟨hlam.1, by linarith [hlam.2]⟩
  have hterm : 4 * lam * cs p ^ 4 / (1 + lam) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hlam.2]) (show 0 ≤ cs p ^ 4 by positivity))
      (sq_nonneg (1 + lam))
  have htest : localTest p lam < 1 := by
    unfold localTest
    linarith only [strict_jordan_pp_proved p hp hp2, hterm]
  have hpm : p - 1 ≠ 0 := by linarith
  have hld : 1 + lam ≠ 0 := by linarith [hlam.1]
  have hid : signBracket p lam = (p - 1) * (1 - localTest p lam) := by
    unfold signBracket localTest dual
    field_simp [hpm, hld]
    ring
  have hbracket : 0 < signBracket p lam := by
    rw [hid]
    exact mul_pos (by linarith) (by linarith)
  obtain ⟨hb, hnorm, _⟩ := contact_sign_factorization_proved p lam hp hp2 hl
  have hn : 0 < Real.exp (q p * yContact p lam) * muSecond p lam /
      (p * weightP p lam (yContact p lam) (theta p)) := by
    rw [hnorm]
    exact mul_pos hb hbracket
  by_contra hnot
  have hP : 0 < p * weightP p lam (yContact p lam) (theta p) :=
    mul_pos (by linarith) (Real.exp_pos _)
  have hnonpos := div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (q p * yContact p lam)).le (le_of_not_gt hnot))
    hP.le
  linarith only [hn, hnonpos]

end GKSharp

#print axioms GKSharp.contact_schur_expanded_proved
#print axioms GKSharp.contact_sign_factorization_proved
#print axioms GKSharp.corollary_L0_proved

