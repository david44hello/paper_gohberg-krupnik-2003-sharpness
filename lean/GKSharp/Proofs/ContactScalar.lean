/- GKSharp/Proofs/ContactScalar.lean — actual contact root and rational identities.
Frozen source: short_v0.40/sec4b_failure.tex:28–32,52–57.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.ThresholdAnalysis

namespace GKSharp
open Threshold Set

private theorem contact_trig {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    0 < cs p ∧ cs p < 1 ∧ 0 < sn p ∧ sn p ^ 2 + cs p ^ 2 = 1 := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 < Real.pi / p := div_pos Real.pi_pos hp0
  have htpi : Real.pi / p < Real.pi := by
    rw [div_lt_iff₀ hp0]
    nlinarith [Real.pi_pos]
  have hthalf : Real.pi / 2 < Real.pi / p := by
    rw [lt_div_iff₀ hp0]
    nlinarith [Real.pi_pos]
  have hc : 0 < cs p := by
    unfold cs
    exact neg_pos.mpr (Real.cos_neg_of_pi_div_two_lt_of_lt hthalf (by linarith))
  have hs : 0 < sn p := Real.sin_pos_of_pos_of_lt_pi ht0 htpi
  have hid : sn p ^ 2 + cs p ^ 2 = 1 := by
    simp [sn, cs]
  exact ⟨hc, by nlinarith [sq_pos_of_pos hs], hs, hid⟩

/-- B:28–32 scalar part: the chosen larger quadratic root is positive and
nondegenerate. Analytic Gamma clauses are not included here. -/
theorem contact_root_properties {p lam : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    1 < rContact p lam ∧ |lam| < rContact p lam ∧ 0 < vContact p lam ∧
      rContact p lam + lam / rContact p lam = sigmaContact p lam := by
  obtain ⟨hc, hc1, _, _⟩ := contact_trig hp hp2
  have hl : 0 < 1 + lam := by linarith [hlam.1]
  have hsig : 1 + lam < sigmaContact p lam := by
    unfold sigmaContact
    rw [lt_div_iff₀ hc]
    nlinarith
  have hd : 0 < sigmaContact p lam ^ 2 - 4 * lam := by
    nlinarith [sq_nonneg (sigmaContact p lam - 2)]
  have hspos := Real.sqrt_pos.mpr hd
  have hsq := Real.sq_sqrt (le_of_lt hd)
  have hr : 1 < rContact p lam := by
    unfold rContact
    by_contra hh
    have hb : Real.sqrt (sigmaContact p lam ^ 2 - 4 * lam) ≤
        2 - sigmaContact p lam := by linarith
    have hprod := mul_nonneg
      (sub_nonneg.mpr hb)
      (show 0 ≤ 2 - sigmaContact p lam +
        Real.sqrt (sigmaContact p lam ^ 2 - 4 * lam) by linarith)
    nlinarith
  have hr0 : 0 < rContact p lam := by linarith
  have hroot : rContact p lam ^ 2 - sigmaContact p lam * rContact p lam + lam = 0 := by
    unfold rContact
    nlinarith
  have hsum : rContact p lam + lam / rContact p lam = sigmaContact p lam := by
    field_simp [ne_of_gt hr0]
    nlinarith [hroot]
  have hv : 0 < vContact p lam := by
    unfold vContact
    have hh : lam / rContact p lam < rContact p lam := by
      rw [div_lt_iff₀ hr0]
      nlinarith [hlam.2, sq_pos_of_pos (sub_pos.mpr hr)]
    linarith
  exact ⟨hr, lt_trans (abs_lt.mpr hlam) hr, hv, hsum⟩

/-- B:52–57. The three printed rational identities at the actual chosen contact.
PROVED: no computer-check hypotheses or analytic contact assumptions. -/
theorem contact_rational_identities_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let r := rContact p lam
    cs p = (1 + lam) * r / (r ^ 2 + lam) ∧
    sn p ^ 2 = (r ^ 2 - 1) * (r ^ 2 - lam ^ 2) / (r ^ 2 + lam) ^ 2 ∧
    dOne p lam = (r ^ 2 - lam) * (r ^ 2 - lam ^ 2) / (r ^ 2 * (r ^ 2 + lam)) := by
  dsimp only
  obtain ⟨hr, _, _, hsum⟩ := contact_root_properties hp hp2 hlam
  obtain ⟨hc, _, _, htrig⟩ := contact_trig hp hp2
  have hr0 : rContact p lam ≠ 0 := by linarith
  have hdenpos : 0 < rContact p lam ^ 2 + lam := by
    nlinarith [hlam.1, sq_pos_of_pos (sub_pos.mpr hr)]
  have hden : rContact p lam ^ 2 + lam ≠ 0 := ne_of_gt hdenpos
  have hrel : cs p * (rContact p lam ^ 2 + lam) = (1 + lam) * rContact p lam := by
    unfold sigmaContact at hsum
    field_simp [hr0, ne_of_gt hc] at hsum
    nlinarith [hsum]
  have hcos : cs p = (1 + lam) * rContact p lam / (rContact p lam ^ 2 + lam) :=
    (eq_div_iff hden).mpr hrel
  refine ⟨hcos, ?_, ?_⟩
  · rw [hcos] at htrig
    field_simp [hden] at htrig ⊢
    nlinarith [htrig]
  · unfold dOne
    rw [hcos]
    field_simp [hr0, hden]
    ring

/-- B:76–77. Positivity of the printed scalar factor at the actual contact. -/
theorem contact_bZero_pos {p lam : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) : 0 < bZero p lam := by
  obtain ⟨hc, _, hs, _⟩ := contact_trig hp hp2
  obtain ⟨_, _, hv, _⟩ := contact_root_properties hp hp2 hlam
  have hl1 : 0 < 1 - lam := by linarith [hlam.2]
  have hl2 : 0 < 1 + lam := by linarith [hlam.1]
  unfold bZero
  positivity

/-- B:79–82. Pure scalar part of the sign test; relating muSecond to this
bracket still requires the analytic derivative and Schur identities. -/
theorem contact_signBracket_negative_iff {p lam : ℝ} (hp : 1 < p)
    (hlam : -1 < lam) : signBracket p lam < 0 ↔ 1 < localTest p lam := by
  have hpm : p - 1 ≠ 0 := by linarith
  have hl : 1 + lam ≠ 0 := by linarith
  have hid : signBracket p lam = (p - 1) * (1 - localTest p lam) := by
    unfold signBracket localTest dual
    field_simp [hpm, hl]
    ring
  rw [hid]
  constructor <;> intro hh <;> nlinarith

end GKSharp

#print axioms GKSharp.contact_root_properties
#print axioms GKSharp.contact_rational_identities_proved
#print axioms GKSharp.contact_bZero_pos
#print axioms GKSharp.contact_signBracket_negative_iff
