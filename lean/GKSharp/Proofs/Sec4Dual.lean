/- GKSharp/Proofs/Sec4Dual.lean - slice (b): the scalar conditions under duality p ↦ p/(p-1) (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v1.30, each as `<row>_proved` with the row's exact type.
- sec4_conditions_dual (sec4b l.12): with `p' = p/(p-1)`: `p'' = p`, so `p' p'' = p p'`; `π/p' = π - π/p`, so
  `sin(π/p') = sin(π/p)` and `cos(π/p') = -cos(π/p)`. localTest, localF, localD2 depend on `p p'`, `sn²`, `cos²`,
  `cs²`, `cs⁴` only, and lambdaLoc on localF and localD2.
- sec4_lemma_Pc_full (sec4b l.94): for `p < 2` rows local_witness_iff and pc_spec (`dual pc > 2 > p`); at `p = 2`,
  `localF 2 = 0` and `localTest 2 λ = 1`, so every side is false; for `p > 2`, `p' ∈ (1, 2)` and the invariance
  reduce to `p'`, and `p' < pc ⟺ pc/(pc-1) < p` (both say `p + pc < p pc`).
-/
import GKSharp.Proofs.Sec4bChecks

namespace GKSharp

open Set GKSharp.Threshold GKSharp.ComputerChecked

lemma sec4d_dual_dual {p : ℝ} (hp : 1 < p) : dual (dual p) = p := by
  have hp1 : p - 1 ≠ 0 := (sub_pos.2 hp).ne'
  have hden : p / (p - 1) - 1 ≠ 0 := by
    rw [div_sub_one hp1, sub_sub_cancel]
    exact div_ne_zero one_ne_zero hp1
  unfold dual
  rw [div_eq_iff hden, div_sub_one hp1, sub_sub_cancel, mul_one_div]

lemma sec4d_pi_div_dual {p : ℝ} (hp : 1 < p) : Real.pi / dual p = Real.pi - Real.pi / p := by
  have hp0 : p ≠ 0 := by linarith
  unfold dual
  rw [div_div_eq_mul_div, mul_sub, mul_one, sub_div, mul_div_assoc, div_self hp0, mul_one]

/-- `dual` reverses the order on `(1, ∞)`: `p/(p-1) < c ⟺ c/(c-1) < p`. -/
lemma sec4d_dual_lt_iff {p c : ℝ} (hp : 1 < p) (hc : 1 < c) : dual p < c ↔ dual c < p := by
  unfold dual
  rw [div_lt_iff₀ (by linarith), div_lt_iff₀ (by linarith)]
  constructor <;> intro h <;> linarith

/-- sec4b_failure.tex:12, row `sec4_conditions_dual`. -/
theorem sec4_conditions_dual_proved (p lam : ℝ) (hp : 1 < p) :
    localTest (dual p) lam = localTest p lam ∧ localF (dual p) = localF p ∧
      localD2 (dual p) = localD2 p ∧ lambdaLoc (dual p) = lambdaLoc p := by
  have hpi := sec4d_pi_div_dual hp
  have hcos : Real.cos (Real.pi / dual p) = -Real.cos (Real.pi / p) := by rw [hpi, Real.cos_pi_sub]
  have hsn : sn (dual p) = sn p := by unfold sn; rw [hpi, Real.sin_pi_sub]
  have hcs : cs (dual p) = -cs p := by unfold cs; rw [hcos]
  have hpp : dual p * dual (dual p) = p * dual p := by rw [sec4d_dual_dual hp, mul_comm]
  have hF : localF (dual p) = localF p := by
    unfold localF
    rw [hpp, hcos, neg_sq]
  have hD : localD2 (dual p) = localD2 p := by
    unfold localD2
    rw [hsn, hcs, hpp]
    ring
  have hT : localTest (dual p) lam = localTest p lam := by
    unfold localTest
    rw [hsn, hcs, hpp]
    ring
  have hL : lambdaLoc (dual p) = lambdaLoc p := by
    unfold lambdaLoc
    rw [hF, hD]
  exact ⟨hT, hF, hD, hL⟩

/-- sec4b_failure.tex:94, row `sec4_lemma_Pc_full`. -/
theorem sec4_lemma_Pc_full_proved (hc : CheckLocalF) (p : ℝ) (hp : 1 < p) :
    ((∃ lam ∈ Ioo (0 : ℝ) 1, 1 < localTest p lam) ↔ 0 < localF p) ∧
      (0 < localF p ↔ (p < pc ∨ dual pc < p)) := by
  obtain ⟨-, ⟨hpc1, hpc2⟩, -, hFiff, -⟩ := pc_spec_proved hc
  have hpc : 1 < pc := by linarith
  have hdpc : 2 < dual pc := by
    unfold dual
    rw [lt_div_iff₀ (by linarith)]
    linarith
  rcases lt_trichotomy p 2 with hp2 | rfl | hp2
  · refine ⟨local_witness_iff_proved p hp hp2, ?_⟩
    rw [hFiff p ⟨hp, hp2⟩]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · linarith
  · have hd2 : dual 2 = 2 := by unfold dual; norm_num
    have hF2 : localF 2 = 0 := by
      unfold localF
      rw [hd2, Real.cos_pi_div_two]
      norm_num
    have hT2 : ∀ lam : ℝ, localTest 2 lam = 1 := by
      intro lam
      unfold localTest sn cs
      rw [hd2, Real.sin_pi_div_two, Real.cos_pi_div_two]
      norm_num
    rw [hF2]
    refine ⟨⟨fun ⟨lam, _, h⟩ => by rw [hT2 lam] at h; exact absurd h (lt_irrefl 1), fun h => absurd h (lt_irrefl 0)⟩,
      ⟨fun h => absurd h (lt_irrefl 0), ?_⟩⟩
    rintro (h | h) <;> linarith
  · have hd1 : 1 < dual p := by
      unfold dual
      rw [lt_div_iff₀ (by linarith)]
      linarith
    have hd2 : dual p < 2 := by
      unfold dual
      rw [div_lt_iff₀ (by linarith)]
      linarith
    have hinv := sec4_conditions_dual_proved p 0 hp
    have hT : ∀ lam : ℝ, localTest (dual p) lam = localTest p lam := fun lam =>
      (sec4_conditions_dual_proved p lam hp).1
    have hW := local_witness_iff_proved (dual p) hd1 hd2
    simp only [hT, hinv.2.1] at hW
    refine ⟨hW, ?_⟩
    rw [← hinv.2.1, hFiff (dual p) ⟨hd1, hd2⟩, sec4d_dual_lt_iff hp hpc]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · linarith
      · exact h

end GKSharp

