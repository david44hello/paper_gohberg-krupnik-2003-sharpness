/- Theorem B (a) and its last sentence, P019_paper.tex l.131-135 (proof: sec5_sharp_inequality.tex l.175-180).
Proposition S (sec5f_strip, p₀ ≤ p < 3 - √3) enters as the explicit premise `hS` (its operator conclusion).
Copyright (C) Dave Goel 2026--now.

  The text's route. (1) 3 - √3 ≤ p < 2, λ ∈ (-1, 1): K_f strictly decreasing (Lemma B⁺), so D_C ≥ 0 (Proposition
  Reduction) and N_p(λ) = GK_p(λ) (Proposition Q, second iff). λ = -1: Theorem C1. λ = 1: N_p(1) = GK_p(1) = 1.
  |λ| > 1: N_p(λ) = |λ| N_p(1/λ), GK_p(λ) = |λ| GK_p(1/λ). (2) p₀ ≤ p < 3 - √3: Proposition S (premise). (3) p = 2:
  N_2 = GK_2 = max(1, |λ|). (4) 2 < p ≤ p₀′: duality at p′ = p/(p - 1) ∈ [p₀, 2) (HV2000 gives a projection at p′).
  Last sentence: homogeneity N(α, β) = |α| N(β/α), GK(α, β) = |α| GK(β/α); "if" from (a) at λ = β/α real, "only if" is
  Theorem A (from Theorem R and the chord inequality, as installed); α = 0: both sides equal |β|/sin(π/p). -/
import GKSharp.Proofs.TheoremC1
import GKSharp.Proofs.MonotoneBplusB
import GKSharp.Proofs.GKSymm
import GKSharp.Proofs.Sec4aEndpoint
import GKSharp.Proofs.Sec3Geom
import GKSharp.Proofs.TheoremR
import GKSharp.Proofs.ChordGK
import GKSharp.Proofs.NormReduce
import GKSharp.ComputerChecked

open Set GKSharp.Threshold GKSharp.ComputerChecked

namespace GKSharp

namespace ThmBa

/-- Theorem A (`p ≠ 2`, `Im ρ ≠ 0` ⇒ `GK_p(ρ) < N_p(ρ)`), from the installed proofs behind the rows. -/
theorem thm_A_proof {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p ≠ 2) (P : RieszProjection p)
    {ρ : ℂ} (hρ : ρ.im ≠ 0) : gk p ρ < pencilNorm P ρ :=
  Sec3Geom.thm_A_given (Sec3Geom.eq_3_2_given @slice_O18_proved (Sec3Geom.sec3_arch_given ChordGK.slice_O30_proved))
    hp hp2 P hρ

/-- Inversion: from `(-1, 1)` to `|λ| > 1`. -/
theorem inv_step {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p)
    (hunit : ∀ lam : ℝ, -1 < lam → lam < 1 → pencilNorm P lam = gk p lam) {lam : ℝ} (hl : 1 < |lam|) :
    pencilNorm P lam = gk p lam := by
  have hl0 : lam ≠ 0 := fun h => by rw [h, abs_zero] at hl; linarith
  have hne : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl0
  have hinv : |1 / lam| < 1 := by
    rw [abs_div, abs_one, div_lt_one (by linarith)]
    exact hl
  have hcast : 1 / (lam : ℂ) = ((1 / lam : ℝ) : ℂ) := by push_cast; ring
  rw [pencilNorm_inv P _ hne, gk_inv p hne, hcast, hunit (1 / lam) (abs_lt.mp hinv).1 (abs_lt.mp hinv).2]

/-- From `λ ∈ (-1, 1)` to every real `λ` (`1 < p < 2`): Theorem C1 at `-1`, `N_p(1) = GK_p(1) = 1`, inversion. -/
theorem all_real_of_unit {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p)
    (hunit : ∀ lam : ℝ, -1 < lam → lam < 1 → pencilNorm P lam = gk p lam) :
    ∀ lam : ℝ, pencilNorm P lam = gk p lam := by
  intro lam
  rcases lt_trichotomy lam (-1) with hlt | heq | hgt
  · exact inv_step P hunit (by rw [abs_of_neg (by linarith)]; linarith)
  · subst heq
    exact Proofs.TheoremC1.thm_C1_proved hp P le_rfl (by norm_num)
  · rcases lt_trichotomy lam 1 with hlt1 | heq1 | hgt1
    · exact hunit lam hgt hlt1
    · subst heq1
      rw [Complex.ofReal_one, pencilNorm_one P, gk_one p]
    · exact inv_step P hunit (by rw [abs_of_pos (by linarith)]; exact hgt1)

/-- `1 < p < 2`: Lemma B⁺ + Reduction + Proposition Q for `3 - √3 ≤ p`, the premise (Proposition S) below. -/
theorem eq_lt_two {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p < 2) (P : RieszProjection p)
    (hS : p < 3 - Real.sqrt 3 → ∀ lam : ℝ, pencilNorm P lam = gk p lam) :
    ∀ lam : ℝ, pencilNorm P lam = gk p lam := by
  by_cases hsq : 3 - Real.sqrt 3 ≤ p
  · refine all_real_of_unit hp P fun lam hl hl1 => ?_
    have hdec := lemma_Bplus_proved @lemma_onevar_proved hsq hp2 hl hl1
    have hcrit := (Proofs.Reduction.prop_reduction_proved hp hp2 hl.le hl1 hdec).1
    exact ((sec4_prop_Q_proved p P hp hp2 lam ⟨hl.le, hl1⟩).2).mpr hcrit
  · exact hS (lt_of_not_ge hsq)

/-- **Theorem B (a)**, P019_paper.tex l.131-133, with Proposition S's operator conclusion as the premise `hS`. -/
theorem thm_B_a_of (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hS : ∀ (q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)] (Q : RieszProjection q),
      q ∈ Ico p0 (3 - Real.sqrt 3) → ∀ lam : ℝ, pencilNorm Q lam = gk q lam)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p)
    (hlo : p0 ≤ p) (hhi : p ≤ p0 / (p0 - 1)) :
    ∀ lam : ℝ, pencilNorm P lam = gk p lam := by
  obtain ⟨-, ha0, hb0, -, -, -⟩ := p0_spec_proved hn hr
  have hp0 : 1 < p0 := lt_trans (by norm_num [a0]) ha0
  have hp02 : p0 < 2 := hb0.trans (by norm_num [b0])
  rcases lt_trichotomy p 2 with hp2 | hp2 | hp2
  · exact eq_lt_two hp hp2 P (fun h => hS p P ⟨hlo, h⟩)
  · subst hp2
    intro lam
    rw [pencilNorm, norm_pencil_two rfl P 1 lam, gk, gkPair_two]
  · -- duality: `p′ = p/(p − 1) ∈ [p₀, 2)`
    have hq1 : 1 < p / (p - 1) := by rw [lt_div_iff₀ (by linarith)]; linarith
    have hq2 : p / (p - 1) < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
    have hqlo : p0 ≤ p / (p - 1) := by
      rw [le_div_iff₀ (by linarith)]
      rw [le_div_iff₀ (by linarith)] at hhi
      nlinarith
    have : Fact (1 ≤ ENNReal.ofReal (p / (p - 1))) :=
      ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le⟩
    obtain ⟨Q, -⟩ := GKSharp.Cited.hv2000_riesz_norm (p / (p - 1)) hq1
    intro lam
    rw [pencilNorm_dual hp P Q, Complex.star_def, Complex.conj_ofReal,
      eq_lt_two hq1 hq2 Q (fun h => hS _ Q ⟨hqlo, h⟩) lam, gk_dual p hp]

/-- **Theorem B, last sentence**, P019_paper.tex l.135 ("With Theorem A"), with Proposition S as the premise `hS`. -/
theorem thm_B_pair_of (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hS : ∀ (q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)] (Q : RieszProjection q),
      q ∈ Ico p0 (3 - Real.sqrt 3) → ∀ lam : ℝ, pencilNorm Q lam = gk q lam)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) :
    (p0 ≤ p → p ≤ p0 / (p0 - 1) → p ≠ 2 →
      ∀ α β : ℂ, α ≠ 0 → (‖pencil P α β‖ = gkPair p α β ↔ (β / α).im = 0)) ∧
    ∀ β : ℂ, ‖pencil P 0 β‖ = gkPair p 0 β := by
  refine ⟨fun hlo hhi hp2 α β hα => ?_, fun β => by rw [norm_pencil_zero_left_eq hp P β, gkPair_zero_left p hp β]⟩
  rw [pencil_norm_homogeneous P α β hα, gkPair_homog p hα β]
  have hαn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  constructor
  · intro heq
    by_contra him
    have hlt := thm_A_proof hp hp2 P him
    have heq' : pencilNorm P (β / α) = gk p (β / α) := (mul_left_cancel₀ hαn.ne' heq)
    linarith
  · intro him
    have hρ : β / α = (((β / α).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hρ, thm_B_a_of hn hr hS hp P hlo hhi (β / α).re]

end ThmBa

end GKSharp
