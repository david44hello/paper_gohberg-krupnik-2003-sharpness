/-
GKSharp/Proofs/TheoremC1.lean — Theorem C1, short v0.70 sec5_sharp_inequality.tex l.167-174: for λ ∈ [−1, 0] and every
p > 1, ‖P₊ + λP₋‖_p = GK_p(λ); for 1 < p < 2 equality in (*) only at z_*, z̄_*. Lemma B enters through its proof
`lemma_B_proved`, whose one input is the one-variable sign lemma (`BplusB.OnevarHyp`, the paper's lemma_onevar).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.Reduction
import GKSharp.Proofs.PropositionQFull
import GKSharp.Proofs.MonotoneLemmaB
import GKSharp.Proofs.MonotoneSign
import GKSharp.Proofs.CurveK
import GKSharp.Proofs.PencilL2
import GKSharp.Proofs.PencilDual
import GKSharp.Proofs.GKProps
import GKSharp.Proofs.GKRoot
import GKSharp.Cited.HV2000

namespace GKSharp.Proofs.TheoremC1

open GKSharp ComplexConjugate Set

/-- `K_f` is strictly decreasing for `λ ∈ [−1, 0]` (l.167-171): `λ = −1` by `(ln K_f)′ < 0`, `λ ∈ (−1, 0]` by Lemma B. -/
theorem curveKf_strictAnti_of_onevar (onevar : BplusB.OnevarHyp) {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl0 : lam ≤ 0) : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) := by
  rcases eq_or_lt_of_le hl with h | h
  · subst h; exact (curveKf_minus_one_deriv hp1 hp2).2
  · exact lemma_B_proved onevar hp1 hp2 h hl0

/-- Theorem C1, equality case (l.172): Proposition (Reduction) for `λ ∈ [−1, 0]`. -/
theorem thm_C1_equality_of_onevar (onevar : BplusB.OnevarHyp) {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl0 : lam ≤ 0) :
    (∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) ∧
    ∀ z : ℂ, critD p (gk p lam) (kConst p lam) lam z = 0 →
      z = curveZ p lam (Real.pi / p) ∨ z = conj (curveZ p lam (Real.pi / p)) :=
  Reduction.prop_reduction_proved hp1 hp2 hl (by linarith) (curveKf_strictAnti_of_onevar onevar hp1 hp2 hl hl0)

/-- Theorem C1 for `1 < p < 2` (l.172): Propositions red and Q. -/
theorem thm_C1_lt_two_of_onevar (onevar : BplusB.OnevarHyp) {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    (hp2 : p < 2) (P : RieszProjection p) {lam : ℝ} (hl : -1 ≤ lam) (hl0 : lam ≤ 0) :
    pencilNorm P lam = gk p lam :=
  (sec4_prop_Q_proved p P hp hp2 lam ⟨hl, by linarith⟩).2.mpr (thm_C1_equality_of_onevar onevar hp hp2 hl hl0).1

/-- Theorem C1 (l.172-173): "For p > 2 use N_p(λ) = N_{p′}(λ) and GK_p = GK_{p′} (Section 2); for p = 2 both sides are
max(1, |λ|)". -/
theorem thm_C1_of_onevar (onevar : BplusB.OnevarHyp) {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    (P : RieszProjection p) {lam : ℝ} (hl : -1 ≤ lam) (hl0 : lam ≤ 0) : pencilNorm P lam = gk p lam := by
  rcases lt_trichotomy p 2 with hp2 | hp2 | hp2
  · exact thm_C1_lt_two_of_onevar onevar hp hp2 P hl hl0
  · subst hp2
    rw [pencilNorm, norm_pencil_two rfl P 1 lam, gk, gkPair_two]
  · -- duality: `p′ = p/(p − 1) ∈ (1, 2)`
    have hq1 : 1 < p / (p - 1) := by rw [lt_div_iff₀ (by linarith)]; linarith
    have hq2 : p / (p - 1) < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
    have : Fact (1 ≤ ENNReal.ofReal (p / (p - 1))) :=
      ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le⟩
    obtain ⟨Q, -⟩ := GKSharp.Cited.hv2000_riesz_norm (p / (p - 1)) hq1
    rw [pencilNorm_dual hp P Q, Complex.star_def, Complex.conj_ofReal,
      thm_C1_lt_two_of_onevar onevar hq1 hq2 Q hl hl0, gk_dual p hp]

/-- The one-variable sign lemma (sec5d_monotone.tex), in the form Lemma B takes. -/
theorem onevar_hyp : BplusB.OnevarHyp := fun hp1 hp2 hl hl1 hθ0 hθ => lemma_onevar_proved hp1 hp2 hl hl1 hθ0 hθ

/-- Theorem C1, equality case (l.167-172), for `1 < p < 2`, `λ ∈ [−1, 0]`. -/
theorem thm_C1_equality_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl0 : lam ≤ 0) :
    (∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) ∧
    ∀ z : ℂ, critD p (gk p lam) (kConst p lam) lam z = 0 →
      z = curveZ p lam (Real.pi / p) ∨ z = conj (curveZ p lam (Real.pi / p)) :=
  thm_C1_equality_of_onevar onevar_hyp hp1 hp2 hl hl0

/-- Theorem C1 (l.167-174): `‖P₊ + λP₋‖_p = GK_p(λ)` for every `p > 1` and `λ ∈ [−1, 0]`. -/
theorem thm_C1_proved {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) {lam : ℝ}
    (hl : -1 ≤ lam) (hl0 : lam ≤ 0) : pencilNorm P lam = gk p lam :=
  thm_C1_of_onevar onevar_hyp hp P hl hl0

end GKSharp.Proofs.TheoremC1

#print axioms GKSharp.Proofs.TheoremC1.thm_C1_equality_proved
#print axioms GKSharp.Proofs.TheoremC1.thm_C1_proved
