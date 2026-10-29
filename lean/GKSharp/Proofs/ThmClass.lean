/- the sharpness classification, P019_paper.tex l.84-90, assembled clause by clause from Theorems A, C1,
B (a), B (b), C* and duality. Proposition S and Theorem C* enter as the explicit premises `hS`, `hCstar` (their
conclusions, for every exponent and projection: the p > 2 clause uses C* at p′).
Copyright (C) Dave Goel 2026--now.

  (1) p ≠ 2, ρ ∉ ℝ: Theorem A. (2) λ ∈ [-1, 0]: Theorem C1. (3) equality for every real λ iff p₀ ≤ p ≤ p₀′: "if" is
  Theorem B (a); "only if": outside [p₀, p₀′] Theorem B (b) gives GK < N at λ = 1 - ε/2. (4) Theorem B (b).
  (5) 1 < p < 2, 0 < λ < 1: Theorem C*. (6) p > 2: N_p(λ) = N_{p′}(λ), GK_p = GK_{p′} (pencilNorm_dual with an HV2000
  projection at p′, gk_dual), then Theorem C* at p′ ∈ (1, 2). (7) p = 2: N_2(ρ) = GK_2(ρ) = max(1, |ρ|). -/
import GKSharp.Proofs.ThmBa
import GKSharp.Proofs.ThmBb

open Set GKSharp.ComputerChecked

namespace GKSharp

namespace ThmClass

/-- **Sharpness classification**, P019_paper.tex l.84-90, from the conclusions of Proposition S (`hS`) and Theorem C*
(`hCstar`). -/
theorem thm_classification_of (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hS : ∀ (q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)] (Q : RieszProjection q),
      q ∈ Ico Threshold.p0 (3 - Real.sqrt 3) → ∀ lam : ℝ, pencilNorm Q lam = gk q lam)
    (hCstar : ∀ (q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)] (Q : RieszProjection q), 1 < q → q < 2 →
      ∀ lam : ℝ, 0 < lam → lam < 1 →
        (pencilNorm Q lam = gk q lam ↔
          kConst q lam ≤ obstacle q (gk q lam) lam 0 ∧ lam < Threshold.lambdaLoc q))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) :
    (p ≠ 2 → ∀ ρ : ℂ, ρ.im ≠ 0 → gk p ρ < pencilNorm P ρ) ∧
    (∀ lam : ℝ, -1 ≤ lam → lam ≤ 0 → pencilNorm P lam = gk p lam) ∧
    ((∀ lam : ℝ, pencilNorm P lam = gk p lam) ↔
      Threshold.p0 ≤ p ∧ p ≤ Threshold.p0 / (Threshold.p0 - 1)) ∧
    ((p < Threshold.p0 ∨ Threshold.p0 / (Threshold.p0 - 1) < p) →
      ∃ ε > 0, ∀ lam : ℝ, 1 - ε < lam → lam < 1 → gk p lam < pencilNorm P lam) ∧
    (p < 2 → ∀ lam : ℝ, 0 < lam → lam < 1 →
      (pencilNorm P lam = gk p lam ↔
        kConst p lam ≤ obstacle p (gk p lam) lam 0 ∧ lam < Threshold.lambdaLoc p)) ∧
    (2 < p → ∀ lam : ℝ, 0 < lam → lam < 1 →
      (pencilNorm P lam = gk p lam ↔
        kConst (p / (p - 1)) lam ≤ obstacle (p / (p - 1)) (gk (p / (p - 1)) lam) lam 0 ∧
          lam < Threshold.lambdaLoc (p / (p - 1)))) ∧
    (p = 2 → ∀ ρ : ℂ, pencilNorm P ρ = gk p ρ) := by
  refine ⟨fun hp2 ρ hρ => ThmBa.thm_A_proof hp hp2 P hρ,
    fun lam hl hl0 => Proofs.TheoremC1.thm_C1_proved hp P hl hl0,
    ⟨fun hall => ?_, fun h => ThmBa.thm_B_a_of hn hr hS hp P h.1 h.2⟩,
    fun hout => ThmBb.thm_B_b_proved hn hr hp P hout,
    fun hp2 lam hl0 hl1 => hCstar p P hp hp2 lam hl0 hl1,
    fun hp2 lam hl0 hl1 => ?_, fun hp2 ρ => ?_⟩
  · -- "only if": outside [p₀, p₀′], Theorem B (b) breaks equality at λ = 1 - ε/2
    by_contra hnot
    have hout : p < Threshold.p0 ∨ Threshold.p0 / (Threshold.p0 - 1) < p := by
      rcases not_and_or.mp hnot with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    obtain ⟨ε, hε, hlt⟩ := ThmBb.thm_B_b_proved hn hr hp P hout
    have h := hlt (1 - ε / 2) (by linarith) (by linarith)
    rw [hall (1 - ε / 2)] at h
    exact lt_irrefl _ h
  · -- p > 2: duality, then Theorem C* at p′ = p/(p - 1) ∈ (1, 2)
    have hq1 : 1 < p / (p - 1) := by rw [lt_div_iff₀ (by linarith)]; linarith
    have hq2 : p / (p - 1) < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
    have : Fact (1 ≤ ENNReal.ofReal (p / (p - 1))) :=
      ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le⟩
    obtain ⟨Q, -⟩ := GKSharp.Cited.hv2000_riesz_norm (p / (p - 1)) hq1
    rw [pencilNorm_dual hp P Q, Complex.star_def, Complex.conj_ofReal, ← gk_dual p hp]
    exact hCstar _ Q hq1 hq2 lam hl0 hl1
  · -- p = 2
    subst hp2
    rw [pencilNorm, norm_pencil_two rfl P 1 ρ, gk, gkPair_two]

end ThmClass

end GKSharp
