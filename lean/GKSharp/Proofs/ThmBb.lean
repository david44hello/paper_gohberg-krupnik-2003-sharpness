/- Theorem B (b), P019_paper.tex l.134: "If p < p₀ or p > p₀′, then ‖P₊ + λP₋‖_p > GK_p(λ) for every λ < 1
close enough to 1" (proof: Proposition F and duality, sec5_sharp_inequality.tex l.180). Inputs: the named checks of
p0_spec (CheckOmegaNeg, CheckOmegaRoot); cited: HKV2003 Thm 2.1 (inside Proposition Q / O04) and HV2000 (duality).
Copyright (C) Dave Goel 2026--now.

  p < p₀ (so 1 < p < p₀ < b₀ < 2): Ω(p) < 0 (p0_spec), hence h(p, λ) = m_GK(0) - K < 0 for λ ∈ (1 - ε, 1)
  (omega_negative_eventual_h, "Proposition F"). Then the first equivalence of Proposition Q fails at t = 0
  (K cos 0 = K > m_GK(0)), so ‖P₊ + λP₋‖_p ≠ GK_p(λ), and GK_p(λ) ≤ ‖P₊ + λP₋‖_p (O04) makes it strict.
  p > p₀′ = p₀/(p₀ - 1): p′ = p/(p - 1) ∈ (1, p₀); N_p(λ) = N_{p′}(λ̄) = N_{p′}(λ) (pencilNorm_dual, HV2000 gives a
  projection at p′) and GK_{p′} = GK_p (gk_dual), so the first case at p′ gives the claim with the same ε. -/
import GKSharp.Proofs.Sec4Near
import GKSharp.Proofs.Sec4aEndpoint
import GKSharp.Proofs.PropositionQFull
import GKSharp.Proofs.GKLowerAll
import GKSharp.Proofs.GKRoot
import GKSharp.Proofs.PencilDual
import GKSharp.Cited.HV2000
import GKSharp.ComputerChecked

open Set GKSharp.Threshold GKSharp.ComputerChecked

namespace GKSharp

namespace ThmBb

/-- "Proposition F": for `1 < p < 2` with `Ω(p) < 0`, `GK_p(λ) < ‖P₊ + λP₋‖_p` for `λ < 1` near `1`. -/
theorem gk_lt_norm_of_omega_neg {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p < 2)
    (P : RieszProjection p) (homega : omega p < 0) :
    ∃ ε > 0, ∀ lam : ℝ, 1 - ε < lam → lam < 1 → gk p lam < pencilNorm P lam := by
  obtain ⟨eps, heps, hh⟩ := omega_negative_eventual_h_proved p hp hp2 homega
  refine ⟨min eps 1, lt_min heps one_pos, fun lam hlo hhi => ?_⟩
  have hlam : lam ∈ Ico (-1 : ℝ) 1 := ⟨by linarith [min_le_right eps 1], hhi⟩
  have hneg := hh lam (by linarith [min_le_left eps 1]) hhi
  refine lt_of_le_of_ne (slice_O04_proved hp P lam) (fun heq => ?_)
  have hQ := ((sec4_prop_Q_proved p P hp hp2 lam hlam).1.mp heq.symm) 0
    ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
  simp only [abs_zero, mul_zero, Real.cos_zero, mul_one] at hQ
  have hdef : Threshold.h p lam = Threshold.obstacle p lam 0 - kConst p lam := rfl
  linarith

/-- **Theorem B (b)**, P019_paper.tex l.134, GIVEN CheckOmegaNeg and CheckOmegaRoot. -/
theorem thm_B_b_proved (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p)
    (hout : p < Threshold.p0 ∨ Threshold.p0 / (Threshold.p0 - 1) < p) :
    ∃ ε > 0, ∀ lam : ℝ, 1 - ε < lam → lam < 1 → gk p lam < pencilNorm P lam := by
  obtain ⟨-, ha0, hb0, -, hneg, -⟩ := p0_spec_proved hn hr
  have hp0 : 1 < Threshold.p0 := lt_trans (by norm_num [Threshold.a0]) ha0
  have hp02 : Threshold.p0 < 2 := hb0.trans (by norm_num [Threshold.b0])
  rcases hout with hlt | hgt
  · exact gk_lt_norm_of_omega_neg hp (hlt.trans hp02) P (hneg p ⟨hp, hlt⟩)
  · -- duality: `p′ = p/(p − 1) ∈ (1, p₀)`
    have hq1 : 1 < p / (p - 1) := by rw [lt_div_iff₀ (by linarith)]; linarith
    have hq0 : p / (p - 1) < Threshold.p0 := by
      rw [div_lt_iff₀ (by linarith)] at hgt ⊢
      nlinarith
    have : Fact (1 ≤ ENNReal.ofReal (p / (p - 1))) :=
      ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le⟩
    obtain ⟨Q, -⟩ := GKSharp.Cited.hv2000_riesz_norm (p / (p - 1)) hq1
    obtain ⟨ε, hε, hQ⟩ := gk_lt_norm_of_omega_neg hq1 (hq0.trans hp02) Q (hneg _ ⟨hq1, hq0⟩)
    refine ⟨ε, hε, fun lam hlo hhi => ?_⟩
    rw [pencilNorm_dual hp P Q, Complex.star_def, Complex.conj_ofReal, ← gk_dual p hp]
    exact hQ lam hlo hhi

end ThmBb

end GKSharp
