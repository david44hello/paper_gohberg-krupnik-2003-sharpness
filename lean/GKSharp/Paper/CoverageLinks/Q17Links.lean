/- Coverage links for the Q17 places (the p_c definition and the exponent regimes, P019_paper.tex l.102, l.115):
each link states the printed claim and is proved from installed rows. -/
import GKSharp.Paper.Statements

namespace GKSharp.CoverageLinks.Q17Links

open GKSharp GKSharp.Paper GKSharp.Threshold GKSharp.ComputerChecked Set

/-- Coverage link: short_v3.90/P019_paper.tex:102 "Let $p_c\approx1.213490304$ be the unique zero in $(1,2)$ of
$pp'-4(1+\cos^2(\pi/p))$ (Lemma 4.6)" (from the row `pc_spec`, given `CheckLocalF`: the certified bracket
`1.213490304 < p_c < 1.213490305` and the unique zero; `p′ = p/(p − 1)`). -/
theorem cover_q17_intro_pc (hc : CheckLocalF) :
    pc ∈ Ioo (1213490304 / 1000000000 : ℝ) (1213490305 / 1000000000) ∧
    ∀ p ∈ Ioo (1 : ℝ) 2, (p * (p / (p - 1)) - 4 * (1 + Real.cos (Real.pi / p) ^ 2) = 0 ↔ p = pc) :=
  ⟨(pc_spec hc).2.1, (pc_spec hc).2.2.1⟩

/-- Coverage link: short_v3.90/P019_paper.tex:102 "Then $T(p)>0$ exactly for $1<p<p_c$", with
`T(p) = s₀²(pp′/4 − 1 − c₀²)/c₀⁴`, `s₀ = sin(π/p)`, `c₀ = −cos(π/p)` (from the rows `q15_sec4b_T_sign` and `pc_spec`,
given `CheckLocalF`). -/
theorem cover_q17_intro_T_pos (hc : CheckLocalF) :
    ∀ p ∈ Ioo (1 : ℝ) 2,
      (0 < Real.sin (Real.pi / p) ^ 2 * (p * (p / (p - 1)) / 4 - 1 - Real.cos (Real.pi / p) ^ 2) /
          Real.cos (Real.pi / p) ^ 4 ↔ p < pc) := by
  intro p hp
  obtain ⟨h1, -, h3⟩ := q15_sec4b_T_sign p
  have hs := h3 hp.1 hp.2
  rw [← h1, ← (pc_spec hc).2.2.2.1 p hp]
  constructor
  · intro h
    have h' := sign_pos h
    rw [hs] at h'
    exact sign_eq_one_iff.mp h'
  · intro h
    have h' := sign_pos h
    rw [← hs] at h'
    exact sign_eq_one_iff.mp h'

/-- Coverage link: short_v3.90/P019_paper.tex:115 "When $p_c\le p<p_0$ the second condition is automatic, so
sharpness is equivalent to the positive-axis test" (`0 < λ < 1`; from the rows `lambdaLoc_spec` (`λ_loc = 1` on `[p_c, 2)`),
`p0_spec` (`p₀ < 2`) and `intro_tests_criterion`; the hypotheses are the computer checks of those rows). -/
theorem cover_q17_intro_regime_axis (hn : CheckOmegaNeg) (hr : CheckOmegaRoot) (hc : CheckLocalF)
    (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) (hpc : pc ≤ p) (hp0 : p < p0) :
    lambdaLoc p = 1 ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      (pencilNorm P lam = gk p lam ↔
        ∀ x : ℝ, 0 < x → kConst p lam * x ^ (p / 2) ≤ gk p lam ^ p * (1 + x) ^ p - (1 + lam * x) ^ p) := by
  have hb0 : b0 = 12336027 / 10000000 := rfl
  have hp0b := (p0_spec hn hr).2.2.1
  have hpc1 := (pc_spec hc).2.1.1
  have hp1 : 1 < p := by linarith
  have hp2 : p < 2 := by linarith
  have hloc : lambdaLoc p = 1 := (lambdaLoc_spec hc).2 p ⟨hpc, hp2⟩
  refine ⟨hloc, fun lam hl0 hl1 => ?_⟩
  rw [intro_tests_criterion hc hb hs hp1 hp2 P hl0 hl1, hloc]
  exact ⟨fun h => h.1, fun h => ⟨h, hl1⟩⟩

/-- Coverage link: short_v3.90/P019_paper.tex:115 "When $p_0\le p<2$ the bound is sharp for every real ratio"; also the
caption of Figure 2, P019_paper.tex:122 "The bound is sharp on and below the lower curve $\lambda=\lambda_1(p)$, defined for
$p<p_0$ (Section~\ref{subsec:second}), and for every $\lambda$ when $p_0\le p<2$" (the last clause; the first is the row
`sec4_lambda1_interval`) (from the rows
`thm_B_a` (every real λ for `p₀ ≤ p ≤ p₀′`) and `p0_spec` (`1 < p₀ < 2`, so `p < 2 < p₀′`); the hypotheses are the
computer checks of `thm_B_a`). -/
theorem cover_q17_intro_regime_sharp (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hcd : CheckCornerDerivatives) (hct : CheckCornerTails)
    (hbm : CheckStripBulkMiddle) (hbt : CheckStripBulkTails) (hc : CheckLocalF)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) (hp0 : p0 ≤ p) (hp2 : p < 2) :
    ∀ lam : ℝ, pencilNorm P lam = gk p lam := by
  have ha0 : a0 = 12336025 / 10000000 := rfl
  have hb0 : b0 = 12336027 / 10000000 := rfl
  have hpa := (p0_spec hn hr).2.1
  have hpb := (p0_spec hn hr).2.2.1
  have hp : 1 < p := by linarith
  have hhi : p ≤ p0 / (p0 - 1) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_pos (sub_pos.mpr hp2) (show (0 : ℝ) < p0 - 1 by linarith)]
  exact thm_B_a hn hr hcd hct hbm hbt hc hp P hp0 hhi

end GKSharp.CoverageLinks.Q17Links
