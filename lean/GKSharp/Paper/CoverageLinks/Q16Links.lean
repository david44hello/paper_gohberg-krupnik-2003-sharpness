/- Coverage links for the Q16 places of short v3.90 whose printed claim already has an installed row (or, for Step 4
of Proposition 5.12, the proved step itself): each link states the printed claim and is proved from it. -/
import GKSharp.Paper.Statements

namespace GKSharp.CoverageLinks.Q16Links

open GKSharp GKSharp.Paper GKSharp.Threshold GKSharp.ComputerChecked Set Filter
open scoped Topology

/-- Coverage link: short_v3.90/P019_paper.tex:81 "For $p\ne2$ the inequality is strict for every non-real ratio
(Theorem 3.2)": every non-real ratio fails for `p ≠ 2` (from the row `thm_A`). -/
theorem cover_q16_intro_nonreal {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p ≠ 2)
    (P : RieszProjection p) {ρ : ℂ} (hρ : ρ.im ≠ 0) : gk p ρ < pencilNorm P ρ :=
  thm_A hp hp2 P hρ

/-- Coverage link: short_v3.90/P019_paper.tex:81 "These include the ratios of all real pairs $a,b$ with $ab\ne0$
($|\rho|=1$, $\rho\ne\pm1$)": for real `a, b` the ratio `ρ = (a + ib)/(a − ib)` is unimodular, and a failure there has non-real `ρ`
(from the rows `normcorr_ratio_unimodular` and `q15_normcorr_real_ratio`). -/
theorem cover_q16_intro_real_ab {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p)
    (a b : ℝ) (hab : (a : ℂ) - Complex.I * b ≠ 0) :
    ‖((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b)‖ = 1 ∧
    (gk p (((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b)) <
        pencilNorm P (((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b)) →
      (((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b)).im ≠ 0) :=
  ⟨normcorr_ratio_unimodular a b hab, (q15_normcorr_real_ratio hp P a b hab).2.2.2.2⟩

/-- Coverage link: short_v3.90/P019_paper.tex:82 "The bound is sharp for every real $\lambda\le0$: Theorem 5.1 treats
$-1\le\lambda\le0$, recovering the classical values at $\lambda=-1$ [Pich] and $\lambda=0$ [HV], and $\lambda<-1$ follows
by reciprocal symmetry"
(from the rows `thm_C1` and `thm_classification_nonpositive`). -/
theorem cover_q16_intro_nonpositive {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) :
    (∀ lam : ℝ, -1 ≤ lam → lam ≤ 0 → pencilNorm P lam = gk p lam) ∧
    (∀ lam : ℝ, lam < -1 → pencilNorm P lam = gk p lam) :=
  ⟨fun _ hl hl0 => thm_C1 hp P hl hl0,
    fun lam hl => thm_classification_nonpositive hp P lam (by linarith)⟩

/-- Coverage link: short_v3.90/P019_paper.tex:111 "(d) If $1<p<2$ and $0<\lambda<1$, then $N_p(\lambda)=\GK_p(\lambda)$ if
and only if both conditions in (1.1) hold", l.113 "part (d) as Theorem 5.3; for $p>2$ part (d) applies with $p'$ in
place of $p$" (from the row `thm_classification_tests`:
for `1 < p < 2` the tests (1.1); for `p > 2` the tests at `p′ = p/(p − 1)`; its hypotheses are the computer checks of
that row). -/
theorem cover_q16_intro_two_tests (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hcd : CheckCornerDerivatives) (hct : CheckCornerTails)
    (hbm : CheckStripBulkMiddle) (hbt : CheckStripBulkTails)
    (hc : CheckLocalF) (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) :
    (p < 2 → ∀ lam : ℝ, 0 < lam → lam < 1 →
      (pencilNorm P lam = gk p lam ↔
        (∀ x : ℝ, 0 < x → kConst p lam * x ^ (p / 2) ≤ gk p lam ^ p * (1 + x) ^ p - (1 + lam * x) ^ p) ∧
          lam < lambdaLoc p)) ∧
    (2 < p → ∀ lam : ℝ, 0 < lam → lam < 1 →
      (pencilNorm P lam = gk p lam ↔
        (∀ x : ℝ, 0 < x → kConst (p / (p - 1)) lam * x ^ (p / (p - 1) / 2) ≤
            gk (p / (p - 1)) lam ^ (p / (p - 1)) * (1 + x) ^ (p / (p - 1)) - (1 + lam * x) ^ (p / (p - 1))) ∧
          lam < lambdaLoc (p / (p - 1)))) :=
  thm_classification_tests hn hr hcd hct hbm hbt hc hb hs hp P

/-- Coverage link: short_v3.90/P019_paper.tex:128 "for every $\lambda\in(-1,1)$ when $3-\sqrt3\le p<2$, the function
$K_f$ is strictly decreasing; the second case uses the product formula for the sine" (from the row `lemma_Bplus`,
Lemma 5.10; the first case of that sentence, `λ ≤ 0`, is Lemma 5.9, row `lemma_Bneg`). -/
theorem cover_q16_intro_bplus_decreasing {p lam : ℝ} (hp1 : 3 - Real.sqrt 3 ≤ p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) :=
  lemma_Bplus hp1 hp2 hl hl1

/-- Coverage link: short_v3.90/sec5d_monotone.tex:157-158 "Let $3 - \sqrt3 \le p < 2$. For $\lambda \in (-1, 1)$, $K_f$ is
strictly decreasing by Lemma 5.10, and Propositions 5.12 and 4.2 give $N_p(\lambda) = \GK_p(\lambda)$": for `3 − √3 ≤ p < 2` and
`−1 < λ < 1`, `N_p(λ) = GK_p(λ)` (from the rows `lemma_Bplus`, `prop_reduction` and the criterion `sec4_prop_Q`, whose
second equivalence is `𝒟_C ≥ 0` on `ℂ`). -/
theorem cover_q16_intro_bplus_sharp {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p)
    (hp1 : 3 - Real.sqrt 3 ≤ p) (hp2 : p < 2) {lam : ℝ} (hl : -1 < lam) (hl1 : lam < 1) :
    pencilNorm P lam = gk p lam := by
  have hs : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hp : 1 < p := by linarith
  exact ((sec4_prop_Q p P hp hp2 lam ⟨hl.le, hl1⟩).2).mpr
    (prop_reduction hp hp2 hl.le hl1 (lemma_Bplus hp1 hp2 hl hl1)).1

/-- Coverage link: short_v3.90/P019_paper.tex:128 "For $p<4/3$ a power series with positive coefficients shows that
$K_f$ has at most one turning point" (Lemma 5.11; from the row `lemma_U`). -/
theorem cover_q16_intro_U_shape {p : ℝ} (hp1 : 1 < p) (hp2 : p < 4 / 3) :
    StrictMonoOn (monoPsi (p / (2 - p))) (Set.Ioo 0 (Real.pi / 2)) ∧
    ∀ lam ∈ Set.Ioo (0 : ℝ) 1, StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) ∨
      ∃ θl ∈ Set.Ioo 0 Real.pi, StrictMonoOn (curveKf p lam) (Set.Ioc 0 θl) ∧
        StrictAntiOn (curveKf p lam) (Set.Ico θl Real.pi) :=
  lemma_U hp1 hp2

/-- Coverage link: short_v3.90/P019_paper.tex:128 "Since $3-\sqrt3<4/3$, these two ranges of $p$ cover $(1,2)$" (from the row
`sec5_strip_endpoint`, `3 − √3 < 317/250`, and `317/250 < 4/3`). -/
theorem cover_q16_intro_ranges_cover :
    3 - Real.sqrt 3 < (4 / 3 : ℝ) ∧ ∀ p ∈ Set.Ioo (1 : ℝ) 2, p < 4 / 3 ∨ 3 - Real.sqrt 3 ≤ p := by
  have h : 3 - Real.sqrt 3 < (4 / 3 : ℝ) := sec5_strip_endpoint.trans (by norm_num)
  refine ⟨h, fun p _ => ?_⟩
  rcases lt_or_ge p (4 / 3) with hlt | hge
  · exact Or.inl hlt
  · exact Or.inr (h.le.trans hge)

/-- Coverage link: short_v3.90/P019_paper.tex:128 "Interval arithmetic, again with analytic bounds at the ends of the ranges, also proves the signs of $\Omega$, the enclosure of $p_c$ and strict inequality at the local threshold, including the range just below $p_c$" (from the rows `p0_spec`
(Proposition 4.3), `pc_spec` (Lemma 4.6), `sec4_prop_edge` (Proposition 4.7, every `1 < p < p_c`) and `boundary_sliver`
(the range `1.2134 ≤ p < p_c`); their hypotheses are the named computer checks of those rows). -/
theorem cover_q16_intro_interval_roles (hn : CheckOmegaNeg) (hr : CheckOmegaRoot) (hc : CheckLocalF)
    (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver) :
    ((∀ p ∈ Ioo (1 : ℝ) p0, omega p < 0) ∧ (∀ p ∈ Icc p0 (317 / 250), 0 ≤ omega p)) ∧
    pc ∈ Ioo (1213490304 / 1000000000 : ℝ) (1213490305 / 1000000000) ∧
    (∀ (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p), 1 < p → p < pc →
      gk p (lambdaLoc p) < pencilNorm P (lambdaLoc p)) ∧
    (∀ p ∈ Ico (6067 / 5000 : ℝ) pc, Threshold.h p (lambdaLoc p) < 0) :=
  ⟨⟨(p0_spec hn hr).2.2.2.2.1, (p0_spec hn hr).2.2.2.2.2⟩, (pc_spec hc).2.1,
    fun p _ P hp1 hp2 => (sec4_prop_edge hc hb hs p P hp1 hp2).2.2.2.2,
    fun p hp => boundary_sliver hc hs p hp⟩

/-- Coverage link: short_v3.90/sec5d_monotone.tex:146 "so $-1$ is not a local minimum. If $\mathcal{D}_C(-1)$ were $0$, then
$-1$ would be a minimum, since $\mathcal{D}_C\ge0$; hence $\mathcal{D}_C(-1)>0$" (proof of Proposition 5.12, the point
`z = −1`; the nonnegativity used is `𝒟_C ≥ 0` near `−1`, off `−1`; from the proved step `reduction_step4`). -/
theorem cover_q16_sec5_step4 {p C K lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl1 : lam < 1) (hK : 0 < K)
    (hnn : ∀ᶠ z in 𝓝[≠] (-1 : ℂ), 0 ≤ critD p C K lam z) : 0 < critD p C K lam (-1) :=
  reduction_step4 hp1 hp2 hl1 hK hnn

end GKSharp.CoverageLinks.Q16Links
