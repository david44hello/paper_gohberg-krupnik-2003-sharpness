# AUDIT_NOTES.md — notes for readers of AUDIT.md (paper short v3.90)
## version 1.60 - 20261101_2020 - spacing in note 22. (1.50: short v3.90, the paper's Z1 vs Lean's unchanged tOne.)
## version 1.30 - 20261031_1010 - short v3.80: pointers re-pointed; new Figure 1 (note 20); old Figure 1 is Figure 2.
## version 1.20 - 20261030_2210 - short v3.70: tags; caption wording in note 19.

These notes list the places where the Lean development differs in form from the paper, or where a reader of AUDIT.md
needs one more sentence. Every claim of the paper is a row of GKSharp/Paper/Statements.lean (listed in AUDIT.md) or a
coverage link in GKSharp/Paper/CoverageLinks/. File and line numbers refer to the frozen short v3.90 sources.

## Routes

Where the Lean proof takes a different route from the paper (the statements are the same):

1. In sec2_obstacle.tex l.100, the paper excludes φ = −∞ because the potential would then be −∞ on a ray, which is not
   polar. Lean proves φ finite by an angular comparison with sinusoids on arcs shorter than π/q, and the connectedness of
   the circle (`homogeneous_finite_of_comparison`).
2. In the proof of Theorem 2.2, "Only if" (sec2_obstacle.tex l.85), the paper writes h = h₀∏(ζ − e^{iγ_j}) with h₀
   zero-free on the closed disc and takes h₀^{1/2} and each (ζ − e^{iγ_j})^{1/2}. Lean writes h = C∏(1 − uζ) with every
   |u| ≤ 1 (one factor for each root of g outside the open disc) and takes the principal square root of each factor,
   whose real part is ≥ 0 on the closed disc (link `cover_slice_O21`, GKSharp/Proofs/BlaschkeLift.lean).
3. In the proof of Proposition 4.2, "Only if" (sec4a_criterion.tex l.66-74), the paper bounds φ below on [θ₀, π] with
   [7, Lemma 3.1] (one-sided derivatives) and [7, Lemma 3.2] (the sinusoid with the value and right derivative of φ at
   θ₀). Lean uses the three-point sine form of q-convexity together with φ = K cos(qt) on the arch [−θ₀, θ₀]
   (`cosine_support_of_arch`); it needs no derivative of φ at θ₀.
4. Besides [7, Theorem 2.1] (an axiom, `hkv_thm21`), the paper cites [7, Lemma 3.1, Lemma 3.2, Proposition 3.4(1),
   Proposition 3.4(2)] in proofs; Lean proves these steps directly (`sec4_angular_tangency`,
   `sec4_cosine_exterior_support`, `sec3_arch` with `slice_O30`, `arch_sinusoid`). [7, Proposition 3.3] is cited in
   sec2_obstacle.tex l.69 only for an equivalent restatement of q-subtrigonometric functions; Lean does not use it.
5. In Lean, Theorem 4.4 takes the contact facts at ζ_* (Γ_C = ∂_yΓ_C = 0 < ∂²_yΓ_C) and the unique zero at the contact
   radius from a direct computation, not from Lemma 4.1; the ray maximum of sec4b_failure.tex l.27-28 is proved
   separately by a direct identity on the ray. This also covers "by the uniqueness in Lemma 4.1" (sec4b_failure.tex l.30):
   Lean proves that r_* = κc₀ is the larger root by its closed form (`contactRadius_interior`).
6. In the proof of Theorem 5.3, "If" (sec5e_cstar.tex l.15-17), the paper obtains K_f′(θ₀) < 0 from Lemma 4.6(b), the
   identities at θ₀ and Lemma 5.8; these are the rows `sec4_lemma_Pc_b`, `sec5e_routeB_identities` and
   `sec5e_Kf_slope_routeB`. Lean's proof of Theorem 5.3 itself obtains K_f′(θ₀) < 0 through a Hessian argument on the
   critical curve (`CstarSlope.sec5e_Kf_slope_proved` in GKSharp/Proofs/CstarSlope.lean, which uses
   `CstarLambdaSecond.sec5e_Lambda_second_proved`). Both routes are proved. The lemma `CstarBranch.sec5e_mGK_eq_mu_proved`
   (m_GK = μ_* near θ₀) belongs to the same earlier argument and is no longer used by any row.
7. In the proof of Lemma 5.7 (sec5d_monotone.tex l.35), the paper obtains Π₁ from its zeros, its leading coefficient and
   its values at X = ±1. Lean compares the coefficients of X², X and 1 directly (row `q15_sec5d_Pi_coefficients`); the
   printed identities for Π₁ are the row `q19_sec5d_q_closed`.
8. In Lemma 5.11 (sec5d_monotone.tex l.99), the paper expands cos(2mω) in t = sin²ω because it is an analytic function of
   ω² near 0. Lean sums Σ yₙtⁿ from the recurrence (the coefficients are bounded), shows that the sum solves the
   differential equation, and identifies it with cos(2mω) by an energy argument (`sec5d_Y_series`,
   GKSharp/Proofs/MonotoneUC.lean).
9. In the proof of Proposition 5.12, at the point z = −1 (sec5d_monotone.tex l.145-146), Lean takes the one-sided slope
   of 𝒟_C along the unit circle z = e^{i(π−s)}, s ↓ 0, instead of along −1 + iy.
10. For sE(η) ≤ σ ≤ s in sec5f_strip.tex l.64, Lean writes s = σE(ση)/E(η) with E(x) = (1 − e^{−x})/x and uses E ≤ 1
   and E decreasing, instead of −log(1 − x) ≥ x and the concavity of log.
11. In Section 5.6 (sec5f_strip.tex l.25), Lemma 5.13 uses the functions Z₁, k and g for δ < 0 through their analytic
   continuations. Lean defines these functions by their closed forms, with C(δ) the root near 1 of
   s₀C² − δC − s₀(1 − δ) = 0 (`cDelta`) for both signs of δ; for δ < 0 these closed forms are the analytic
   continuations (row `g_analytic_zero`). The paper renamed T₁ to Z₁; Lean keeps the same closed-form quantity as
   `GKSharp.Threshold.tOne`, without a definition change.

## Definitions

12. p₀: the paper (Section 1) defines p₀ as the zero of Ω in (1, 1.268]. Lean defines p₀ as the least zero of Ω in (1, 2)
   (`p0 = sInf omegaZeros`); the row `p0_spec` proves that it is the only zero of Ω in (1, 1.268], so the two agree.
13. λ_loc: for 1 < p < 2 the paper (P019_paper.tex l.96-97) branches on T(p) > 0, Lean on F(p) > 0; these agree, since
   T = s₀²F/(4c₀⁴) (row `q15_sec4b_T_sign`).

## Pointers, cited inputs, approximations, motivation

14. Line pointers inside comments under Proofs/ refer to earlier drafts (the draft named in the comment, or an earlier one
   when none is named) and are not maintained; the maintained pointers to the posted version are in Paper/, Cited/,
   Defs/, ComputerChecked.lean and AUDIT.md.
15. The classification uses exactly two cited theorems (`hkv_thm21`, Cole's theorem in the form [HKV, Theorem 2.1];
   `hv2000_riesz_norm`, the Hollenbeck-Verbitsky norm of P₊). The real-line correspondence
   link `cover_slice_N01_nonvacuity` also uses `hv2000_thm31_schwartz`, the real-line form of the same
   Hollenbeck-Verbitsky norm (HV Theorem 3.1).
16. The values p₀ ≈ 1.2336026 and p₀′ ≈ 5.2807742 (P019_paper.tex l.168) are printed approximations. Lean proves the
   brackets 1.2336025 < p₀ < 1.2336027 and 5.280772 < p₀′ < 5.280777 (link `cover_final_p0_dual_bracket`, given the two
   computer checks of `p0_spec`).
17. The sentence "Near (p₀, s_*), where Ξ(0, σ) is close to 0, positivity must come from the term e₂(σ)η²"
   (sec5f_strip.tex l.54, Proposition 5.14, Case 1) is motivation, not a claim; it has no row.

## Figures 1 and 2

18. Figure 2 (P019_paper.tex l.119-123, drawn by fig_regions_pair.tex) is an illustration, and Lean has no row for the
   drawing. Its right panel is the (p, λ) map; its left panel, the same rectangle all hatched, shows the sentence
   "Left: before this paper, to our knowledge, no ratio $0<\lambda<1$ had been settled for $p\ne2$" (l.122), a statement
   about the literature, not a claim of the paper; it has no row. The lower curve λ = λ₁(p) "was computed numerically,
   for illustration only, and the proofs do not use it" (l.122); the upper curve is a list of sample points of the closed form for λ_loc; the marked axis values p_c and p₀
   are the approximations 1.213490304 and 1.2336026. The claims of the caption are covered by the row
   `sec4_lambda1_interval` and the link `cover_q17_intro_regime_sharp` (sharp on and below λ₁(p) for p < p₀, and for
   every λ when p₀ ≤ p < 2), the link `cover_final_caption_upper_curve` (not sharp on and above λ_loc(p) for p < p_c;
   λ_loc(p_c) = 1) and the row `thm_classification` (clauses (c) and (d), for the hatched band).
19. In the caption of Figure 2 (l.122), "its outcome is known only in part" and "We do not know whether it is sharp
   anywhere in the band" say what is not known; they are not claims and have no row. The same holds for the abstract's
   "on a band of intermediate ratios the outcome of the criterion is known only in part" (l.40); the first half of that sentence, "For
   $1<p<p_0$ the bound is sharp for all $\lambda$ near $0$", is the link `cover_final_abstract_near_zero`.
20. Figure 1 (P019_paper.tex l.88-92, drawn by fig_disk.tex) is an illustration, and Lean has no row for the drawing.
   The claims of its caption (l.91) are the links `cover_final_disk_reduction` (ratios outside the disk reduce to it),
   `cover_final_disk_before` (sharp at ρ = −1, 0, 1 for every p; the ratios of the real pairs a, b are exactly the circle
   |ρ| = 1), `cover_final_disk_lambdaLoc_bracket` (0.513 ≤ λ_loc(1.1) < 0.514), `cover_final_disk_p11` (Theorem 1.1 at
   p = 1.1: not sharp for non-real ρ and for λ_loc(1.1) ≤ λ < 1; sharp for −1 ≤ λ ≤ λ₁(1.1) and for λ = 1;
   λ₁(1.1) < λ_loc(1.1)) and `cover_final_disk_segment` (sharp on [−1, 1] for p₀ ≤ p ≤ p₀′). That the cases of the
   left panel were settled before this paper, and that [HKV, Theorem 4.1] found the exact norm on the circle, are
   statements about the literature, not claims of the paper. The value "λ₁(1.1) ≈ 0.389" "was computed numerically":
   Lean proves that λ₁(1.1) exists and lies below λ_loc(1.1), not its decimal value (the numerical run gives
   λ₁(1.1) = 0.38877…); the drawing's marked points 0.3888 and 0.5133 are the same values, for illustration.

## Changes checked for short v3.90

21. The stronger table sentence (P019_paper.tex l.70) and the abstract's l.39 say the bound is not sharp for EVERY
   real ratio below and sufficiently close to one, outside the closed exponent interval. The link
   `cover_delta390_near_one` states exactly an ε-neighborhood with universal λ, for both p < p₀ and p > p₀′,
   from the corresponding conjunct of `thm_classification`; it does not merely assert one failed ratio.
   The wording "sufficiently close" in Theorem 5.2(b) and Proposition 4.3 changes no existing type. The real-ratio
   remark of sec3_nonreal.tex l.78 now explicitly restricts Theorem 4.4 to λ > λ_loc(p), already a hypothesis of its row.
   The cosine/sine decomposition and B = 0 in sec4a_criterion.tex l.67 reduce to the same `arch_sinusoid` conclusion;
   the route comparison in notes 3–4 remains applicable. The explicit cancelling terms in sec5d_monotone.tex l.34
   cancel in the determinant identity `q15_sec5d_cleared`; the renames c_omega, g, nu and Z1 change notation, not the definitions.

22. Table 1's new sizes are recorded computer-run outputs, not Lean proofs of the execution's cell census.
   The primary interval replay logs record 141 cells for Ω<0; 1 and 35 for Ω'>0 and Ω>0; 12 and 13 cells for the two
   F sign domains, one interval enclosure for F'<0, and two root-endpoint evaluations. The sliver log records 1023
   cells. The three boundary-bulk logs record 8153 + 2682 + 6950 = 17785 certified cells. These are the successful claim
   runs, excluding deliberately refused controls. The mathematical sign conclusions remain the same explicit
   computer-check hypotheses shown in AUDIT.md. No run census is promoted to a new proved row by this comparison.
