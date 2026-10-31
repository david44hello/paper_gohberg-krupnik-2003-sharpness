# AUDIT_NOTES.md — notes for readers of AUDIT.md (paper short v3.70)
## version 1.20 - 20261030_2210 - short v3.70: tags; caption wording in note 19.
## version 1.10 - 20261030_1240 - short v3.40: pointers re-pointed; notes on the Figure 1 caption (18, 19).
## version 1.00 - 20261030_0630 - first: routes, definitions, pointers, cited inputs, approximations.

These notes list the places where the Lean development differs in form from the paper, or where a reader of AUDIT.md
needs one more sentence. Every claim of the paper is a row of GKSharp/Paper/Statements.lean (listed in AUDIT.md) or a
coverage link in GKSharp/Paper/CoverageLinks/. File and line numbers refer to the frozen short v3.70 sources.

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
11. In Section 5.6 (sec5f_strip.tex l.25), Lemma 5.13 uses the functions T₁, k and g for δ < 0 through their analytic
   continuations. Lean defines these functions by their closed forms, with C(δ) the root near 1 of
   s₀C² − δC − s₀(1 − δ) = 0 (`cDelta`) for both signs of δ; for δ < 0 these closed forms are the analytic
   continuations (row `g_analytic_zero`).

## Definitions

12. p₀: the paper (Section 1) defines p₀ as the zero of Ω in (1, 1.268]. Lean defines p₀ as the least zero of Ω in (1, 2)
   (`p0 = sInf omegaZeros`); the row `p0_spec` proves that it is the only zero of Ω in (1, 1.268], so the two agree.
13. λ_loc: for 1 < p < 2 the paper (P019_paper.tex l.87-88) branches on T(p) > 0, Lean on F(p) > 0; these agree, since
   T = s₀²F/(4c₀⁴) (row `q15_sec4b_T_sign`).

## Pointers, cited inputs, approximations, motivation

14. Line pointers inside comments under Proofs/ refer to earlier drafts (the draft named in the comment, or an earlier one
   when none is named) and are not maintained; the maintained pointers to the posted version are in Paper/, Cited/,
   Defs/, ComputerChecked.lean and AUDIT.md.
15. The classification uses exactly two cited theorems (`hkv_thm21`, `hv2000_riesz_norm`). The real-line correspondence
   link `cover_slice_N01_nonvacuity` also uses `hv2000_thm31_schwartz`, the real-line form of the same
   Hollenbeck-Verbitsky norm (HV Theorem 3.1).
16. The values p₀ ≈ 1.2336026 and p₀′ ≈ 5.2807742 (P019_paper.tex l.156) are printed approximations. Lean proves the
   brackets 1.2336025 < p₀ < 1.2336027 and 5.280772 < p₀′ < 5.280777 (link `cover_final_p0_dual_bracket`, given the two
   computer checks of `p0_spec`).
17. The sentence "Near (p₀, s_*), where Ξ(0, σ) is close to 0, positivity must come from the term e₂(σ)η²"
   (sec5f_strip.tex l.54, Proposition 5.14, Case 1) is motivation, not a claim; it has no row.

## Figure 1

18. Figure 1 (P019_paper.tex l.110-115, drawn by fig_regions.tex) is an illustration, and Lean has no row for the
   drawing. Its lower curve λ = λ₁(p) "was computed numerically, for illustration only, and the proofs do not use it"
   (l.113); its upper curve is a list of sample points of the closed form for λ_loc; the marked axis values p_c and p₀
   are the approximations 1.213490304 and 1.2336026. The claims of the caption are covered by the row
   `sec4_lambda1_interval` and the link `cover_q17_intro_regime_sharp` (sharp on and below λ₁(p) for p < p₀, and for
   every λ when p₀ ≤ p < 2), the link `cover_final_caption_upper_curve` (not sharp on and above λ_loc(p) for p < p_c;
   λ_loc(p_c) = 1) and the row `thm_classification` (clauses (c) and (d), for the hatched band).
19. In the caption (l.113), "its outcome is known only in part" and "We do not know whether it is sharp anywhere
   in the band" say what is not known; they are not claims and have no row.
