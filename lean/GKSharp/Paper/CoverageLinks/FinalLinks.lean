/- Coverage links for the places of the paper added at the final re-reference pass (P019_paper.tex l.95, l.113, l.119, l.156;
sec4a_criterion.tex l.45-47, l.79-80; sec4b_failure.tex l.90, l.100, l.108-109, l.141; sec5_sharp_inequality.tex
l.53-54) whose printed claim already has
installed rows: each link states the printed claim and is proved from them. -/
import GKSharp.Paper.Statements
import GKSharp.Paper.CoverageLinks.SliceA_PotentialDerived2

namespace GKSharp.CoverageLinks.FinalLinks

open GKSharp GKSharp.Paper GKSharp.Threshold GKSharp.ComputerChecked Set

/-- Coverage link: short_v3.40/P019_paper.tex:95 "Since the bound is sharp for every real ratio when $3-\sqrt3\le p<2$
(Section~\ref{subsec:proofsC1B}) and $3-\sqrt3<1.268$" (the first clause; the second is the row
`sec5_strip_endpoint`): for `3 − √3 ≤ p < 2`, `N_p(λ) = GK_p(λ)` for every real `λ`, with no computer check (from the
rows `lemma_Bplus`, `prop_reduction`, `sec4_prop_Q` for `−1 < λ < 1`, `thm_classification_nonpositive` for `λ ≤ 0`,
`sec5_lambda_one` for `λ = 1` and `thm_classification_reciprocal` for `λ > 1`; the route of sec5d_monotone.tex
l.157-160). -/
theorem cover_final_sqrt3_every_real {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p)
    (hp1 : 3 - Real.sqrt 3 ≤ p) (hp2 : p < 2) : ∀ lam : ℝ, pencilNorm P lam = gk p lam := by
  have hs : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hp : 1 < p := by linarith
  have hunit : ∀ lam : ℝ, -1 < lam → lam < 1 → pencilNorm P lam = gk p lam := fun lam hl hl1 =>
    ((sec4_prop_Q p P hp hp2 lam ⟨hl.le, hl1⟩).2).mpr
      (prop_reduction hp hp2 hl.le hl1 (lemma_Bplus hp1 hp2 hl hl1)).1
  intro lam
  rcases le_or_gt lam 0 with h0 | h0
  · exact thm_classification_nonpositive hp P lam h0
  rcases lt_trichotomy lam 1 with h1 | h1 | h1
  · exact hunit lam (by linarith) h1
  · subst h1
    rw [Complex.ofReal_one, (sec5_lambda_one (p := p) P).1, (sec5_lambda_one (p := p) P).2]
  · refine (thm_classification_reciprocal P lam h1).mpr (hunit (1 / lam) ?_ ?_)
    · have : 0 < 1 / lam := by positivity
      linarith
    · exact (div_lt_one (by linarith)).mpr h1

/-- Coverage link: short_v3.40/P019_paper.tex:119 "It is delicate at $p=p_0$ as $\lambda\to1$, where the leading term of
the test vanishes" (with sec4b_failure.tex l.141 "whose minimum over $s$ is $\Omega(p)$"): at `δ = 0` the function `g`
of Section 5.6 is at least `Ω(p)` for every `0 < s < 1`, with equality at `s = s_*`, and `Ω(p₀) = 0` (from the rows
`etilde_zero_minimum`, `g_zero` and `p0_spec`; the last given its two computer checks). -/
theorem cover_final_intro_delicate (hn : CheckOmegaNeg) (hr : CheckOmegaRoot) :
    (∀ p : ℝ, 1 < p → p < 2 → (∀ s ∈ Ioo (0 : ℝ) 1, omega p ≤ g p 0 s) ∧ g p 0 (sStar p) = omega p) ∧
      omega p0 = 0 := by
  refine ⟨fun p hp hp2 => ⟨fun s hs => ?_, ?_⟩, ?_⟩
  · obtain ⟨he, hle⟩ := etilde_zero_minimum p s hp hp2 hs
    rw [← he]
    exact hle
  · rw [g_zero p (sStar p) hp hp2]
    rfl
  · obtain ⟨-, ha0, hb0, huniq, -, -⟩ := p0_spec hn hr
    have h1 : (1 : ℝ) < p0 := lt_trans (by norm_num [a0]) ha0
    have h2 : p0 ≤ 317 / 250 := le_trans hb0.le (by norm_num [b0])
    exact (huniq p0 ⟨h1, h2⟩).mpr rfl

/-- Coverage link: short_v3.40/sec4b_failure.tex:141 "Interval arithmetic also gives $T(p)\le0.015^2$ on
$[1.2134,1.2134904]$" (calculation_certificates.tex l.30, Table 1 row "$T$": "$T(p)\le0.015^2$"), in exactly the printed
form (from the kernel-proved row `sec4_local_gap_kernel`, which states `2√(max(T(p), 0)) ≤ 0.03`; no computer check). -/
theorem cover_final_T_gap (p : ℝ) (hp : p ∈ Icc (6067 / 5000 : ℝ) (12134904 / 10000000)) :
    localD2 p ≤ (15 / 1000 : ℝ) ^ 2 := by
  have hrow := sec4_local_gap_kernel p hp
  have hs : Real.sqrt (max (localD2 p) 0) ≤ 15 / 1000 := by linarith
  have hsq : max (localD2 p) 0 = Real.sqrt (max (localD2 p) 0) ^ 2 :=
    (Real.sq_sqrt (le_max_right _ _)).symm
  calc localD2 p ≤ max (localD2 p) 0 := le_max_left _ _
    _ = Real.sqrt (max (localD2 p) 0) ^ 2 := hsq
    _ ≤ (15 / 1000 : ℝ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2

/-- Coverage link: short_v3.40/sec4a_criterion.tex:45-47 "With $r_* = c_0 (C^2 - \lambda)/(C^2 - 1)$ and
\[ |\zeta_* + 1|^2 = r_*^2 - 2 r_*^2/\kappa + 1 = 1+\kappa c_0^2(\kappa-2) = \frac{(1 - \lambda)^2 (C^2 + \lambda)}{(C^2 - 1)(C^2 - \lambda)} , \]
by $\kappa^2c_0^2=\kappa^2-R^2=(C^2-\lambda^2)/(C^2-1)$ (tangency, proof of Lemma 4.1)" (`1 < p < 2`, `−1 ≤ λ < 1`,
`C = GK_p(λ)`, `κ = (C² − λ)/(C² − 1)`, `R = C(1 − λ)/(C² − 1)`; the outer forms of `|ζ_* + 1|²` are the link
`cover_contact_base_identities`; `κ²c₀² = (C² − λ²)/(C² − 1)` uses the quadratic for `C`, row `eq_GKreal`). -/
theorem cover_final_contact_values {p lam : ℝ} (hp : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    contactRadius p lam = contactKappa (gk p (lam : ℂ)) lam * cs p ∧
    ‖(contactRadius p lam : ℂ) * unitPoint (Real.pi / p) + 1‖ ^ 2 =
      1 + contactKappa (gk p (lam : ℂ)) lam * cs p ^ 2 * (contactKappa (gk p (lam : ℂ)) lam - 2) ∧
    contactKappa (gk p (lam : ℂ)) lam ^ 2 * cs p ^ 2 =
      contactKappa (gk p (lam : ℂ)) lam ^ 2 - (gk p (lam : ℂ) * (1 - lam) / (gk p (lam : ℂ) ^ 2 - 1)) ^ 2 ∧
    contactKappa (gk p (lam : ℂ)) lam ^ 2 - (gk p (lam : ℂ) * (1 - lam) / (gk p (lam : ℂ) ^ 2 - 1)) ^ 2 =
      (gk p (lam : ℂ) ^ 2 - lam ^ 2) / (gk p (lam : ℂ) ^ 2 - 1) := by
  have hθ1 : Real.pi / 2 < Real.pi / p := by
    rw [div_lt_div_iff₀ two_pos (by linarith)]
    nlinarith [Real.pi_pos]
  have hθ2 : Real.pi / p < Real.pi := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (Real.pi / p) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hθ1 (by linarith [Real.pi_pos])
  have hne : (lam : ℂ) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hC1 : 1 < gk p (lam : ℂ) :=
    lt_of_le_of_lt (le_max_left _ _) (sec3_gk_gt_max hp (ne_of_lt hp2) hne)
  have hGK := (eq_GKreal hp hl1).1
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp.le⟩
  have hbase := GKSharp.CoverageLinks.SliceA_PotentialDerived2.GKSharp.Paper.cover_contact_base_identities
    (p := p) hp hp2 lam ⟨hl, hl1⟩
  simp only at hbase
  obtain ⟨-, -, hN, -⟩ := hbase
  have hr : contactRadius p lam = contactKappa (gk p (lam : ℂ)) lam * cs p := by
    unfold contactRadius cs
    rw [abs_of_neg hcos]
  generalize hCdef : gk p (lam : ℂ) = C at hC1 hGK hN hr ⊢
  have hden : 0 < C ^ 2 - 1 := by nlinarith
  have hκpos : 0 < contactKappa C lam := by
    unfold contactKappa
    exact div_pos (by nlinarith) hden
  have hc2 : Real.cos (Real.pi / p) ^ 2 * (C ^ 2 - lam) ^ 2 = (C ^ 2 - 1) * (C ^ 2 - lam ^ 2) := by
    linear_combination (C ^ 2 - lam) ^ 2 * Real.sin_sq_add_cos_sq (Real.pi / p) +
      ((1 - lam) * C + Real.sin (Real.pi / p) * (C ^ 2 - lam)) * hGK
  have h4 : contactKappa C lam ^ 2 - (C * (1 - lam) / (C ^ 2 - 1)) ^ 2 = (C ^ 2 - lam ^ 2) / (C ^ 2 - 1) := by
    unfold contactKappa
    field_simp
    ring
  refine ⟨hr, ?_, ?_, h4⟩
  · rw [hN, hr]
    field_simp
    ring
  · rw [h4]
    unfold contactKappa cs
    rw [neg_sq, div_pow, div_mul_eq_mul_div, mul_comm, hc2]
    field_simp

/-- Coverage link: short_v3.40/sec4a_criterion.tex:79-80 (Proposition 4.3) "Moreover $\Omega < 0$ on
$(1, 1.2336025]$" (`1.2336025 = a0`; from the row `omega_endpoint` on `(1, 1.001]` and the computer check
`CheckOmegaNeg` on `[1.001, 1.2336025]`, as in the paper's proof). -/
theorem cover_final_omega_neg_upto_a0 (hn : CheckOmegaNeg) : ∀ p ∈ Ioc (1 : ℝ) a0, omega p < 0 := by
  intro p hp
  rcases le_or_gt p (1001 / 1000) with hle | hgt
  · exact omega_endpoint p hp.1 hle
  · exact hn p ⟨hgt.le, hp.2⟩

/-- Coverage link: short_v3.40/sec4b_failure.tex:90 "So for $\lambda\le0$ the second-order mechanism of
Theorem~\ref{thm:L} gives no obstruction, in agreement with Theorem~\ref{thm:C1}" (`1 < p < 2`, `−1 < λ ≤ 0`): the
hypothesis (4.2) of Theorem 4.4 fails (its left side is `< 1`, rows `strict_jordan_pp` and `λ ≤ 0`) and
`μ_*″(θ₀) > 0` for `μ_*(t) = Γ_C(y_*(t), t)` with the branch `y_*` of `∂_yΓ_C = 0` of the proof of Theorem 4.4
(rows `corollary_L0` and `contact_envelope`); Theorem 5.1 is the row `thm_C1`. -/
theorem cover_final_lambda_nonpos_no_obstruction {p lam : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioc (-1 : ℝ) 0) :
    localTest p lam < 1 ∧ 0 < muSecond p lam ∧
      ∃ branch : ℝ → ℝ, ∃ eps > 0, branch (theta p) = yContact p lam ∧
        (∀ t ∈ Ioo (theta p - eps) (theta p + eps), dy (gammaGK p lam) (branch t) t = 0) ∧
        0 < deriv (deriv (fun t => gammaGK p lam (branch t) t)) (theta p) := by
  have hmu := corollary_L0 p lam hp hp2 hlam
  obtain ⟨branch, eps, heps, hb0, -, hdy, hsec⟩ :=
    contact_envelope p lam hp hp2 ⟨hlam.1, by linarith [hlam.2]⟩
  refine ⟨?_, hmu, branch, eps, heps, hb0, fun t ht => (hdy t ht).1, hsec ▸ hmu⟩
  have hj := strict_jordan_pp p hp hp2
  have hneg : 4 * lam * cs p ^ 4 / (1 + lam) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hlam.2]) (by positivity)) (by positivity)
  unfold localTest
  linarith

/-- Coverage link: short_v3.40/sec4b_failure.tex:108-109 "We have $h(0, p) > 0$: by Theorem~\ref{thm:C1}, equality in
$(*)$ at $\lambda = 0$ holds only at $z = e^{\pm i\theta_0}/r_*$" (`1 < p < 2`, `θ₀ = π/p`, `r_*` = contactRadius; the
rows `thm_C1_equality` and `lemma_contact`; the next reason, `r^{-q}G(r) → +∞` as `r → 0` and `r → ∞`, is the row
`sec3_radial_limits`; `h(0, p) > 0` is the row `axis_zero_positive`). -/
theorem cover_final_lambda_zero_equality {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (z : ℂ)
    (hz : critD p (gk p 0) (kConst p 0) 0 z = 0) :
    z = 1 / ((contactRadius p 0 : ℂ) * Complex.exp (((Real.pi / p : ℝ) : ℂ) * Complex.I)) ∨
      z = 1 / ((contactRadius p 0 : ℂ) * Complex.exp (-(((Real.pi / p : ℝ) : ℂ) * Complex.I))) := by
  have hpt := (lemma_contact hp hp2 (by norm_num : (-1 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1)).2.2.2.1
  rcases (thm_C1_equality hp hp2 (by norm_num) le_rfl).2 z hz with h | h
  · exact Or.inl (h.trans hpt)
  · refine Or.inr ?_
    rw [h, hpt, map_div₀, map_one, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    ring_nf

/-- Coverage link: short_v3.40/P019_paper.tex:156 "Let $p_0$ and $p_0'$ be as in Theorem~\ref{thm:classification}
($p_0\approx1.2336026$, $p_0'\approx5.2807742$)" (the printed values are approximations; Lean proves the brackets
`1.2336025 < p₀ < 1.2336027` and `5.280772 < p₀′ < 5.280777`, `p₀′ = p₀/(p₀ − 1)`, from the row `p0_spec`, given the
same two computer checks). -/
theorem cover_final_p0_dual_bracket (hn : CheckOmegaNeg) (hr : CheckOmegaRoot) :
    (12336025 / 10000000 : ℝ) < p0 ∧ p0 < 12336027 / 10000000 ∧
      (5280772 / 1000000 : ℝ) < dual p0 ∧ dual p0 < 5280777 / 1000000 := by
  obtain ⟨-, ha, hb, -⟩ := p0_spec hn hr
  simp only [a0, b0] at ha hb
  have h1 : 0 < p0 - 1 := by linarith
  unfold dual
  refine ⟨ha, hb, ?_, ?_⟩
  · rw [lt_div_iff₀ h1]
    linarith
  · rw [div_lt_iff₀ h1]
    linarith

/-- Coverage link: short_v3.40/sec4b_failure.tex:100 "On $(1, 1 + 10^{-6}]$, $\mathcal{F} \ge 1/(p-1) - 8 > 0$, since
$(p-2)^2/(p-1)=1/(p-1)+p-3$" (the reason; the bound itself is the row `localF_endpoint_one`). -/
theorem cover_final_F_near_one_identity {p : ℝ} (hp : 1 < p) :
    (p - 2) ^ 2 / (p - 1) = 1 / (p - 1) + p - 3 := by
  have h : p - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Coverage link: short_v3.40/sec5_sharp_inequality.tex:53-54 "For $\lambda \ne 0$ its zeros have product
$1/\lambda$: for $\lambda < 0$ the other zero is negative" ("its" = of `D(θ, ·)`; `−1 ≤ λ < 0`, `0 < θ < π`): `R(θ)`
and `1/(λR(θ))` are zeros of `D(θ, ·)` with product `1/λ`, and `1/(λR(θ)) < 0` (from the rows
`sec5_critical_zero_product` and `sec5_critical_root_formula`, which gives `R(θ) > 0`). -/
theorem cover_final_other_zero_negative {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hl : -1 ≤ lam) (hl0 : lam < 0) :
    curveD p lam θ (curveR p lam θ) = 0 ∧ curveD p lam θ (1 / (lam * curveR p lam θ)) = 0 ∧
      curveR p lam θ * (1 / (lam * curveR p lam θ)) = 1 / lam ∧ 1 / (lam * curveR p lam θ) < 0 := by
  obtain ⟨-, -, hR, -, hD⟩ := sec5_critical_root_formula hp1 hp2 hθ0 hθ hl (by linarith)
  have hfac := (sec5_critical_zero_product hp1 hp2 hθ0 hθ hl (by linarith) hl0.ne).1
  refine ⟨hD, ?_, ?_, div_neg_of_pos_of_neg one_pos (mul_neg_of_neg_of_pos hl0 hR)⟩
  · rw [hfac]
    ring
  · field_simp

/-- Coverage link: short_v3.40/P019_paper.tex:113 (caption of Figure 1) "For $p<p_c$ it is not sharp on and above the
upper curve $\lambda=\lambda_{\mathrm{loc}}(p)$; this curve reaches $\lambda=1$ at $p=p_c$." (`1 < p < p_c`,
`λ_loc(p) ≤ λ < 1`): `N_p(λ) > GK_p(λ)`, at `λ = λ_loc(p)` from the row `sec4_prop_edge` (Proposition 4.7) and for
`λ > λ_loc(p)` from the rows `local_threshold_iff` and `sec4_thm_L` (Theorem 4.4); and `λ_loc(p_c) = 1` (from the rows
`lambdaLoc_spec` and `pc_spec`). Given the three computer checks of Proposition 4.7. -/
theorem cover_final_caption_upper_curve (hc : CheckLocalF) (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) :
    (1 < p → p < pc → ∀ lam : ℝ, lambdaLoc p ≤ lam → lam < 1 → gk p lam < pencilNorm P lam) ∧
      lambdaLoc pc = 1 := by
  have hpc2 : pc < 2 := by
    have hhi := (pc_spec hc).2.1.2
    linarith
  refine ⟨fun hp hpc lam hlo hhi => ?_, (lambdaLoc_spec hc).2 pc ⟨le_rfl, hpc2⟩⟩
  have hp2 : p < 2 := lt_trans hpc hpc2
  rcases hlo.lt_or_eq with hlt | heq
  · have hl0 : 0 < lam := lt_trans ((lambdaLoc_spec hc).1 p ⟨hp, hpc⟩).2.1 hlt
    exact sec4_thm_L p P hp hp2 lam ⟨hl0, hhi⟩ ((local_threshold_iff p lam hp hp2 ⟨hl0, hhi⟩).mpr hlt)
  · rw [← heq]
    exact (sec4_prop_edge hc hb hs p P hp hpc).2.2.2.2

end GKSharp.CoverageLinks.FinalLinks
