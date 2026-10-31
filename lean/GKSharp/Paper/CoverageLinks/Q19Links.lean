/- Coverage links for the places of the paper (P019_paper.tex l.56, l.80, l.91-93, l.95, l.106, l.116, l.118;
sec4a_criterion.tex l.61-62; sec5_sharp_inequality.tex l.106) whose printed claim already has installed rows:
each link states the printed claim and is proved from them. -/
import GKSharp.Paper.Statements

namespace GKSharp.CoverageLinks.Q19Links

open GKSharp GKSharp.Paper GKSharp.Threshold GKSharp.ComputerChecked Set

/-- Coverage link: short_v3.70/P019_paper.tex:56 "for a single projection, whose norm $1/\sin(\pi/p)$ was conjectured
by Gohberg and Krupnik and found by Hollenbeck and Verbitsky~\cite{HV}" (the cited input `hv2000_riesz_norm`; for every
Riesz projection `P`, `‖P₊‖_p = 1/sin(π/p)` is the link `cover_classical_projection_norm`). -/
theorem cover_q19_intro_hv_norm {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) :
    ∃ P : RieszProjection p, ‖P.plus‖ = 1 / Real.sin (Real.pi / p) :=
  GKSharp.Cited.hv2000_riesz_norm p hp

/-- Coverage link: short_v3.70/P019_paper.tex:80 "For $p\ne2$ the inequality is strict for every non-real ratio
(Theorem~\ref{thm:A}). These include the ratios of all real pairs $a,b$ with $ab\ne0$ ($|\rho|=1$, $\rho\ne\pm1$)": for real `a, b ≠ 0` the ratio
`ρ = (a + ib)/(a − ib)` is unimodular, not `±1`, non-real, and fails for `p ≠ 2` (from the rows
`normcorr_ratio_unimodular`, `q15_normcorr_real_ratio` and `thm_A`). -/
theorem cover_q19_intro_real_pairs {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p ≠ 2)
    (P : RieszProjection p) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    let ρ := ((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b)
    ‖ρ‖ = 1 ∧ ρ ≠ 1 ∧ ρ ≠ -1 ∧ ρ.im ≠ 0 ∧ gk p ρ < pencilNorm P ρ := by
  intro ρ
  have hab : (a : ℂ) - Complex.I * b ≠ 0 := by
    intro h
    apply ha
    have hre := congrArg Complex.re h
    simpa using hre
  obtain ⟨hreal, h1, hm1, -, -⟩ := q15_normcorr_real_ratio hp P a b hab
  have hne1 : ρ ≠ 1 := fun h => hb (h1.mp h)
  have hnem1 : ρ ≠ -1 := fun h => ha (hm1.mp h)
  have him : ρ.im ≠ 0 := fun h => (hreal.mp h).elim hne1 hnem1
  exact ⟨normcorr_ratio_unimodular a b hab, hne1, hnem1, him, thm_A hp hp2 P him⟩

/-- Coverage link: short_v3.70/P019_paper.tex:91-93 "The first condition is the restriction to $z=x>0$ of the inequality"
`(*)` "with the principal branch of $z^q$. Proposition~\ref{prop:Q}, where this inequality is labeled $(*)$, shows that it
is equivalent to sharpness for these $\lambda$. We call the first condition in \eqref{eq:introcrit} the
\emph{positive-axis test}" (`1 < p < 2`,
`0 < λ < 1`, `C = GK_p(λ)`; from the row `sec4_prop_Q`; `Re z^q` is `reQPow`, principal argument). -/
theorem cover_q19_intro_axis_test_star {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p < 2)
    (P : RieszProjection p) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    (∀ x : ℝ, 0 < x → critD p (gk p lam) (kConst p lam) lam (x : ℂ) =
      gk p lam ^ p * (1 + x) ^ p - (1 + lam * x) ^ p - kConst p lam * x ^ (p / 2)) ∧
    (pencilNorm P lam = gk p lam ↔ ∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) := by
  refine ⟨fun x hx => ?_, (sec4_prop_Q p P hp hp2 lam ⟨by linarith, hl1⟩).2⟩
  unfold critD
  have e1 : ‖1 + (x : ℂ)‖ = 1 + x := by
    rw [show (1 : ℂ) + x = ((1 + x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have e2 : ‖1 + (lam : ℂ) * x‖ = 1 + lam * x := by
    rw [show (1 : ℂ) + lam * x = ((1 + lam * x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have e5 : reQPow (x : ℂ) (p / 2) = x ^ (p / 2) := by
    rw [reQPow, Complex.norm_real, Real.norm_of_nonneg hx.le, Complex.arg_ofReal_of_nonneg hx.le, mul_zero,
      Real.cos_zero, mul_one]
  rw [e1, e2, e5]

/-- Coverage link: short_v3.70/P019_paper.tex:116 "trigonometric convexity shows that such a function exists if and only
if $K\cos(q|t|)\le m_C(t)$, $C=\GK_p(\lambda)$, on the whole circle. This reduces sharpness to the pointwise inequality
$(*)$ in one complex variable (Proposition~\ref{prop:Q})" (`1 < p < 2`, `−1 ≤ λ < 1`; "such a function" = a `q`-subtrigonometric
angular function below the obstacle; from the rows `slice_O18` (Theorem 2.2), `slice_O04`, `sec3_gk_gt_max` and
`sec4_prop_Q`). -/
theorem cover_q19_intro_angular_iff {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p < 2)
    (P : RieszProjection p) {lam : ℝ} (hlam : lam ∈ Ico (-1 : ℝ) 1) :
    ((∃ φ : ℝ → ℝ, QSubtrig (p / 2) φ ∧ ∀ t, φ t ≤ Threshold.obstacle p lam t) ↔
      ∀ t ∈ Icc (-Real.pi) Real.pi, kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t) ∧
    (pencilNorm P lam = gk p lam ↔ ∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) := by
  have hρ : (lam : ℂ) ≠ 1 := fun h => hlam.2.ne (by exact_mod_cast h)
  have hmax : max 1 ‖(lam : ℂ)‖ < gk p lam := sec3_gk_gt_max hp hp2.ne hρ
  obtain ⟨hQ1, hQ2⟩ := sec4_prop_Q p P hp hp2 lam hlam
  have h18 := (slice_O18 hp P (lam : ℂ) (gk p lam) hmax).1
  refine ⟨⟨?_, ?_⟩, hQ2⟩
  · rintro ⟨φ, hφ, hle⟩
    exact hQ1.1 (le_antisymm (h18.2 ⟨φ, hφ, hle⟩) (slice_O04 hp P (lam : ℂ)))
  · intro hcos
    exact h18.1 (hQ1.2 hcos).le

/-- Coverage link: short_v3.70/P019_paper.tex:118 "After the M\"obius change of variable $w=(1+\lambda z)/(1+z)$, the left
side of $(*)$ equals, up to a positive factor, $(1-\lambda)^p(C^p-|w|^p)-K\operatorname{Re}Q^q$ with
$Q=(w-\lambda)(1-\bar w)$. On a circle $|w|=\mathrm{const}$ the first term is constant and $Q$ runs over an ellipse"
(any `C`, `K`, `λ < 1`, `z ≠ −1`; from the rows `eq_5_1` and `sec5_ellipse`). -/
theorem cover_q19_intro_mobius_ellipse {p C K lam : ℝ} (hp : 0 < p) (hl : lam < 1) :
    (∀ z : ℂ, z ≠ -1 → 0 < ‖1 + z‖ ^ p / (1 - lam) ^ p ∧
      critD p C K lam z = ‖1 + z‖ ^ p / (1 - lam) ^ p *
        ((1 - lam) ^ p * (C ^ p - ‖mobW lam z‖ ^ p) - K * reQPow (mobQ lam (mobW lam z)) (p / 2))) ∧
    ∀ ρ φ : ℝ, mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) =
      ((-(ρ ^ 2 + lam) + (1 + lam) * ρ * Real.cos φ : ℝ) : ℂ) + (((1 - lam) * ρ * Real.sin φ : ℝ) : ℂ) * Complex.I := by
  refine ⟨fun z hz => ⟨?_, (eq_5_1 p C K hp hl hz).2.2⟩, fun ρ φ => (sec5_ellipse lam ρ φ 0).1⟩
  have h1 : 0 < ‖1 + z‖ := norm_pos_iff.mpr (fun h => hz (by linear_combination h))
  exact div_pos (Real.rpow_pos_of_pos h1 p) (Real.rpow_pos_of_pos (by linarith) p)

/-- Coverage link: short_v3.70/P019_paper.tex:118 "If $K_f$ decreases throughout, the normalized left side has its only
minimum at $\theta_0$, where it vanishes. If $K_f$ first increases and then decreases, and $K_f'(\theta_0)<0$, which is
what $\lambda<\lambda_{\mathrm{loc}}(p)$ gives, then the only other possible minimum is the end of the curve on the
positive real axis, which the positive-axis test controls" (`1 < p < 2`; from the rows `prop_reduction`,
`sec5e_Kf_slope_routeB`, `sec5e_Lambda_pos` and `q15_sec5e_star_holds`; the second case under the hypotheses of
Theorem 5.3, positive-axis test and `λ < λ_loc(p)`). -/
theorem cover_q19_intro_reduction_cases {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (-1 ≤ lam → lam < 1 → StrictAntiOn (curveKf p lam) (Ioo 0 Real.pi) →
      (∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) ∧
      ∀ z : ℂ, critD p (gk p lam) (kConst p lam) lam z = 0 →
        z = curveZ p lam (Real.pi / p) ∨ z = (starRingEnd ℂ) (curveZ p lam (Real.pi / p))) ∧
    (0 < lam → lam < 1 → kConst p lam ≤ GKSharp.obstacle p (gk p lam) (lam : ℂ) 0 → lam < lambdaLoc p →
      deriv (curveKf p lam) (Real.pi / p) < 0 ∧
      (∀ θ ∈ Ioo 0 Real.pi, θ ≠ Real.pi / p →
        0 < mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam θ)) / (1 - lam) ^ p) ∧
      ∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) :=
  ⟨fun hl hl1 hdec => prop_reduction hp1 hp2 hl hl1 hdec,
    fun hl0 hl1 hh hloc => ⟨sec5e_Kf_slope_routeB hp1 hp2 hl0 hl1 hloc, sec5e_Lambda_pos hp1 hp2 hl0 hl1 hh hloc,
      (q15_sec5e_star_holds hp1 hp2 hl0 hl1 hh hloc).1⟩⟩

/-- Coverage link: short_v3.70/sec5_sharp_inequality.tex:106 "By \eqref{eq:dPhi} below, $K_f(\theta)$ is the value of $K$
at which $\Lambda$ is stationary at $\theta$" (`Λ = Φ(w(θ))/(1−λ)^p`, any `C`, `−1 ≤ λ < 1`, `0 < θ < π`; from the
row `eq_5_8`). -/
theorem cover_q19_sec5_Kf_stationary {p C K lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    deriv (fun x => mobPhi p C K lam (mobW lam (curveZ p lam x)) / (1 - lam) ^ p) θ = 0 ↔ K = curveKf p lam θ := by
  obtain ⟨-, -, hd, hpos⟩ := eq_5_8 (C := C) (K := K) hp1 hp2 hl hl1 hθ0 hθ
  rw [hd.deriv, mul_eq_zero, sub_eq_zero]
  exact ⟨fun h => h.resolve_left hpos.ne', Or.inr⟩

/-- Coverage link: short_v3.70/sec4a_criterion.tex:61-62 "for $\zeta=1/z$ one has $|\zeta|^p\mathcal{D}_C(1/\zeta)=C^p|\zeta+1|^p
-|\zeta+\lambda|^p-K|\zeta|^q\cos(q\arg\zeta)$, so $(*)$ holds if and only if
$r^{-q}\bigl(C^p|1+re^{it}|^p-|\lambda+re^{it}|^p\bigr)\ge K\cos(qt)$ for all $r>0$ and $|t|\le\pi$" (any `K`, `C > 1`;
the second part with `ζ = re^{it}`, `t = arg ζ` (principal), multiplied by `r^q > 0`; from `critD_inv_factor` and
`critD_nonneg_iff_radial`, the proof of the row `obstacle_cos_iff_critD`). -/
theorem cover_q19_prop_Q_inversion {p C K lam : ℝ} (hp : 1 < p) (hC : 1 < C) :
    (∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ ^ p * critD p C K lam ζ⁻¹ =
      C ^ p * ‖ζ + 1‖ ^ p - ‖ζ + (lam : ℂ)‖ ^ p - K * (‖ζ‖ ^ (p / 2) * Real.cos (p / 2 * Complex.arg ζ))) ∧
    ((∀ z : ℂ, 0 ≤ critD p C K lam z) ↔ ∀ ζ : ℂ, ζ ≠ 0 →
      K * (‖ζ‖ ^ (p / 2) * Real.cos (p / 2 * Complex.arg ζ)) ≤ C ^ p * ‖ζ + 1‖ ^ p - ‖ζ + (lam : ℂ)‖ ^ p) := by
  have hG : ∀ ζ : ℂ, obstacleG p C (lam : ℂ) ζ = C ^ p * ‖ζ + 1‖ ^ p - ‖ζ + (lam : ℂ)‖ ^ p := by
    intro ζ
    unfold obstacleG
    rw [add_comm (1 : ℂ) ζ, add_comm (lam : ℂ) ζ]
  have hR : ∀ ζ : ℂ, reQPow ζ (p / 2) = ‖ζ‖ ^ (p / 2) * Real.cos (p / 2 * Complex.arg ζ) := fun ζ => rfl
  refine ⟨fun ζ hζ => ?_, ?_⟩
  · have h := critD_inv_factor p C K lam (inv_ne_zero hζ)
    rw [inv_inv] at h
    have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
    have hcancel : ‖ζ‖ ^ p * ‖ζ⁻¹‖ ^ p = 1 := by
      rw [norm_inv, Real.inv_rpow hn.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hn p).ne']
    rw [h, ← mul_assoc, hcancel, one_mul, hG, hR]
  · rw [critD_nonneg_iff_radial (by linarith) hC K lam]
    simp only [hG, hR]

/-- Coverage link: short_v3.70/P019_paper.tex:95 "Propositions~\ref{prop:F} and~\ref{prop:strip} show that $\Omega$ has
exactly one zero $p_0\approx1.2336026$ in $(1,1.268]$, with $\Omega<0$ on $(1,p_0)$ and $\Omega>0$ on $(p_0,1.268]$" (the
two signs; "exactly one zero" is the uniqueness conjunct of `p0_spec`; `1.268 = 317/250`; from the row
`p0_spec`, given its two computer checks). -/
theorem cover_q20_intro_omega_signs (hn : CheckOmegaNeg) (hr : CheckOmegaRoot) :
    (∀ p ∈ Ioo (1 : ℝ) p0, omega p < 0) ∧ ∀ p ∈ Ioc p0 (317 / 250 : ℝ), 0 < omega p := by
  obtain ⟨-, ha0, -, huniq, hneg, hnonneg⟩ := p0_spec hn hr
  refine ⟨hneg, fun p hp => ?_⟩
  have h1 : (1 : ℝ) < p := lt_trans (lt_trans (by norm_num [a0]) ha0) hp.1
  rcases (hnonneg p ⟨hp.1.le, hp.2⟩).lt_or_eq with h | h
  · exact h
  · exact absurd ((huniq p ⟨h1, hp.2⟩).mp h.symm) hp.1.ne'

/-- Coverage link: short_v3.70/P019_paper.tex:93 "when $\Omega(p)<0$ it fails for all $\lambda$ close enough to $1$
(Proposition~\ref{prop:F})" (also l.85: "A number $\Omega(p)$ controls the first condition below as
$\lambda\uparrow1$"): if `Ω(p) < 0`, the positive-axis test fails for every `λ < 1` close
enough to 1 (`1 < p < 2`; from the rows `omega_negative_eventual_h` and `intro_axis_test_iff`). -/
theorem cover_q20_intro_omega_axis {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (homega : omega p < 0) :
    ∃ eps > 0, ∀ lam : ℝ, 1 - eps < lam → lam < 1 →
      ¬ ∀ x : ℝ, 0 < x → kConst p lam * x ^ (p / 2) ≤ gk p lam ^ p * (1 + x) ^ p - (1 + lam * x) ^ p := by
  obtain ⟨eps, heps, hneg⟩ := omega_negative_eventual_h p hp hp2 homega
  refine ⟨min eps 1, lt_min heps one_pos, fun lam hlam hl1 htest => ?_⟩
  have hl0 : 0 < lam := by linarith [min_le_right eps 1]
  have hh := hneg lam (by linarith [min_le_left eps 1]) hl1
  have hK := (intro_axis_test_iff hp hp2 hl0 hl1).mpr htest
  simp only [Threshold.h, GKSharp.axisGap] at hh
  linarith

/-- Coverage link: short_v3.70/P019_paper.tex:106 "When $p_c\le p<p_0$ the second condition is automatic, so
sharpness is equivalent to the positive-axis test, and it fails for $\lambda$ close to $1$" (the last clause, here for every
`1 < p < p₀`; from the rows `p0_spec`, given its two computer checks, `omega_negative_eventual_h` and
`intro_axis_test_iff`). -/
theorem cover_q20_intro_regime_fails_near_one (hn : CheckOmegaNeg) (hr : CheckOmegaRoot) {p : ℝ}
    (hp : 1 < p) (hp0 : p < p0) :
    ∃ eps > 0, ∀ lam : ℝ, 1 - eps < lam → lam < 1 →
      ¬ ∀ x : ℝ, 0 < x → kConst p lam * x ^ (p / 2) ≤ gk p lam ^ p * (1 + x) ^ p - (1 + lam * x) ^ p := by
  obtain ⟨-, -, hb0, -, hneg, -⟩ := p0_spec hn hr
  have hb2 : b0 < 2 := by norm_num [b0]
  exact cover_q20_intro_omega_axis hp (by linarith) (hneg p ⟨hp, hp0⟩)

end GKSharp.CoverageLinks.Q19Links
