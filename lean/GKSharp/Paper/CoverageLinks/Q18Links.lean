/- Coverage links for the Q18 places (P019_paper.tex l.130, l.115, l.125) whose printed claim already has
installed rows: each link states the printed claim and is proved from them. -/
import GKSharp.Paper.Statements

namespace GKSharp.CoverageLinks.Q18Links

open GKSharp GKSharp.Paper GKSharp.Threshold GKSharp.ComputerChecked Set

/-- Coverage link: short_v3.90/P019_paper.tex:130 "For real mean-zero $u$, put $\lambda=(1-t)/(1+t)$; then
$u+itv=(1+t)(\Pp+\lambda\Pm)u$" (from the row `intro_hilbert_convention` with `a = 1`, `b = it`). Lean states it with
the paper's `H = −i(P₊ − P₋)` (`shiftedHilbert`, `H1 = −i`), for every `u` and every `t > −1`. On mean-zero `u` the
paper's `v = H₀u` equals `Hu` (P019_paper.tex l.54); `H₀` itself is not defined in Lean. -/
theorem cover_q18_intro_real_identity {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p)
    (t : ℝ) (ht : -1 < t) (u : LpT p) :
    u + ((t : ℂ) * Complex.I) • shiftedHilbert P u =
      ((1 + t : ℝ) : ℂ) • pencil P 1 (((1 - t) / (1 + t) : ℝ) : ℂ) u := by
  have hu := congrArg (fun T : LpT p →L[ℂ] LpT p => T u)
    (intro_hilbert_convention P 1 ((t : ℂ) * Complex.I)).1
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, one_smul] at hu
  rw [hu]
  have hne : (1 + t : ℝ) ≠ 0 := by linarith
  have er : (1 + t) * ((1 - t) / (1 + t)) = 1 - t := by field_simp
  have e1 : (1 : ℂ) - Complex.I * ((t : ℂ) * Complex.I) = ((1 + t : ℝ) : ℂ) * 1 := by
    push_cast
    linear_combination (-(t : ℂ)) * Complex.I_sq
  have e2 : (1 : ℂ) + Complex.I * ((t : ℂ) * Complex.I) =
      ((1 + t : ℝ) : ℂ) * (((1 - t) / (1 + t) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, er]
    push_cast
    linear_combination (t : ℂ) * Complex.I_sq
  rw [e1, e2]
  simp only [pencil, add_apply, smul_apply, smul_add, mul_smul]

/-- Coverage link: short_v3.90/P019_paper.tex:115 "Proposition 4.7 shows that the positive-axis test already fails at
$\lambda=\lambda_{\mathrm{loc}}(p)$" (for `1 < p < p_c`): the first condition of (1.1) is false at `λ = λ_loc(p)`.
From `h(λ_loc(p), p) < 0`, the first conjunct of the row `sec4_prop_edge` (its scalar part `boundary_edge_proved`,
with the same three named checks), `lambdaLoc_spec` (`0 < λ_loc(p) < 1`) and `intro_axis_test_iff`. -/
theorem cover_q18_intro_edge_axis_fails (hc : CheckLocalF) (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver)
    {p : ℝ} (hp : 1 < p) (hpc : p < pc) :
    ¬ ∀ x : ℝ, 0 < x → kConst p (lambdaLoc p) * x ^ (p / 2) ≤
        gk p (lambdaLoc p) ^ p * (1 + x) ^ p - (1 + lambdaLoc p * x) ^ p := by
  have hp2 : p < 2 := by have hh := (pc_spec hc).2.1.2; linarith
  obtain ⟨hl0, hl1⟩ := ((lambdaLoc_spec hc).1 p ⟨hp, hpc⟩).2
  rw [← intro_axis_test_iff hp hp2 hl0 hl1]
  have hneg := GKSharp.boundary_edge_proved hc hb hs p hp hpc
  simp only [Threshold.h, GKSharp.axisGap] at hneg
  intro hK
  linarith

/-- Coverage link: short_v3.90/P019_paper.tex:125 "The two contact zeros then force a $q$-subtrigonometric function below the obstacle to be a cosine on the arch between them. Its slope at the contact fixes the coefficient $K$ of~\eqref{eq:K}", and the "only if" half
of "such a function exists if and only if $K\cos(q|t|)\le m_C(t)$, $C=\GK_p(\lambda)$, on the whole circle" (Proposition
4.2) (from the rows `qsub_continuous_trigconvex`, `arch_sinusoid`, `sec4_angular_tangency` and
`angular_contact_determines_cos`). The rows are for `−1 ≤ λ < 1`; the other real ratios come by the reductions printed
at P019_paper.tex l.63 and l.113. -/
theorem cover_q18_intro_forcing (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ico (-1 : ℝ) 1)
    (ff : ℝ → ℝ) (hf : QSubtrig (q p) ff) (hminor : ∀ t : ℝ, ff t ≤ Threshold.obstacle p lam t) :
    ff (-theta p) = 0 ∧ ff (theta p) = 0 ∧
      (∀ t ∈ Icc (-theta p) (theta p), ff t = kConst p lam * Real.cos (q p * t)) ∧
      ∀ t ∈ Icc (-Real.pi) Real.pi, kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t := by
  have hq : (1 : ℝ) / 2 < q p := by unfold q; linarith
  obtain ⟨hcont, hconv⟩ := qsub_continuous_trigconvex (q p) hq ff hf
  obtain ⟨h1, h2, aa, harch⟩ := arch_sinusoid p lam hp hp2 hlam ff hcont hconv hminor
  have hK := (sec4_angular_tangency p lam hp hp2 hlam ff hf hminor aa harch).1
  subst hK
  exact ⟨h1, h2, harch, angular_contact_determines_cos p lam hp hp2 hlam ff hcont hconv hminor⟩

end GKSharp.CoverageLinks.Q18Links
