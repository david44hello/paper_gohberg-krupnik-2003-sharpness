/- Coverage links for the Q15 places of short v3.40 whose printed claim already has an installed row of the same type:
each link states the printed claim and is proved from that row. -/
import GKSharp.Paper.Statements

namespace GKSharp.CoverageLinks.Q15Links

open GKSharp GKSharp.Paper GKSharp.Threshold GKSharp.ComputerChecked Set MeasureTheory
open scoped ComplexConjugate

/-- Coverage link: short_v3.40/sec4b_failure.tex:141 "so for $1.2134\le p<p_c$ we have ...
$1-\lambda_{\mathrm{loc}}(p)=2d/(1+d)\le2d\le0.03$" (from the row `deltaLoc_gap`; hypothesis `CheckLocalF` as
there). -/
theorem cover_q15_sec4b_sliver_gap (hc : CheckLocalF) (p : ℝ) (hp : p ∈ Ico (6067 / 5000 : ℝ) pc) :
    1 - lambdaLoc p ≤ 3 / 100 :=
  (deltaLoc_gap hc p hp).2

/-- Coverage link: short_v3.40/sec5d_monotone.tex:35 "this gives $2\sin u_1\sin u_2\,\mathcal ES=\Pi(X)$" (from the row
`sec5d_E_identity`; `u₁ = θ = 2a`, `u₂ = εθ`, `X = cos 2γ`, any `γ ∈ (b, π/2)`, `γ ≠ a`). -/
theorem cover_q15_sec5d_thus {p θ g : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2) (hga : g ≠ θ / 2) :
    2 * Real.sin θ * Real.sin ((p - 1) * θ) * monoE p (θ / 2) g * monoS p (θ / 2) g =
      monoPi (p - 1) θ (Real.cos (2 * g)) :=
  sec5d_E_identity hp1 hp2 hθ0 hθ hg hga

/-- Coverage link: short_v3.40/P019_paper.tex:58 "both projections are self-adjoint for the sesquilinear
$L^p$--$L^{p'}$ pairing $\langle f,g\rangle=\int_{\T}f\bar g\,dt/(2\pi)$" (from the row `intro_selfadjoint`; `Circ` is
`ℝ/2πℤ` with total mass `2π`). -/
theorem cover_q15_intro_pairing {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)] (hp : 1 < p)
    (hq : q = p / (p - 1)) (P : RieszProjection p) (Q : RieszProjection q) (f : LpT p) (g : LpT q) :
    let pair := fun (u v : Circ → ℂ) => (2 * Real.pi)⁻¹ * ∫ x : Circ, u x * star (v x)
    pair (P.plus f) g = pair f (Q.plus g) ∧ pair (rieszMinus P f) g = pair f (rieszMinus Q g) := by
  intro pair
  obtain ⟨h1, h2⟩ := intro_selfadjoint hp hq P Q f g
  exact ⟨by show _ * _ = _ * _; rw [h1], by show _ * _ = _ * _; rw [h2]⟩

/-- Coverage link: short_v3.40/P019_paper.tex:118 "The interior critical points form one explicit curve,
together with its inversion images when $\lambda>0$" (Section 5.1, Lemma 5.6; from the row `sec5_critical_points`). -/
theorem cover_q15_intro_critical_curve {p lam ρ φ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hρ : 0 < ρ) (hφ0 : 0 < φ) (hφ : φ < Real.pi) :
    deriv (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ = 0 ↔
      (∃ θ ∈ Set.Ioo 0 Real.pi, (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = mobW lam (curveZ p lam θ)) ∨
      (0 < lam ∧ ∃ θ ∈ Set.Ioo 0 Real.pi,
        (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = (lam : ℂ) / conj (mobW lam (curveZ p lam θ))) :=
  sec5_critical_points hp1 hp2 hl hl1 hρ hφ0 hφ

/-- Coverage link: short_v3.40/P019_paper.tex:162 "if and only if $m_{\GK}(0) \ge K$ (the first condition in (1.1))"
(from the row `intro_axis_test_iff`: `m_GK(0) ≥ K` is the first condition of (1.1)). -/
theorem cover_q15_intro_axis_condition {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1) :
    kConst p lam ≤ GKSharp.obstacle p (gk p lam) lam 0 ↔
      ∀ x : ℝ, 0 < x → kConst p lam * x ^ (p / 2) ≤ gk p lam ^ p * (1 + x) ^ p - (1 + lam * x) ^ p :=
  intro_axis_test_iff hp1 hp2 hl0 hl1

end GKSharp.CoverageLinks.Q15Links
