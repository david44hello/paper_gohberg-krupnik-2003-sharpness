/- elementary norm and density foundations for real-line norm transference.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.RealLineFourier
import GKSharp.Proofs.FourierDensity

namespace GKSharp.Proofs.NormTransference

open GKSharp.RealLineFourier MeasureTheory Filter Topology Set

theorem schwartz_norm_rpow (p : ℝ) (hp : 0 < p) (f : SchwartzMap ℝ ℂ) :
    ‖f.toLp (ENNReal.ofReal p) volume‖ ^ p = ∫ x : ℝ, ‖f x‖ ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by positivity
  rw [SchwartzMap.norm_toLp' hp0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  rw [← Real.rpow_mul (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)),
    inv_mul_cancel₀ hp.ne', Real.rpow_one]

theorem circle_norm_rpow {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 0 < p) (F : C(Circ, ℂ)) :
    ‖DensityLp.toLpT p F‖ ^ p = ∫ t in (0 : ℝ)..(2 * Real.pi), ‖F (t : Circ)‖ ^ p := by
  rw [Lp.norm_def, eLpNorm_congr_ae (DensityLp.coeFn_toLpT F), DensityLp.eLpNorm_circ hp F.continuous]
  have hI : 0 ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), ‖F (t : Circ)‖ ^ p :=
    intervalIntegral.integral_nonneg (by positivity) (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _), ← Real.rpow_mul hI,
    one_div_mul_cancel hp.ne', Real.rpow_one]

theorem opNorm_le_of_separated_tests {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (A : LpR p →L[ℂ] LpR p) {K : ℝ} (hK : 0 ≤ K)
    (hdense : ∀ (u : LpR p) (ε : ℝ), 0 < ε →
      ∃ g : SchwartzMap ℝ ℂ, ‖g.toLp (ENNReal.ofReal p) volume - u‖ < ε ∧
        HasCompactSupport (paperFourier g) ∧ 0 ∉ tsupport (paperFourier g))
    (hbound : ∀ g : SchwartzMap ℝ ℂ, HasCompactSupport (paperFourier g) →
      0 ∉ tsupport (paperFourier g) →
      ‖A (g.toLp (ENNReal.ofReal p) volume)‖ ≤ K * ‖g.toLp (ENNReal.ofReal p) volume‖) :
    ‖A‖ ≤ K := by
  let S : Set (LpR p) := {u | ∃ g : SchwartzMap ℝ ℂ,
    u = g.toLp (ENNReal.ofReal p) volume ∧
      HasCompactSupport (paperFourier g) ∧ 0 ∉ tsupport (paperFourier g)}
  have hS : Dense S := by
    rw [Metric.dense_iff]
    intro u ε hε
    obtain ⟨g, hdist, hc, hz⟩ := hdense u ε hε
    exact ⟨g.toLp (ENNReal.ofReal p) volume, by simpa [Metric.mem_ball, dist_eq_norm] using hdist,
      ⟨g, rfl, hc, hz⟩⟩
  apply A.opNorm_le_bound hK
  have hclosed : IsClosed {u : LpR p | ‖A u‖ ≤ K * ‖u‖} :=
    isClosed_le A.continuous.norm (continuous_const.mul continuous_norm)
  have hsub : S ⊆ {u : LpR p | ‖A u‖ ≤ K * ‖u‖} := by
    rintro u ⟨g, rfl, hc, hz⟩
    exact hbound g hc hz
  intro u
  exact (closure_minimal hsub hclosed) (hS u)

end GKSharp.Proofs.NormTransference

#print axioms GKSharp.Proofs.NormTransference.opNorm_le_of_separated_tests
