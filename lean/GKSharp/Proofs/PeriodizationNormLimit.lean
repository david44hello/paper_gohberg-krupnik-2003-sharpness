/- norm inequality transferred through the literal periodization limits.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.NormTransference

namespace GKSharp.Proofs.PeriodizationNormLimit

open GKSharp.RealLineFourier GKSharp.Proofs.NormTransference MeasureTheory Filter Topology Set

theorem scaled_circlePower_eq {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (f : SchwartzMap ℝ ℂ) (N : ℕ) (F : C(Circ, ℂ))
    (hF : ∀ t : ℝ, F (t : Circ) = periodized f N t) :
    (2 * Real.pi * N) * circlePower p (periodized f N) =
      (N : ℝ) * ‖DensityLp.toLpT p F‖ ^ p := by
  rw [circle_norm_rpow hp F]
  unfold circlePower
  simp_rw [← hF]
  field_simp

theorem schwartz_norm_le_of_periodization {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 0 < p) (f g : SchwartzMap ℝ ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hlimit : ∀ u : SchwartzMap ℝ ℂ,
      Tendsto (fun N : ℕ => (2 * Real.pi * N) * circlePower p (periodized u N)) atTop
        (𝓝 (∫ x : ℝ, ‖u x‖ ^ p)))
    (hbound : ∀ N : ℕ, 0 < N → ∃ F G : C(Circ, ℂ),
      (∀ t : ℝ, F (t : Circ) = periodized f N t) ∧
      (∀ t : ℝ, G (t : Circ) = periodized g N t) ∧
      ‖DensityLp.toLpT p G‖ ≤ K * ‖DensityLp.toLpT p F‖) :
    ‖g.toLp (ENNReal.ofReal p) volume‖ ≤ K * ‖f.toLp (ENNReal.ofReal p) volume‖ := by
  have hI : (∫ x : ℝ, ‖g x‖ ^ p) ≤ K ^ p * ∫ x : ℝ, ‖f x‖ ^ p := by
    apply le_of_tendsto_of_tendsto (hlimit g) ((hlimit f).const_mul (K ^ p))
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    obtain ⟨F, G, hF, hG, hFG⟩ := hbound N hN
    rw [scaled_circlePower_eq hp g N G hG, scaled_circlePower_eq hp f N F hF]
    have hpow := Real.rpow_le_rpow (norm_nonneg _) hFG hp.le
    rw [Real.mul_rpow hK (norm_nonneg _)] at hpow
    calc (N : ℝ) * ‖DensityLp.toLpT p G‖ ^ p
        ≤ (N : ℝ) * (K ^ p * ‖DensityLp.toLpT p F‖ ^ p) :=
          mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg N)
      _ = K ^ p * ((N : ℝ) * ‖DensityLp.toLpT p F‖ ^ p) := by ring
  rw [← schwartz_norm_rpow p hp g, ← schwartz_norm_rpow p hp f,
    ← Real.mul_rpow hK (norm_nonneg _)] at hI
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg hK (norm_nonneg _)) hp).mp hI

end GKSharp.Proofs.PeriodizationNormLimit

#print axioms GKSharp.Proofs.PeriodizationNormLimit.schwartz_norm_le_of_periodization
