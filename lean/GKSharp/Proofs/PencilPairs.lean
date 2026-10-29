/- GKSharp/Proofs/PencilPairs.lean - O08: the actual pencil norm bound `N_p(ρ) ≤ C` holds iff every polynomial pair
`(z, w)`, `w(0) = 0`, has `∫ G_C(z, w) ≥ 0` (sec2_obstacle.tex:38-41).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.PencilDual
import GKSharp.Proofs.Pencil
import GKSharp.Proofs.PolynomialPairs

namespace GKSharp

open MeasureTheory

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- On a trigonometric polynomial the pencil is the finite sum `P₊c + ρ P₋c`. -/
theorem pencil_tC (P : RieszProjection p) (ρ : ℂ) (c : ℤ →₀ ℂ) :
    pencil P 1 ρ (DensityLp.toLpT p (DensityLp.tC c)) =
      DensityLp.toLpT p (DensityLp.pC c + ρ • DensityLp.mC c) := by
  apply DensityLp.fourier_ext
  intro m
  rw [coeff_pencil, toLpT_add, toLpT_smul, coeff_add, coeff_smul, DensityLp.coeff_toLpT, DensityLp.coeff_toLpT,
    DensityLp.coeff_toLpT, DensityLp.coeff_tC, DensityLp.coeff_pC, DensityLp.coeff_mC]
  by_cases hm : 0 ≤ m
  · simp [hm, not_lt.mpr hm]
  · simp [hm, lt_of_not_ge hm]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- The `L^p` norm of a continuous function as an interval integral over `[0, 2π]`. -/
theorem norm_toLpT_eq [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p) (φ : C(Circ, ℂ)) :
    ‖DensityLp.toLpT p φ‖ = (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖φ θ‖ ^ p) ^ (1 / p) := by
  rw [Lp.norm_def, eLpNorm_congr_ae (DensityLp.coeFn_toLpT φ), DensityLp.eLpNorm_circ hp φ.continuous,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (intervalIntegral.integral_nonneg (by positivity)
      fun _ _ => by positivity) _)]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- `a^{1/p} ≤ C b^{1/p} ↔ a ≤ C^p b` for `a, b, C ≥ 0`, `0 < p`. -/
theorem rpow_inv_le_iff {a b C : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C) :
    a ^ (1 / p) ≤ C * b ^ (1 / p) ↔ a ≤ C ^ p * b := by
  have e : C * b ^ (1 / p) = (C ^ p * b) ^ (1 / p) := by
    rw [Real.mul_rpow (by positivity) hb, ← Real.rpow_mul hC, mul_one_div_cancel hp.ne', Real.rpow_one]
  rw [e]
  exact Real.rpow_le_rpow_iff ha (by positivity) (by positivity)

/-- The pencil-norm test on one trigonometric polynomial, as an integral inequality. -/
theorem pencil_tC_bound_iff (hp : 0 < p) (P : RieszProjection p) (ρ : ℂ) {C : ℝ} (hC : 0 ≤ C) (c : ℤ →₀ ℂ) :
    ‖pencil P 1 ρ (DensityLp.toLpT p (DensityLp.tC c))‖ ≤ C * ‖DensityLp.toLpT p (DensityLp.tC c)‖ ↔
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖Pplus c θ + ρ * Pminus c θ‖ ^ p ≤
        C ^ p * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖trig c θ‖ ^ p := by
  rw [pencil_tC, norm_toLpT_eq hp, norm_toLpT_eq hp]
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul, DensityLp.pC_coe,
    DensityLp.mC_coe, DensityLp.tC_coe]
  exact rpow_inv_le_iff hp (intervalIntegral.integral_nonneg (by positivity) fun _ _ => by positivity)
    (intervalIntegral.integral_nonneg (by positivity) fun _ _ => by positivity) hC

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- If `(z, w)` is the polynomial pair of `c`, the pair integral is `C^p ∫|f|^p - ∫|P₊f + ρP₋f|^p`. -/
theorem integral_pairObstacle_eq (hp : 0 < p) (C : ℝ) (ρ : ℂ) (c : ℤ →₀ ℂ) (z w : Polynomial ℂ)
    (hzw : ∀ t, Pplus c t = z.eval (unitPoint t) ∧ Pminus c t = star (w.eval (unitPoint t))) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), pairObstacle p C ρ (z.eval (unitPoint t)) (w.eval (unitPoint t)) =
      C ^ p * (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖trig c θ‖ ^ p) -
        ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖Pplus c θ + ρ * Pminus c θ‖ ^ p := by
  have hpt : ∀ t, pairObstacle p C ρ (z.eval (unitPoint t)) (w.eval (unitPoint t)) =
      C ^ p * ‖trig c t‖ ^ p - ‖Pplus c t + ρ * Pminus c t‖ ^ p := by
    intro t
    rw [pairObstacle, ← (hzw t).1, ← (hzw t).2, trig_eq_add]
  have hcont : ∀ F : ℝ → ℂ, Continuous F → Continuous fun θ => ‖F θ‖ ^ p :=
    fun F hF => hF.norm.rpow_const fun _ => Or.inr hp.le
  have htrig : Continuous (trig c) := by
    have h : trig c = fun θ => Pplus c θ + Pminus c θ := funext (trig_eq_add c)
    rw [h]
    exact (continuous_Pplus c).add (continuous_Pminus c)
  have h1 : IntervalIntegrable (fun θ => C ^ p * ‖trig c θ‖ ^ p) volume 0 (2 * Real.pi) :=
    (continuous_const.mul (hcont _ htrig)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ => ‖Pplus c θ + ρ * Pminus c θ‖ ^ p) volume 0 (2 * Real.pi) :=
    (hcont (fun θ => Pplus c θ + ρ * Pminus c θ)
      ((continuous_Pplus c).add (continuous_const.mul (continuous_Pminus c)))).intervalIntegrable _ _
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]

/-- O08, sec2_obstacle.tex:38-41: for the actual pencil and `C ≥ 0`, `N_p(ρ) ≤ C` iff every polynomial pair
`(z, w)` with `w(0) = 0` satisfies `∫₀^{2π} (C^p |z + w̄|^p - |z + ρ w̄|^p) dt ≥ 0` (on the unit circle). -/
theorem norm_iff_polynomial_pairs (hp : 1 < p) (P : RieszProjection p) (ρ : ℂ) (C : ℝ) (hC : 0 ≤ C) :
    pencilNorm P ρ ≤ C ↔ PolynomialPairBound p C ρ := by
  have hp0 : 0 < p := by linarith
  rw [← pencil_bound_iff P ρ hC, pencil_bound_iff_trig]
  simp_rw [pencil_tC_bound_iff hp0 P ρ hC]
  obtain ⟨hfwd, hbwd⟩ := polynomial_pair_correspondence
  constructor
  · intro h z w hw
    obtain ⟨c, hc⟩ := hbwd z w hw
    rw [integral_pairObstacle_eq hp0 C ρ c z w hc, sub_nonneg]
    exact h c
  · intro h c
    obtain ⟨z, w, hw, hc⟩ := hfwd c
    have h0 := h z w hw
    rwa [integral_pairObstacle_eq hp0 C ρ c z w hc, sub_nonneg] at h0

end GKSharp
