/- separated compact-frequency Schwartz tests are dense in L^p, frozen target slice_N10 (norm_correspondence.tex l.53, short v0.70).
Copyright (C) Dave Goel 2026--now. -/
import Mathlib

open MeasureTheory Real Filter Topology

open scoped ContDiff SchwartzMap

open FourierTransform

namespace GKSharp.Proofs.N10Density

/-! ### The fixed bump `χ`: equal to `1` on `[-1, 1]`, zero outside `(-2, 2)`. -/

/-- The fixed smooth bump on `ℝ` with inner radius `1` and outer radius `2`. -/
noncomputable def chiBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump `χ` as a real function. -/
noncomputable def chi (x : ℝ) : ℝ := chiBump x

lemma chi_contDiff : ContDiff ℝ ∞ chi := chiBump.contDiff

lemma chi_eq_one {x : ℝ} (hx : |x| ≤ 1) : chi x = 1 := by
  apply chiBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, chiBump] using hx

lemma chi_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : chi x = 0 := by
  apply chiBump.zero_of_le_dist
  simpa [Real.dist_eq, chiBump] using hx

lemma chi_nonneg (x : ℝ) : 0 ≤ chi x := chiBump.nonneg

lemma chi_le_one (x : ℝ) : chi x ≤ 1 := chiBump.le_one

lemma chi_hasCompactSupport : HasCompactSupport chi := chiBump.hasCompactSupport

lemma chi_differentiable : Differentiable ℝ chi :=
  chi_contDiff.differentiable (by simp)

lemma continuous_deriv_chi : Continuous (deriv chi) :=
  chi_contDiff.continuous_deriv (by simp)

lemma integrable_deriv_chi : Integrable (deriv chi) :=
  continuous_deriv_chi.integrable_of_hasCompactSupport chi_hasCompactSupport.deriv

/-! ### The band-pass multiplier `ψ_r(ξ) = χ(ξ/r) - χ(rξ)`. -/

/-- The band-pass multiplier `ψ_r(ξ) = χ(ξ / r) - χ(r ξ)`: compactly supported, zero near `0`. -/
noncomputable def psi (r ξ : ℝ) : ℝ := chi (ξ / r) - chi (r * ξ)

lemma psi_contDiff (r : ℝ) : ContDiff ℝ ∞ (psi r) := by
  have h1 : ContDiff ℝ ∞ (fun ξ : ℝ => chi (ξ / r)) :=
    chi_contDiff.comp (contDiff_id.div_const r)
  have h2 : ContDiff ℝ ∞ (fun ξ : ℝ => chi (r * ξ)) :=
    chi_contDiff.comp (contDiff_const.mul contDiff_id)
  exact h1.sub h2

lemma psi_eq_zero_of_large {r ξ : ℝ} (hr : 1 ≤ r) (hξ : 2 * r ≤ |ξ|) : psi r ξ = 0 := by
  have hr0 : 0 < r := by linarith
  have h1 : chi (ξ / r) = 0 := by
    apply chi_eq_zero
    rw [abs_div, abs_of_pos hr0, le_div_iff₀ hr0]
    linarith
  have h2 : chi (r * ξ) = 0 := by
    apply chi_eq_zero
    rw [abs_mul, abs_of_pos hr0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (abs_nonneg ξ)]
  simp [psi, h1, h2]

lemma psi_eq_zero_of_small {r ξ : ℝ} (hr : 1 ≤ r) (hξ : |ξ| ≤ 1 / r) : psi r ξ = 0 := by
  have hr0 : 0 < r := by linarith
  have hinv : 1 / r ≤ 1 := by rw [div_le_one hr0]; exact hr
  have h1 : chi (ξ / r) = 1 := by
    apply chi_eq_one
    rw [abs_div, abs_of_pos hr0, div_le_one hr0]
    linarith
  have h2 : chi (r * ξ) = 1 := by
    apply chi_eq_one
    rw [abs_mul, abs_of_pos hr0]
    rw [le_div_iff₀ hr0] at hξ
    nlinarith
  simp [psi, h1, h2]

lemma psi_hasCompactSupport {r : ℝ} (hr : 1 ≤ r) : HasCompactSupport (psi r) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * r)) fun ξ hξ => ?_
  apply psi_eq_zero_of_large hr
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hξ
  exact hξ.le

lemma psi_hasTemperateGrowth {r : ℝ} (hr : 1 ≤ r) : (psi r).HasTemperateGrowth :=
  (psi_hasCompactSupport hr).hasTemperateGrowth (psi_contDiff r)

lemma one_sub_psi_nonneg (r ξ : ℝ) : 0 ≤ 1 - psi r ξ := by
  have := chi_le_one (ξ / r)
  have := chi_nonneg (r * ξ)
  simp only [psi]
  linarith

lemma one_sub_psi_le_two (r ξ : ℝ) : 1 - psi r ξ ≤ 2 := by
  have := chi_nonneg (ξ / r)
  have := chi_le_one (r * ξ)
  simp only [psi]
  linarith

lemma abs_one_sub_psi_le_two (r ξ : ℝ) : |1 - psi r ξ| ≤ 2 := by
  rw [abs_of_nonneg (one_sub_psi_nonneg r ξ)]
  exact one_sub_psi_le_two r ξ

lemma eventually_one_sub_psi_eq_zero {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∀ᶠ r in atTop, 1 - psi r ξ = 0 := by
  have hξ0 : 0 < |ξ| := abs_pos.mpr hξ
  filter_upwards [eventually_ge_atTop (max 1 (max |ξ| (2 / |ξ|)))] with r hr
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have hr2 : |ξ| ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hr
  have hr3 : 2 / |ξ| ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hr
  have hr0 : 0 < r := by linarith
  have h1 : chi (ξ / r) = 1 := by
    apply chi_eq_one
    rw [abs_div, abs_of_pos hr0, div_le_one hr0]
    exact hr2
  have h2 : chi (r * ξ) = 0 := by
    apply chi_eq_zero
    rw [abs_mul, abs_of_pos hr0]
    rw [div_le_iff₀ hξ0] at hr3
    exact hr3
  simp [psi, h1, h2]

lemma hasDerivAt_psi (r ξ : ℝ) :
    HasDerivAt (psi r) (deriv chi (ξ / r) / r - r * deriv chi (r * ξ)) ξ := by
  have h1 : HasDerivAt (fun x : ℝ => chi (x / r)) (deriv chi (ξ / r) * (1 / r)) ξ :=
    (chi_differentiable (ξ / r)).hasDerivAt.comp ξ ((hasDerivAt_id' ξ).div_const r)
  have h2 : HasDerivAt (fun x : ℝ => chi (r * x)) (deriv chi (r * ξ) * (r * 1)) ξ :=
    (chi_differentiable (r * ξ)).hasDerivAt.comp ξ ((hasDerivAt_id' ξ).const_mul r)
  show HasDerivAt (fun x : ℝ => chi (x / r) - chi (r * x)) _ ξ
  convert h1.sub h2 using 1
  ring

lemma integral_abs_deriv_psi_le {r : ℝ} (hr : 0 < r) :
    ∫ ξ, |deriv (psi r) ξ| ≤ 2 * ∫ x, |deriv chi x| := by
  have hA : Integrable (fun ξ : ℝ => |deriv chi (ξ / r)|) :=
    (integrable_deriv_chi.comp_div hr.ne').abs
  have hB : Integrable (fun ξ : ℝ => |deriv chi (r * ξ)|) :=
    (integrable_deriv_chi.comp_mul_left' hr.ne').abs
  have hpt : ∀ ξ, |deriv (psi r) ξ| ≤ |deriv chi (ξ / r)| / r + r * |deriv chi (r * ξ)| := by
    intro ξ
    rw [(hasDerivAt_psi r ξ).deriv]
    calc |deriv chi (ξ / r) / r - r * deriv chi (r * ξ)|
        ≤ |deriv chi (ξ / r) / r| + |r * deriv chi (r * ξ)| := abs_sub _ _
      _ = _ := by rw [abs_div, abs_mul, abs_of_pos hr]
  calc ∫ ξ, |deriv (psi r) ξ|
      ≤ ∫ ξ, (|deriv chi (ξ / r)| / r + r * |deriv chi (r * ξ)|) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          ((hA.div_const r).add (hB.const_mul r)) (Eventually.of_forall hpt)
    _ = (∫ ξ, |deriv chi (ξ / r)|) / r + r * ∫ ξ, |deriv chi (r * ξ)| := by
        rw [integral_add (hA.div_const r) (hB.const_mul r), integral_div, integral_const_mul]
    _ = 2 * ∫ x, |deriv chi x| := by
        rw [Measure.integral_comp_div (fun x => |deriv chi x|) r,
          Measure.integral_comp_mul_left (fun x => |deriv chi x|) r,
          abs_of_pos hr, abs_of_pos (inv_pos.mpr hr), smul_eq_mul, smul_eq_mul]
        field_simp
        ring

/-! ### Pointwise bounds for Fourier transforms of Schwartz functions. -/

lemma integrable_deriv_schwartz (H : 𝓢(ℝ, ℂ)) : Integrable (deriv (H : ℝ → ℂ)) := by
  have h := (SchwartzMap.derivCLM ℝ ℂ H).integrable (μ := volume)
  have heq : ((SchwartzMap.derivCLM ℝ ℂ H : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = deriv (H : ℝ → ℂ) := by
    funext x
    simp
  rwa [heq] at h

/-- `(1 + |u|) ‖𝓕 H u‖ ≤ ‖H‖₁ + (2π)⁻¹ ‖H'‖₁` for a Schwartz function `H` (Mathlib's normalization). -/
lemma one_add_abs_mul_norm_fourier_le (H : 𝓢(ℝ, ℂ)) (u : ℝ) :
    (1 + |u|) * ‖𝓕 (H : ℝ → ℂ) u‖ ≤ (∫ v, ‖H v‖) + (2 * π)⁻¹ * ∫ v, ‖deriv H v‖ := by
  have hcd : ContDiff ℝ (1 : ℕ) (H : ℝ → ℂ) := H.smooth 1
  have hint : ∀ k ≤ 1, Integrable (iteratedDeriv k (H : ℝ → ℂ)) := by
    intro k hk
    interval_cases k
    · simpa using H.integrable (μ := volume)
    · simpa [iteratedDeriv_one] using integrable_deriv_schwartz H
  have := Real.one_add_pow_mul_norm_fourier_le hcd hint u
  simpa [iteratedDeriv_one] using this

/-! ### The removed part `E_r Φ = Φ - ψ_r Φ = (1 - ψ_r) Φ`. -/

/-- The part of `Φ` removed by the band-pass multiplier: `Φ - ψ_r • Φ`. -/
noncomputable def remainder (r : ℝ) (Φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  Φ - SchwartzMap.smulLeftCLM ℂ (psi r) Φ

lemma remainder_apply {r : ℝ} (hr : 1 ≤ r) (Φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    remainder r Φ ξ = (1 - psi r ξ) • Φ ξ := by
  simp [remainder, SchwartzMap.smulLeftCLM_apply_apply (psi_hasTemperateGrowth hr), sub_smul]

lemma remainder_coe {r : ℝ} (hr : 1 ≤ r) (Φ : 𝓢(ℝ, ℂ)) :
    (remainder r Φ : ℝ → ℂ) = fun ξ => Φ ξ - psi r ξ • Φ ξ := by
  funext ξ
  rw [remainder_apply hr, sub_smul, one_smul]

lemma norm_remainder_le {r : ℝ} (hr : 1 ≤ r) (Φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    ‖remainder r Φ ξ‖ ≤ 2 * ‖Φ ξ‖ := by
  rw [remainder_apply hr, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_one_sub_psi_le_two r ξ) (norm_nonneg _)

lemma integral_norm_remainder_le {r : ℝ} (hr : 1 ≤ r) (Φ : 𝓢(ℝ, ℂ)) :
    ∫ ξ, ‖remainder r Φ ξ‖ ≤ 2 * ∫ ξ, ‖Φ ξ‖ := by
  rw [← integral_const_mul]
  exact integral_mono ((remainder r Φ).integrable (μ := volume)).norm
    (((Φ.integrable (μ := volume)).norm).const_mul 2) (norm_remainder_le hr Φ)

lemma deriv_remainder {r : ℝ} (hr : 1 ≤ r) (Φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    deriv (remainder r Φ : ℝ → ℂ) ξ =
      (1 - psi r ξ) • deriv Φ ξ - deriv (psi r) ξ • Φ ξ := by
  rw [remainder_coe hr]
  have hψ : HasDerivAt (psi r) (deriv (psi r) ξ) ξ :=
    ((psi_contDiff r).differentiable (by simp) ξ).hasDerivAt
  have h : HasDerivAt (fun x => Φ x - psi r x • Φ x)
      (deriv Φ ξ - (psi r ξ • deriv Φ ξ + deriv (psi r) ξ • Φ ξ)) ξ :=
    (Φ.hasDerivAt ξ).sub (hψ.smul (Φ.hasDerivAt ξ))
  rw [h.deriv, sub_smul, one_smul]
  abel

lemma integrable_deriv_psi {r : ℝ} (hr : 1 ≤ r) : Integrable (deriv (psi r)) :=
  ((psi_contDiff r).continuous_deriv (by simp)).integrable_of_hasCompactSupport
    (psi_hasCompactSupport hr).deriv

lemma integral_norm_deriv_remainder_le {r : ℝ} (hr : 1 ≤ r) (Φ : 𝓢(ℝ, ℂ)) :
    ∫ ξ, ‖deriv (remainder r Φ : ℝ → ℂ) ξ‖ ≤
      2 * (∫ ξ, ‖deriv Φ ξ‖) + SchwartzMap.seminorm ℝ 0 0 Φ * (2 * ∫ x, |deriv chi x|) := by
  set M := SchwartzMap.seminorm ℝ 0 0 Φ
  have hM : ∀ ξ, ‖Φ ξ‖ ≤ M := fun ξ => SchwartzMap.norm_le_seminorm ℝ Φ ξ
  have hpt : ∀ ξ, ‖deriv (remainder r Φ : ℝ → ℂ) ξ‖ ≤
      2 * ‖deriv Φ ξ‖ + M * |deriv (psi r) ξ| := by
    intro ξ
    rw [deriv_remainder hr]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_one_sub_psi_le_two r ξ) (norm_nonneg _)
    · rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM ξ) (abs_nonneg _)
  have hI1 : Integrable (fun ξ => 2 * ‖deriv (Φ : ℝ → ℂ) ξ‖) :=
    (integrable_deriv_schwartz Φ).norm.const_mul 2
  have hI2 : Integrable (fun ξ => M * |deriv (psi r) ξ|) :=
    (integrable_deriv_psi hr).abs.const_mul M
  have hr0 : 0 < r := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  calc ∫ ξ, ‖deriv (remainder r Φ : ℝ → ℂ) ξ‖
      ≤ ∫ ξ, (2 * ‖deriv (Φ : ℝ → ℂ) ξ‖ + M * |deriv (psi r) ξ|) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hI1.add hI2)
          (Eventually.of_forall hpt)
    _ = 2 * (∫ ξ, ‖deriv Φ ξ‖) + M * ∫ ξ, |deriv (psi r) ξ| := by
        rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul]
    _ ≤ 2 * (∫ ξ, ‖deriv Φ ξ‖) + M * (2 * ∫ x, |deriv chi x|) := by
        gcongr
        exact integral_abs_deriv_psi_le hr0

lemma tendsto_integral_norm_remainder (Φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun n : ℕ => ∫ ξ, ‖remainder ((n : ℝ) + 1) Φ ξ‖) atTop (𝓝 0) := by
  have hseq : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hr : ∀ n : ℕ, 1 ≤ (n : ℝ) + 1 := fun n => by
    have := n.cast_nonneg (α := ℝ)
    linarith
  have key := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) (ξ : ℝ) => ‖remainder ((n : ℝ) + 1) Φ ξ‖) (f := fun _ => (0 : ℝ))
    (fun ξ => 2 * ‖Φ ξ‖)
    (fun n => (remainder ((n : ℝ) + 1) Φ).continuous.norm.aestronglyMeasurable)
    (((Φ.integrable (μ := volume)).norm).const_mul 2)
    (fun n => Eventually.of_forall fun ξ => by
      rw [norm_norm]
      exact norm_remainder_le (hr n) Φ ξ)
    (by
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with ξ hξ
      apply tendsto_const_nhds.congr'
      filter_upwards [hseq.eventually (eventually_one_sub_psi_eq_zero hξ)] with n hn
      rw [remainder_apply (hr n), hn, zero_smul, norm_zero])
  simpa using key

/-! ### An `L^p` dominated-convergence criterion on `ℝ`, `1 < p < ∞`. -/

/-- If `‖F n x‖ ≤ a n → 0` uniformly and `(1 + |x|) ‖F n x‖ ≤ K`, then `‖F n‖_p → 0` for
`1 < p < ∞` (dominated convergence with the `L^p` majorant `K / (1 + |x|)`). -/
lemma tendsto_eLpNorm_of_uniform_of_decay {p : ENNReal} (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (F : ℕ → ℝ → ℂ) (hF : ∀ n, Continuous (F n)) (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (K : ℝ) (h1 : ∀ n x, ‖F n x‖ ≤ a n) (h2 : ∀ n x, (1 + |x|) * ‖F n x‖ ≤ K) :
    Tendsto (fun n => eLpNorm (F n) p volume) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hq1 : 1 < p.toReal := by
    simpa using ENNReal.toReal_strict_mono hptop hp1
  have hq0 : 0 < p.toReal := zero_lt_one.trans hq1
  have hK : 0 ≤ K := le_trans (by positivity) (h2 0 0)
  have bound_pt : ∀ n x, ‖F n x‖ₑ ^ p.toReal ≤
      ENNReal.ofReal (K ^ p.toReal * (1 + ‖x‖) ^ (-p.toReal)) := by
    intro n x
    have hx : 0 < 1 + |x| := by positivity
    have hb : ‖F n x‖ ≤ K / (1 + |x|) := by
      rw [le_div_iff₀ hx, mul_comm]
      exact h2 n x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le]
    apply ENNReal.ofReal_le_ofReal
    calc ‖F n x‖ ^ p.toReal ≤ (K / (1 + |x|)) ^ p.toReal :=
          Real.rpow_le_rpow (norm_nonneg _) hb hq0.le
      _ = K ^ p.toReal * (1 + ‖x‖) ^ (-p.toReal) := by
          rw [Real.norm_eq_abs, Real.div_rpow hK hx.le, Real.rpow_neg hx.le, div_eq_mul_inv]
  have lim_pt : ∀ x, Tendsto (fun n => ‖F n x‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    intro x
    have hn : Tendsto (fun n => ‖F n x‖) atTop (𝓝 0) :=
      squeeze_zero (fun n => norm_nonneg _) (fun n => h1 n x) ha
    have he : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
      simpa [ofReal_norm] using ENNReal.tendsto_ofReal hn
    have := ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0).comp he
    rw [ENNReal.zero_rpow_of_pos hq0] at this
    exact this
  have hfin : ∫⁻ x, ENNReal.ofReal (K ^ p.toReal * (1 + ‖x‖) ^ (-p.toReal)) ≠ ⊤ :=
    (((integrable_one_add_norm (E := ℝ) (μ := volume) (r := p.toReal)
      (by simpa using hq1)).const_mul (K ^ p.toReal)).lintegral_lt_top).ne
  have hlin : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    have key := tendsto_lintegral_of_dominated_convergence (μ := volume)
      (F := fun n x => ‖F n x‖ₑ ^ p.toReal) (f := fun _ => 0)
      (fun x => ENNReal.ofReal (K ^ p.toReal * (1 + ‖x‖) ^ (-p.toReal)))
      (fun n => (hF n).measurable.enorm.pow_const p.toReal)
      (fun n => Eventually.of_forall fun x => bound_pt n x) hfin
      (Eventually.of_forall lim_pt)
    simpa using key
  have hroot := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp hlin
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at hroot
  refine hroot.congr fun n => ?_
  simp only [Function.comp]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (hF n).aestronglyMeasurable]

/-! ### The band-pass approximant `g_r = 𝓕⁻(ψ_r · 𝓕 φ)`. -/

/-- The band-pass approximant `g_r = 𝓕⁻(ψ_r · 𝓕 φ)` of a Schwartz function `φ`. -/
noncomputable def bandpass (r : ℝ) (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (psi r) (𝓕 φ))

lemma fourier_bandpass_apply {r : ℝ} (hr : 1 ≤ r) (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (bandpass r φ : ℝ → ℂ) ξ = psi r ξ • 𝓕 (φ : ℝ → ℂ) ξ := by
  rw [← SchwartzMap.fourier_coe, bandpass, fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (psi_hasTemperateGrowth hr), SchwartzMap.fourier_coe]

lemma sub_bandpass_apply (r : ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (φ - bandpass r φ) x = 𝓕 (remainder r (𝓕 φ) : ℝ → ℂ) (-x) := by
  have h1 : φ - bandpass r φ = 𝓕⁻ (remainder r (𝓕 φ)) := by
    calc φ - bandpass r φ = 𝓕⁻ (𝓕 φ) - bandpass r φ := by rw [fourierInv_fourier_eq]
      _ = 𝓕⁻ (remainder r (𝓕 φ)) := by
        rw [bandpass, remainder, sub_eq_add_neg, sub_eq_add_neg, fourierInv_add, fourierInv_neg]
  rw [h1, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]

/-- **Low/high-frequency removal is small in `L^p`.** For a Schwartz `φ` and `1 < p < ∞`, some
band-pass approximant `g_r` is `ε`-close to `φ` in `L^p`. -/
theorem exists_bandpass_close (φ : 𝓢(ℝ, ℂ)) {p : ENNReal} [Fact (1 ≤ p)] (hp1 : 1 < p)
    (hptop : p ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 1 ≤ r ∧ ‖(bandpass r φ).toLp p volume - φ.toLp p volume‖ < ε := by
  have hr : ∀ n : ℕ, 1 ≤ (n : ℝ) + 1 := fun n => by
    have := n.cast_nonneg (α := ℝ)
    linarith
  set Φ : 𝓢(ℝ, ℂ) := 𝓕 φ with hΦ
  set K : ℝ := 2 * (∫ ξ, ‖Φ ξ‖) + (2 * π)⁻¹ * (2 * (∫ ξ, ‖deriv Φ ξ‖) +
    SchwartzMap.seminorm ℝ 0 0 Φ * (2 * ∫ x, |deriv chi x|)) with hK
  have hconv := tendsto_eLpNorm_of_uniform_of_decay hp1 hptop
    (fun n x => (φ - bandpass ((n : ℝ) + 1) φ) x)
    (fun n => (φ - bandpass ((n : ℝ) + 1) φ).continuous)
    (fun n => ∫ ξ, ‖remainder ((n : ℝ) + 1) Φ ξ‖) (tendsto_integral_norm_remainder Φ) K
    (fun n x => by
      rw [sub_bandpass_apply]
      exact Real.norm_fourier_le_integral_norm _ _)
    (fun n x => by
      rw [sub_bandpass_apply]
      have h := one_add_abs_mul_norm_fourier_le (remainder ((n : ℝ) + 1) Φ) (-x)
      rw [abs_neg] at h
      refine h.trans (add_le_add (integral_norm_remainder_le (hr n) Φ) ?_)
      exact mul_le_mul_of_nonneg_left (integral_norm_deriv_remainder_le (hr n) Φ)
        (by positivity))
  have hεe : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds hεe)).exists
  refine ⟨(n : ℝ) + 1, hr n, ?_⟩
  have hsub : (bandpass ((n : ℝ) + 1) φ).toLp p volume - φ.toLp p volume =
      (bandpass ((n : ℝ) + 1) φ - φ).toLp p volume :=
    (map_sub (SchwartzMap.toLpCLM ℝ ℂ p volume) (bandpass ((n : ℝ) + 1) φ) φ).symm
  rw [hsub, SchwartzMap.norm_toLp]
  apply ENNReal.toReal_lt_of_lt_ofReal
  have hcoe : ((bandpass ((n : ℝ) + 1) φ - φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) =
      (bandpass ((n : ℝ) + 1) φ : ℝ → ℂ) - (φ : ℝ → ℂ) := by
    funext x
    simp
  have hcoe' : ((φ - bandpass ((n : ℝ) + 1) φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) =
      (φ : ℝ → ℂ) - (bandpass ((n : ℝ) + 1) φ : ℝ → ℂ) := by
    funext x
    simp
  rw [hcoe, eLpNorm_sub_comm, ← hcoe']
  exact hn

/-! ### The paper's Fourier transform and the main theorem. -/

/-- The paper's Fourier transform `∫ g(x) e^{-i x ξ} dx` is Mathlib's `𝓕 g` at `ξ / (2π)`. -/
lemma paperFourier_eq (g : ℝ → ℂ) (ξ : ℝ) :
    (∫ x : ℝ, g x * Complex.exp (-Complex.I * (x : ℂ) * (ξ : ℂ))) = 𝓕 g (ξ / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have h : ((-2 * π * x * (ξ / (2 * π)) : ℝ) : ℂ) * Complex.I =
      -Complex.I * (x : ℂ) * (ξ : ℂ) := by
    rw [show -2 * π * x * (ξ / (2 * π)) = -(x * ξ) * (2 * π / (2 * π)) by ring,
      div_self (by positivity), mul_one]
    push_cast
    ring
  simp only [smul_eq_mul]
  rw [h, mul_comm]

lemma paperFourier_bandpass {r : ℝ} (hr : 1 ≤ r) (φ : 𝓢(ℝ, ℂ)) :
    (fun ξ : ℝ => ∫ x : ℝ, bandpass r φ x * Complex.exp (-Complex.I * (x : ℂ) * (ξ : ℂ))) =
      fun ξ => psi r (ξ / (2 * π)) • 𝓕 (φ : ℝ → ℂ) (ξ / (2 * π)) := by
  funext ξ
  rw [paperFourier_eq, fourier_bandpass_apply hr]

lemma hasCompactSupport_scaled_bandpass {r : ℝ} (hr : 1 ≤ r) (G : ℝ → ℂ) :
    HasCompactSupport (fun ξ : ℝ => psi r (ξ / (2 * π)) • G (ξ / (2 * π))) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * π * (2 * r))) fun ξ hξ => ?_
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hξ
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hlarge : 2 * r ≤ |ξ / (2 * π)| := by
    rw [abs_div, abs_of_pos h2π, le_div_iff₀ h2π]
    linarith
  simp [psi_eq_zero_of_large hr hlarge]

lemma zero_notMem_tsupport_scaled_bandpass {r : ℝ} (hr : 1 ≤ r) (G : ℝ → ℂ) :
    0 ∉ tsupport (fun ξ : ℝ => psi r (ξ / (2 * π)) • G (ξ / (2 * π))) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  have hr0 : 0 < r := by linarith
  have h2π : (0 : ℝ) < 2 * π := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (div_pos h2π hr0)] with ξ hξ
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hξ
  have hsmall : |ξ / (2 * π)| ≤ 1 / r := by
    rw [abs_div, abs_of_pos h2π, div_le_div_iff₀ h2π hr0]
    rw [lt_div_iff₀ hr0] at hξ
    linarith
  simp [psi_eq_zero_of_small hr hsmall]

/-- **Separated compact-frequency Schwartz tests are dense in `L^p(ℝ)`, `1 < p < ∞`.**
Here the Fourier transform is the paper's `ĝ(ξ) = ∫ g(x) e^{-i x ξ} dx`. -/
theorem slice_N10_proved {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : SchwartzMap ℝ ℂ, ‖g.toLp (ENNReal.ofReal p) volume - f‖ < ε ∧
      HasCompactSupport (fun ξ : ℝ => ∫ x : ℝ, g x * Complex.exp (-Complex.I * (x : ℂ) * (ξ : ℂ))) ∧
      0 ∉ tsupport (fun ξ : ℝ => ∫ x : ℝ, g x * Complex.exp (-Complex.I * (x : ℂ) * (ξ : ℂ))) := by
  have hp1 : 1 < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨φ, hφ⟩ := (SchwartzMap.denseRange_toLpCLM (F := ℂ) (μ := volume) hptop).exists_dist_lt
    f (half_pos hε)
  obtain ⟨r, hr, hg⟩ := exists_bandpass_close φ hp1 hptop (half_pos hε)
  refine ⟨bandpass r φ, ?_, ?_, ?_⟩
  · rw [SchwartzMap.toLpCLM_apply, dist_comm, dist_eq_norm] at hφ
    calc ‖(bandpass r φ).toLp (ENNReal.ofReal p) volume - f‖
        ≤ ‖(bandpass r φ).toLp (ENNReal.ofReal p) volume - φ.toLp (ENNReal.ofReal p) volume‖ +
          ‖φ.toLp (ENNReal.ofReal p) volume - f‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hg hφ
      _ = ε := add_halves ε
  · rw [paperFourier_bandpass hr]
    exact hasCompactSupport_scaled_bandpass hr _
  · rw [paperFourier_bandpass hr]
    exact zero_notMem_tsupport_scaled_bandpass hr _

end GKSharp.Proofs.N10Density

#print axioms GKSharp.Proofs.N10Density.slice_N10_proved
