/- generic Fourier/density foundations, ported from018 DensityLpA.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Pencil

open Real MeasureTheory Filter Topology Set AddCircle
open scoped ENNReal NNReal

namespace GKSharp

namespace DensityLp

/-! ## Measures on `T` -/

theorem two_pi_ofReal_ne_zero : ENNReal.ofReal (2 * π) ≠ 0 := (ENNReal.ofReal_pos.mpr two_pi_pos).ne'

theorem ae_haar_iff {P : Circ → Prop} :
    (∀ᵐ x ∂(volume : Measure Circ), P x) ↔ ∀ᵐ x ∂(haarAddCircle : Measure Circ), P x := by
  rw [volume_eq_smul_haarAddCircle]
  exact Measure.ae_ennreal_smul_measure_iff two_pi_ofReal_ne_zero

theorem haar_le_volume : (haarAddCircle : Measure Circ) ≤ volume := by
  rw [volume_eq_smul_haarAddCircle, Measure.le_iff']
  intro s
  rw [Measure.smul_apply, smul_eq_mul]
  refine le_mul_of_one_le_left zero_le ?_
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith [pi_gt_three])

theorem integrable_haar_of_lp {p : ℝ} [hp : Fact (1 ≤ ENNReal.ofReal p)] (f : LpT p) :
    Integrable (⇑f) (haarAddCircle : Measure Circ) :=
  (memLp_haarAddCircle_iff.mpr (Lp.memLp f)).integrable hp.out

theorem continuous_integrable {μ : Measure Circ} [IsFiniteMeasure μ] (φ : C(Circ, ℂ)) : Integrable (⇑φ) μ :=
  (map_continuous φ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ## Trigonometric polynomials on `T` -/

/-- `Σ_n c_n e^{inθ}` as a continuous function on `T`. -/
noncomputable def tC (c : ℤ →₀ ℂ) : C(Circ, ℂ) := Finsupp.linearCombination ℂ (fun n : ℤ => (fourier n : C(Circ, ℂ))) c

/-- `P₊`: the terms with `n ≥ 0`. -/
noncomputable def pC (c : ℤ →₀ ℂ) : C(Circ, ℂ) := tC (c.filter fun n => 0 ≤ n)

/-- `P₋`: the terms with `n < 0`. -/
noncomputable def mC (c : ℤ →₀ ℂ) : C(Circ, ℂ) := tC (c.filter fun n => n < 0)

theorem tC_sub (c d : ℤ →₀ ℂ) : tC (c - d) = tC c - tC d := map_sub _ c d

theorem pC_sub (c d : ℤ →₀ ℂ) : pC (c - d) = pC c - pC d := by
  unfold pC; rw [Finsupp.filter_sub, tC_sub]

theorem mC_sub (c d : ℤ →₀ ℂ) : mC (c - d) = mC c - mC d := by
  unfold mC; rw [Finsupp.filter_sub, tC_sub]

theorem fourier_coe_two_pi (n : ℤ) (θ : ℝ) :
    fourier n (θ : Circ) = Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  push_cast
  field_simp

theorem tC_coe (c : ℤ →₀ ℂ) (θ : ℝ) : tC c (θ : Circ) = trig c θ := by
  unfold tC trig mode
  rw [Finsupp.linearCombination_apply, Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, fourier_coe_two_pi]

theorem trig_filter (c : ℤ →₀ ℂ) (P : ℤ → Prop) [DecidablePred P] (θ : ℝ) :
    trig (c.filter P) θ = c.sum fun n a => if P n then mode n a θ else 0 := by
  unfold trig Finsupp.sum
  rw [Finsupp.support_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : P n <;> simp [h, Finsupp.filter_apply]

theorem pC_coe (c : ℤ →₀ ℂ) (θ : ℝ) : pC c (θ : Circ) = Pplus c θ := by
  unfold pC Pplus; rw [tC_coe, trig_filter]

theorem mC_coe (c : ℤ →₀ ℂ) (θ : ℝ) : mC c (θ : Circ) = Pminus c θ := by
  unfold mC Pminus Pplus
  rw [tC_coe, trig_filter]
  unfold trig Finsupp.sum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : n < 0
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

theorem coeff_tC (c : ℤ →₀ ℂ) (m : ℤ) : fourierCoeff (⇑(tC c)) m = c m := by
  unfold tC
  rw [Finsupp.linearCombination_apply, Finsupp.sum, ContinuousMap.coe_sum,
    fourierCoeff.sum _ _ (fun n _ => continuous_integrable _), Finset.sum_apply]
  simp_rw [ContinuousMap.coe_smul, fourierCoeff.const_smul, fourierCoeff_fourier]
  rw [Finset.sum_eq_single m]
  · simp
  · intro n _ hnm; simp [Pi.single_apply, Ne.symm hnm]
  · intro hm; simp [Finsupp.notMem_support_iff.mp hm]

theorem coeff_pC (c : ℤ →₀ ℂ) (m : ℤ) : fourierCoeff (⇑(pC c)) m = if 0 ≤ m then c m else 0 := by
  unfold pC; rw [coeff_tC, Finsupp.filter_apply]

theorem coeff_mC (c : ℤ →₀ ℂ) (m : ℤ) : fourierCoeff (⇑(mC c)) m = if m < 0 then c m else 0 := by
  unfold mC; rw [coeff_tC, Finsupp.filter_apply]

/-- `toLp` of a continuous function, in `L^p(T)`. -/
noncomputable abbrev toLpT (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (φ : C(Circ, ℂ)) : LpT p :=
  ContinuousMap.toLp (E := ℂ) (ENNReal.ofReal p) (volume : Measure Circ) ℂ φ

theorem coeFn_toLpT {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (φ : C(Circ, ℂ)) : ⇑(toLpT p φ) =ᵐ[volume] ⇑φ :=
  ContinuousMap.coeFn_toLp (E := ℂ) (volume : Measure Circ) φ

theorem coeff_toLpT {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (φ : C(Circ, ℂ)) :
    fourierCoeff (⇑(toLpT p φ)) = fourierCoeff (⇑φ) :=
  fourierCoeff_congr_ae (ae_haar_iff.mp (coeFn_toLpT φ))

/-! ## D1: a function in `L^p(T)` is fixed by its Fourier coefficients -/

theorem integral_mul_eq_zero {w : Circ → ℂ} (hw : Integrable w haarAddCircle) (h0 : ∀ n, fourierCoeff w n = 0)
    (φ : C(Circ, ℂ)) : ∫ x, φ x * w x ∂haarAddCircle = 0 := by
  have hint : ∀ ψ : C(Circ, ℂ), Integrable (fun x => ψ x * w x) haarAddCircle := fun ψ =>
    hw.bdd_mul (map_continuous ψ).aestronglyMeasurable (ae_of_all _ fun x => ψ.norm_coe_le_norm x)
  let L : C(Circ, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => ∫ x, ψ x * w x ∂haarAddCircle
      map_add' := fun ψ χ => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint ψ) (hint χ)
      map_smul' := fun a ψ => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul a _ }
  have hL : Continuous L := by
    refine AddMonoidHomClass.continuous_of_bound L (∫ x, ‖w x‖ ∂haarAddCircle) fun ψ => ?_
    show ‖∫ x, ψ x * w x ∂haarAddCircle‖ ≤ _
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [mul_comm (∫ x, ‖w x‖ ∂haarAddCircle) ‖ψ‖, ← integral_const_mul]
    refine integral_mono (hint ψ).norm (hw.norm.const_mul _) fun x => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (ψ.norm_coe_le_norm x) (norm_nonneg _)
  have hfour : ∀ n : ℤ, L (fourier n) = 0 := fun n => by
    show ∫ x, fourier n x * w x ∂haarAddCircle = 0
    have h := h0 (-n)
    unfold fourierCoeff at h
    simpa only [neg_neg, smul_eq_mul] using h
  have hker : Submodule.span ℂ (range fun n : ℤ => (fourier n : C(Circ, ℂ))) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    exact hfour n
  have hclosed : IsClosed ((LinearMap.ker L : Submodule ℂ C(Circ, ℂ)) : Set C(Circ, ℂ)) :=
    isClosed_singleton.preimage hL
  have htop := Submodule.topologicalClosure_minimal _ hker hclosed
  rw [span_fourier_closure_eq_top] at htop
  exact htop Submodule.mem_top

theorem setIntegral_closed_eq_zero {w : Circ → ℂ} (hw : Integrable w haarAddCircle) (h0 : ∀ n, fourierCoeff w n = 0)
    (F : Set Circ) (hF : IsClosed F) : ∫ x in F, w x ∂haarAddCircle = 0 := by
  have hδ : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have htend := thickenedIndicator_tendsto_indicator_closure hδ tendsto_one_div_add_atTop_nhds_zero_nat F
  rw [hF.closure_eq] at htend
  let φ : ℕ → C(Circ, ℂ) := fun k =>
    ⟨fun x => (((thickenedIndicator (hδ k) F x : ℝ≥0) : ℝ) : ℂ),
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (thickenedIndicator (hδ k) F).continuous)⟩
  have hzero : ∀ k, ∫ x, φ k x * w x ∂haarAddCircle = 0 := fun k => integral_mul_eq_zero hw h0 (φ k)
  have hlim : Tendsto (fun k => ∫ x, φ k x * w x ∂haarAddCircle) atTop (𝓝 (∫ x, F.indicator w x ∂haarAddCircle)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖w x‖)
      (fun k => ((map_continuous (φ k)).aestronglyMeasurable.mul hw.aestronglyMeasurable)) hw.norm
      (fun k => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · show ‖(((thickenedIndicator (hδ k) F x : ℝ≥0) : ℝ) : ℂ) * w x‖ ≤ ‖w x‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (by exact_mod_cast thickenedIndicator_le_one (hδ k) F x)
    · have hx := tendsto_pi_nhds.mp htend x
      have hx' : Tendsto (fun k => (((thickenedIndicator (hδ k) F x : ℝ≥0) : ℝ) : ℂ) * w x) atTop
          (𝓝 ((((F.indicator (fun _ => (1 : ℝ≥0)) x : ℝ≥0) : ℝ) : ℂ) * w x)) :=
        ((Complex.continuous_ofReal.comp NNReal.continuous_coe).continuousAt.tendsto.comp hx).mul_const _
      have hval : (((F.indicator (fun _ => (1 : ℝ≥0)) x : ℝ≥0) : ℝ) : ℂ) * w x = F.indicator w x := by
        by_cases hxF : x ∈ F <;> simp [hxF]
      rw [← hval]
      exact hx'
  rw [integral_indicator hF.measurableSet] at hlim
  exact tendsto_nhds_unique hlim (by simp only [hzero]; exact tendsto_const_nhds)

/-- **D1.** A function in `L^p(T)`, `p ≥ 1`, is determined by its Fourier coefficients. -/
theorem fourier_ext {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (u v : LpT p)
    (h : ∀ n : ℤ, fourierCoeff (⇑u) n = fourierCoeff (⇑v) n) : u = v := by
  have hu := integrable_haar_of_lp u
  have hv := integrable_haar_of_lp v
  have hw : Integrable (fun x => u x - v x) haarAddCircle := hu.sub hv
  have h0 : ∀ n, fourierCoeff (fun x => u x - v x) n = 0 := fun n => by
    have e : fourierCoeff (fun x => u x - v x) n = fourierCoeff (⇑u) n - fourierCoeff (⇑v) n := by
      unfold fourierCoeff
      simp_rw [smul_sub]
      exact integral_sub (hu.fourier_smul _) (hv.fourier_smul _)
    rw [e, h n, sub_self]
  have hae := ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hw (setIntegral_closed_eq_zero hw h0)
  refine Lp.ext (ae_haar_iff.mpr ?_)
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp hx

/-! ## Fourier coefficients are continuous on `L^p(T)` -/

theorem norm_coeff_sub_le {p : ℝ} [hp : Fact (1 ≤ ENNReal.ofReal p)] (u v : LpT p) (n : ℤ) :
    ‖fourierCoeff (⇑u) n - fourierCoeff (⇑v) n‖ ≤ ‖u - v‖ := by
  have hu := integrable_haar_of_lp u
  have hv := integrable_haar_of_lp v
  have e : fourierCoeff (⇑u) n - fourierCoeff (⇑v) n =
      ∫ t, fourier (-n) t • (u t - v t) ∂haarAddCircle := by
    unfold fourierCoeff
    simp_rw [smul_sub]
    exact (integral_sub (hu.fourier_smul _) (hv.fourier_smul _)).symm
  rw [e]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hn : ∀ t : Circ, ‖fourier (-n) t • (u t - v t)‖ = ‖u t - v t‖ := fun t => by
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
  simp_rw [hn]
  have hsm : AEStronglyMeasurable (fun t => u t - v t) (haarAddCircle : Measure Circ) := hu.1.sub hv.1
  rw [integral_norm_eq_lintegral_enorm hsm, ← eLpNorm_one_eq_lintegral_enorm hsm, Lp.norm_def]
  have hcongr : eLpNorm (fun t => u t - v t) (ENNReal.ofReal p) volume = eLpNorm (⇑(u - v)) (ENNReal.ofReal p) volume :=
    eLpNorm_congr_ae (Lp.coeFn_sub u v).symm
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top (u - v)) ?_
  rw [← hcongr]
  exact (eLpNorm_le_eLpNorm_of_exponent_le hp.out).trans (eLpNorm_mono_measure _ haar_le_volume)

theorem tendsto_coeff {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {u : ℕ → LpT p} {v : LpT p}
    (hu : Tendsto u atTop (𝓝 v)) (n : ℤ) :
    Tendsto (fun k => fourierCoeff (⇑(u k)) n) atTop (𝓝 (fourierCoeff (⇑v) n)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hu ⊢
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => norm_coeff_sub_le (u k) v n) hu

/-! ## Density of trigonometric polynomials in `L^p(T)` -/

theorem exists_trig_tendsto {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (f : LpT p) :
    ∃ c : ℕ → (ℤ →₀ ℂ), Tendsto (fun k => toLpT p (tC (c k))) atTop (𝓝 f) := by
  have hcl := (ContinuousMap.toLp_denseRange ℂ (volume : Measure Circ) ℂ
    (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top).topologicalClosure_map_submodule
    (span_fourier_closure_eq_top (T := 2 * π))
  set S : Submodule ℂ (LpT p) := Submodule.map
    ((ContinuousMap.toLp (E := ℂ) (ENNReal.ofReal p) (volume : Measure Circ) ℂ : C(Circ, ℂ) →L[ℂ] LpT p) :
      C(Circ, ℂ) →ₗ[ℂ] LpT p)
    (Submodule.span ℂ (range fun n : ℤ => (fourier n : C(Circ, ℂ)))) with hSdef
  have hS : S.topologicalClosure = ⊤ := hcl
  have hf : f ∈ closure (S : Set (LpT p)) := by
    rw [← Submodule.topologicalClosure_coe, hS]
    exact Submodule.mem_top
  obtain ⟨x, hxS, hxf⟩ := mem_closure_iff_seq_limit.mp hf
  have hc : ∀ k, ∃ c : ℤ →₀ ℂ, toLpT p (tC c) = x k := fun k => by
    obtain ⟨φ, hφ, hφx⟩ := Submodule.mem_map.mp (hxS k)
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hφ
    refine ⟨c, ?_⟩
    rw [← hφx, ← hc]
    unfold tC
    rw [Finsupp.linearCombination_apply]
    rfl
  choose c hc using hc
  exact ⟨c, by simp only [hc]; exact hxf⟩

/-! ## `L^p` norms of continuous functions as interval integrals -/

theorem eLpNorm_circ {E : Type*} [NormedAddCommGroup E] {p : ℝ} (hp : 0 < p) {F : Circ → E} (hF : Continuous F) :
    eLpNorm F (ENNReal.ofReal p) volume = ENNReal.ofReal ((∫ θ in (0 : ℝ)..(2 * π), ‖F θ‖ ^ p) ^ (1 / p)) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hF.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le]
  have hc : Continuous fun θ : ℝ => ‖F θ‖ ^ p :=
    (hF.comp (AddCircle.continuous_mk' (2 * π))).norm.rpow_const fun _ => Or.inr hp.le
  have hI : ∫⁻ x : Circ, ‖F x‖ₑ ^ p = ENNReal.ofReal (∫ θ in (0 : ℝ)..(2 * π), ‖F θ‖ ^ p) := by
    rw [← AddCircle.lintegral_preimage (2 * π) 0 (fun x => ‖F x‖ₑ ^ p), zero_add,
      intervalIntegral.integral_of_le two_pi_pos.le,
      ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Ioc (ae_of_all _ fun θ => rpow_nonneg (norm_nonneg _) _)]
    refine lintegral_congr fun θ => ?_
    show ‖F θ‖ₑ ^ p = ENNReal.ofReal (‖F θ‖ ^ p)
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  rw [hI, ENNReal.ofReal_rpow_of_nonneg
    (intervalIntegral.integral_nonneg two_pi_pos.le fun θ _ => rpow_nonneg (norm_nonneg _) _) (by positivity)]

/-- `A ≤ K^p B` ⇔ `A^{1/p} ≤ K B^{1/p}` (as `ENNReal.ofReal`), for `A, B, K ≥ 0`, `p > 0`. -/
theorem rpow_ineq_iff {p A B K : ℝ} (hp : 0 < p) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    A ≤ K ^ p * B ↔ ENNReal.ofReal (A ^ (1 / p)) ≤ ENNReal.ofReal K * ENNReal.ofReal (B ^ (1 / p)) := by
  rw [← ENNReal.ofReal_mul hK, ENNReal.ofReal_le_ofReal_iff (by positivity)]
  have e : K * B ^ (1 / p) = (K ^ p * B) ^ (1 / p) := by
    rw [mul_rpow (by positivity) hB, ← rpow_mul hK, mul_one_div_cancel hp.ne', rpow_one]
  rw [e]
  constructor
  · intro h; exact rpow_le_rpow hA h (by positivity)
  · intro h
    have h' := rpow_le_rpow (by positivity) h hp.le
    rwa [← rpow_mul hA, ← rpow_mul (by positivity), one_div_mul_cancel hp.ne', rpow_one, rpow_one] at h'


end DensityLp
end GKSharp

