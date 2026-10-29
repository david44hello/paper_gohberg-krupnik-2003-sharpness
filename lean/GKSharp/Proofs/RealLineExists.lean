/- RealLineExists.lean - project 019, N family: for 1 < p and all α, β a RealLinePencil exists (N01_nonvacuity).
   P₊ = 𝓕⁻(χ_{(0,∞)} 𝓕 ·) on Schwartz inputs (cited bound HV2000 Theorem 3.1), extended to L^p by density;
   the map is α P₊ + β (1 − P₊); both weak half-line tests are proved.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Cited.HV2000RealLine
import GKSharp.Proofs.RealLineUnique

open MeasureTheory Real Filter Topology
open scoped FourierTransform ENNReal

namespace GKSharp.Proofs.RealLineExists

open GKSharp.Proofs.RealLineUnique (integral_toLp_mul)

/-- χ_{(0,∞)} 𝓕f for a Schwartz input f. -/
noncomputable def halfMask (f : SchwartzMap ℝ ℂ) : ℝ → ℂ := Set.indicator (Set.Ioi (0 : ℝ)) (𝓕 (f : ℝ → ℂ))

/-- P₊f = 𝓕⁻(χ_{(0,∞)} 𝓕f) pointwise, HV2000 (1.2), for a Schwartz input f. -/
noncomputable def plusFun (f : SchwartzMap ℝ ℂ) : ℝ → ℂ := 𝓕⁻ (halfMask f)

theorem integrable_halfMask (f : SchwartzMap ℝ ℂ) : Integrable (halfMask f) :=
  (𝓕 f).integrable.indicator measurableSet_Ioi

theorem halfMask_add (f g : SchwartzMap ℝ ℂ) : halfMask (f + g) = halfMask f + halfMask g := by
  unfold halfMask
  rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe,
    FourierTransform.fourier_add]
  exact Set.indicator_add _ _ _

theorem halfMask_smul (c : ℂ) (f : SchwartzMap ℝ ℂ) : halfMask (c • f) = c • halfMask f := by
  unfold halfMask
  rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe, FourierTransform.fourier_smul]
  exact Set.indicator_const_smul _ c _

theorem continuous_neg_inner : Continuous fun q : ℝ × ℝ => (-innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) q.1 q.2 := by
  simp only [LinearMap.neg_apply, innerₗ_apply_apply]
  exact continuous_inner.neg

theorem plusFun_add (f g : SchwartzMap ℝ ℂ) : plusFun (f + g) = plusFun f + plusFun g := by
  unfold plusFun
  rw [halfMask_add]
  exact VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_neg_inner
    (integrable_halfMask f) (integrable_halfMask g)

theorem plusFun_smul (c : ℂ) (f : SchwartzMap ℝ ℂ) : plusFun (c • f) = c • plusFun f := by
  unfold plusFun
  rw [halfMask_smul]
  exact VectorFourier.fourierIntegral_const_smul _ _ _ _ c

variable {p : ℝ}

theorem memLp_plusFun (hp : 1 < p) (f : SchwartzMap ℝ ℂ) : MemLp (plusFun f) (ENNReal.ofReal p) volume :=
  (GKSharp.Cited.hv2000_thm31_schwartz p hp f).1

/-- P₊ on Schwartz inputs, with values in L^p (HV2000 Theorem 3.1). -/
noncomputable def plusLM (hp : 1 < p) : SchwartzMap ℝ ℂ →ₗ[ℂ] LpR p where
  toFun f := (memLp_plusFun hp f).toLp (plusFun f)
  map_add' f g :=
    (MemLp.toLp_congr _ _ (EventuallyEq.of_eq (plusFun_add f g))).trans (MemLp.toLp_add _ _)
  map_smul' c f :=
    (MemLp.toLp_congr _ _ (EventuallyEq.of_eq (plusFun_smul c f))).trans (MemLp.toLp_const_smul c _)

theorem plusLM_apply (hp : 1 < p) (f : SchwartzMap ℝ ℂ) :
    plusLM hp f = (memLp_plusFun hp f).toLp (plusFun f) := rfl

theorem sin_pi_div_pos (hp : 1 < p) : 0 < Real.sin (Real.pi / p) :=
  Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hp)

theorem norm_plusLM_le (hp : 1 < p) (f : SchwartzMap ℝ ℂ) :
    ‖plusLM hp f‖ ≤ (1 / Real.sin (Real.pi / p)) * ‖f.toLp (ENNReal.ofReal p) volume‖ := by
  have hC : 0 ≤ 1 / Real.sin (Real.pi / p) := (one_div_pos.mpr (sin_pi_div_pos hp)).le
  have hb := (GKSharp.Cited.hv2000_thm31_schwartz p hp f).2
  rw [plusLM_apply, Lp.norm_toLp, SchwartzMap.norm_toLp, ← ENNReal.toReal_ofReal hC, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (f.memLp _ volume).eLpNorm_ne_top) hb

variable [Fact (1 ≤ ENNReal.ofReal p)]

/-- Schwartz inputs as L^p elements, as a ℂ-linear map. -/
noncomputable def toLpLM : SchwartzMap ℝ ℂ →ₗ[ℂ] LpR p :=
  ((SchwartzMap.toLpCLM (E := ℝ) ℂ ℂ (ENNReal.ofReal p) volume : SchwartzMap ℝ ℂ →L[ℂ] LpR p) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] LpR p)

theorem toLpLM_apply (f : SchwartzMap ℝ ℂ) :
    (toLpLM : SchwartzMap ℝ ℂ →ₗ[ℂ] LpR p) f = f.toLp (ENNReal.ofReal p) volume := rfl

theorem denseRange_toLpLM : DenseRange (toLpLM : SchwartzMap ℝ ℂ →ₗ[ℂ] LpR p) := by
  have h := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (μ := volume)
    (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top
  have hcoe : ⇑(toLpLM : SchwartzMap ℝ ℂ →ₗ[ℂ] LpR p) =
      ⇑(SchwartzMap.toLpCLM ℝ ℂ (ENNReal.ofReal p) volume) := by
    funext f
    rfl
  rw [hcoe]
  exact h

/-- P₊ on L^p: the extension of `plusLM` by density of the Schwartz class. -/
noncomputable def plusOp (hp : 1 < p) : LpR p →L[ℂ] LpR p := (plusLM hp).extendOfNorm toLpLM

theorem plusOp_toLp (hp : 1 < p) (f : SchwartzMap ℝ ℂ) :
    plusOp hp (toLpLM f) = plusLM hp f :=
  LinearMap.extendOfNorm_eq denseRange_toLpLM ⟨_, norm_plusLM_le hp⟩ f

/-- The weak test v ↦ ∫ v·g (g Schwartz) is a continuous linear functional on L^p (Hölder). -/
theorem exists_testCLM (hp : 1 < p) (g : SchwartzMap ℝ ℂ) :
    ∃ Λ : LpR p →L[ℂ] ℂ, ∀ u : LpR p, Λ u = ∫ x, u x * g x := by
  have hconjR : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have hq1 : 1 < p / (p - 1) := hconjR.symm.lt
  have : Fact (1 ≤ ENNReal.ofReal (p / (p - 1))) :=
    ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le⟩
  have : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal (p / (p - 1))) :=
    ⟨by rw [inv_one]; exact hconjR.inv_add_inv_ennreal⟩
  refine ⟨((ContinuousLinearMap.mul ℂ ℂ).lpPairing volume (ENNReal.ofReal p)
    (ENNReal.ofReal (p / (p - 1)))).flip (g.toLp (ENNReal.ofReal (p / (p - 1))) volume), fun u => ?_⟩
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp (ENNReal.ofReal (p / (p - 1))) volume] with x hx
  rw [hx]
  rfl

/-- Schwartz duality for P₊: ∫ P₊f · 𝓕φ = ∫ χ_{(0,∞)} 𝓕f · φ. -/
theorem integral_plusFun_mul (f φ : SchwartzMap ℝ ℂ) :
    ∫ x, plusFun f x * 𝓕 φ x = ∫ ξ, halfMask f ξ * φ ξ := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_neg_inner (integrable_halfMask f) (𝓕 φ).integrable
  have hflip : (-innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = -innerₗ ℝ := by
    ext
    simp only [LinearMap.flip_apply, LinearMap.neg_apply, innerₗ_apply_apply]
  rw [hflip] at h
  have hinv : ∀ x, VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ ℝ)
      ⇑(𝓕 φ : SchwartzMap ℝ ℂ) x = φ x := fun x => by
    change 𝓕⁻ ⇑(𝓕 φ : SchwartzMap ℝ ℂ) x = φ x
    rw [← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]
  have hP : ∀ x, plusFun f x = VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ ℝ) (halfMask f) x :=
    fun x => rfl
  simp only [smul_eq_mul, hinv] at h
  simp only [hP]
  exact h

theorem integral_halfMask_mul_pos (f φ : SchwartzMap ℝ ℂ) (hφ : Function.support φ ⊆ Set.Ioi 0) :
    ∫ ξ, halfMask f ξ * φ ξ = ∫ x, f x * 𝓕 φ x := by
  rw [← SchwartzMap.integral_fourier_mul_eq]
  congr 1
  funext ξ
  by_cases hξ : φ ξ = 0
  · simp [hξ]
  · rw [halfMask, Set.indicator_of_mem (hφ (Function.mem_support.mpr hξ)), SchwartzMap.fourier_coe]

theorem integral_halfMask_mul_neg (f φ : SchwartzMap ℝ ℂ) (hφ : Function.support φ ⊆ Set.Iio 0) :
    ∫ ξ, halfMask f ξ * φ ξ = 0 := by
  have hz : ∀ ξ, halfMask f ξ * φ ξ = 0 := fun ξ => by
    by_cases hξ : φ ξ = 0
    · simp [hξ]
    · have hout : ξ ∉ Set.Ioi (0 : ℝ) := fun hin =>
        lt_asymm (show ξ < 0 from hφ (Function.mem_support.mpr hξ)) hin
      rw [halfMask, Set.indicator_of_notMem hout, zero_mul]
  simp [hz]

/-- A weak test of P₊ that holds on Schwartz inputs holds on all of L^p (density + continuity). -/
theorem test_plusOp (hp : 1 < p) (φ : SchwartzMap ℝ ℂ) (c : ℂ)
    (hc : ∀ f : SchwartzMap ℝ ℂ, ∫ ξ, halfMask f ξ * φ ξ = c * ∫ x, f x * 𝓕 φ x)
    (Λ : LpR p →L[ℂ] ℂ) (hΛ : ∀ u : LpR p, Λ u = ∫ x, u x * 𝓕 φ x) (u : LpR p) :
    Λ (plusOp hp u) = c * Λ u := by
  refine denseRange_toLpLM.induction_on u
    (isClosed_eq (Λ.continuous.comp (plusOp hp).continuous) (continuous_const.mul Λ.continuous))
    (fun f => ?_)
  rw [plusOp_toLp, toLpLM_apply, hΛ, hΛ, integral_toLp_mul, ← hc f, ← integral_plusFun_mul, plusLM_apply]
  apply integral_congr_ae
  filter_upwards [(memLp_plusFun hp f).coeFn_toLp] with x hx
  rw [hx]

/-- The real-line pencil α P₊ + β (1 − P₊) on L^p. -/
noncomputable def pencilOp (hp : 1 < p) (α β : ℂ) : LpR p →L[ℂ] LpR p :=
  α • plusOp hp + β • (ContinuousLinearMap.id ℂ (LpR p) - plusOp hp)

theorem pencilOp_test (hp : 1 < p) (α β : ℂ) (φ : SchwartzMap ℝ ℂ) (c : ℂ)
    (hc : ∀ f : SchwartzMap ℝ ℂ, ∫ ξ, halfMask f ξ * φ ξ = c * ∫ x, f x * 𝓕 φ x) (u : LpR p) :
    (∫ x, pencilOp hp α β u x * 𝓕 φ x) = (α * c + β * (1 - c)) * ∫ x, u x * 𝓕 φ x := by
  obtain ⟨Λ, hΛ⟩ := exists_testCLM hp (𝓕 φ)
  rw [← hΛ, ← hΛ]
  have hP := test_plusOp hp φ c hc Λ hΛ u
  simp only [pencilOp, add_apply, smul_apply, sub_apply, ContinuousLinearMap.id_apply, map_add, map_smul, map_sub, smul_eq_mul, hP]
  ring

/-- The pencil passes both weak half-line tests. -/
noncomputable def realLinePencil (hp : 1 < p) (α β : ℂ) : RealLinePencil p α β where
  map := pencilOp hp α β
  positive_test f φ hφ := by
    rw [pencilOp_test hp α β φ 1 (fun g => by rw [one_mul]; exact integral_halfMask_mul_pos g φ hφ) f]
    ring
  negative_test f φ hφ := by
    rw [pencilOp_test hp α β φ 0 (fun g => by rw [zero_mul]; exact integral_halfMask_mul_neg g φ hφ) f]
    ring

/-- N01_nonvacuity: for 1 < p and all α, β a RealLinePencil exists (cited input: HV2000 Theorem 3.1). -/
theorem slice_N01_nonvacuity_proved (hp : 1 < p) (α β : ℂ) : Nonempty (RealLinePencil p α β) :=
  ⟨realLinePencil hp α β⟩

end GKSharp.Proofs.RealLineExists
