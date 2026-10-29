/- GKSharp/Proofs/N06Forward.lean - row slice_N06 (norm_correspondence.tex l.20-37): the circle pencil, circleMinus and
circleMid are bounded by the real-line multiplier's norm ‖T.map‖. Premise style: GIVEN the exact frozen N03, N04,
N04_minus, N05 (APPROVED_SLICE_A_Operators_v020.lean l.131-162).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.RealLineFourier
import GKSharp.Proofs.NormTransference
import GKSharp.Proofs.CircleMapNorm

namespace GKSharp.N06

open GKSharp GKSharp.RealLineFourier MeasureTheory Filter Topology DensityLp

/-! ## The window: `‖Z‖^p = ‖η(h·)‖^p · ‖F‖^p` and `∫ |η|^p > 0` -/

/-- The continuous `2π`-periodic weight `x ↦ ‖G x‖^p` of a continuous circle function `G`. -/
noncomputable def weight (p : ℝ) (G : C(Circ, ℂ)) (x : ℝ) : ℝ := ‖G (x : Circ)‖ ^ p

theorem continuous_weight {p : ℝ} (hp : 0 < p) (G : C(Circ, ℂ)) : Continuous (weight p G) := by
  unfold weight
  exact (G.continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))).norm.rpow_const fun _ => Or.inr hp.le

theorem periodic_weight {p : ℝ} (G : C(Circ, ℂ)) : Function.Periodic (weight p G) (2 * Real.pi) := fun x => by
  simp only [weight, AddCircle.coe_add_period]

theorem norm_modulation (d x : ℝ) : ‖Complex.exp (Complex.I * (d : ℂ) * x)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norm_modulation_neg (d x : ℝ) : ‖Complex.exp (-(Complex.I * (d : ℂ) * x))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- A modulated window `Z = η(h·) m F` with `|m| = 1` has `|Z|^p = |η(h·)|^p ‖F‖^p`. -/
theorem integral_window {p : ℝ} (η Z : SchwartzMap ℝ ℂ) (h : ℝ) {m : ℝ → ℂ} (hm : ∀ x, ‖m x‖ = 1)
    (F : C(Circ, ℂ)) (hZ : ∀ x, Z x = η (h * x) * m x * F (x : Circ)) :
    ∫ x, ‖Z x‖ ^ p = ∫ x, ‖η (h * x)‖ ^ p * weight p F x := by
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [hZ x, norm_mul, hm x, mul_one, weight]
  exact Real.mul_rpow (norm_nonneg _) (norm_nonneg _)

theorem integral_window_pos {p : ℝ} (hp : 0 < p) {η : SchwartzMap ℝ ℂ} (hη : η ≠ 0) :
    0 < ∫ x, ‖η x‖ ^ p := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, η x ≠ 0 := by
    by_contra hcon
    exact hη (SchwartzMap.ext fun x => by simpa using not_exists.mp hcon x)
  have hp0 : ENNReal.ofReal p ≠ 0 := by positivity
  have hint : Integrable (fun x => ‖η x‖ ^ p) := by
    simpa [ENNReal.toReal_ofReal hp.le] using
      (η.memLp (ENNReal.ofReal p) volume).integrable_norm_rpow hp0 ENNReal.ofReal_ne_top
  exact integral_pos_of_integrable_nonneg_nonzero (x := x₀)
    (η.continuous.norm.rpow_const fun _ => Or.inr hp.le) hint
    (fun x => Real.rpow_nonneg (norm_nonneg _) p) (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx₀) p).ne'

/-! ## Letting `h → 0` (N05) and cancelling `∫ |η|^p > 0` -/

theorem limit_step {p : ℝ} {η : SchwartzMap ℝ ℂ} (hη : 0 < ∫ x, ‖η x‖ ^ p) {AW AZ : ℝ → ℝ} {K : ℝ}
    (tW : Tendsto (fun h : ℝ => h * ∫ x : ℝ, ‖η (h * x)‖ ^ p * AW x) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((∫ x : ℝ, ‖η x‖ ^ p) * ((2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), AW t))))
    (tZ : Tendsto (fun h : ℝ => h * ∫ x : ℝ, ‖η (h * x)‖ ^ p * AZ x) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((∫ x : ℝ, ‖η x‖ ^ p) * ((2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), AZ t))))
    (hloc : ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∫ x : ℝ, ‖η (h * x)‖ ^ p * AW x ≤ K * ∫ x : ℝ, ‖η (h * x)‖ ^ p * AZ x) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), AW t ≤ K * ∫ t in (0 : ℝ)..(2 * Real.pi), AZ t := by
  obtain ⟨h₀, h₀pos, hb⟩ := hloc
  have hev : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      h * ∫ x : ℝ, ‖η (h * x)‖ ^ p * AW x ≤ K * (h * ∫ x : ℝ, ‖η (h * x)‖ ^ p * AZ x) := by
    filter_upwards [Ioo_mem_nhdsGT h₀pos] with h hh
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hb h hh.1 hh.2) hh.1.le
  have hlim := le_of_tendsto_of_tendsto tW (tZ.const_mul K) hev
  have hc : 0 < (∫ x : ℝ, ‖η x‖ ^ p) * (2 * Real.pi)⁻¹ := by positivity
  refine le_of_mul_le_mul_left ?_ hc
  calc _ = (∫ x : ℝ, ‖η x‖ ^ p) * ((2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), AW t) := by ring
    _ ≤ _ := hlim
    _ = _ := by ring

section Circle

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-! ## One trigonometric polynomial: `‖G‖_{L^p(T)} ≤ ‖T‖ ‖F‖_{L^p(T)}` -/

/-- `T Z = W` gives `∫ |W|^p ≤ ‖T‖^p ∫ |Z|^p`. -/
theorem real_step (hp : 0 < p) (T : LpR p →L[ℂ] LpR p) (Z W : SchwartzMap ℝ ℂ)
    (hTW : T (Z.toLp (ENNReal.ofReal p) volume) = W.toLp (ENNReal.ofReal p) volume) :
    ∫ x, ‖W x‖ ^ p ≤ ‖T‖ ^ p * ∫ x, ‖Z x‖ ^ p := by
  have h := T.le_opNorm (Z.toLp (ENNReal.ofReal p) volume)
  rw [hTW] at h
  have h2 := Real.rpow_le_rpow (norm_nonneg _) h hp.le
  rwa [Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Proofs.NormTransference.schwartz_norm_rpow p hp,
    Proofs.NormTransference.schwartz_norm_rpow p hp] at h2

/-- The transference step: if for all small `h` the multiplier `T` maps the window `η(h·) m F` to `η(h·) m G`, then
`‖G‖_p ≤ ‖T‖ ‖F‖_p` on the circle. -/
theorem circle_bound (hp : 1 < p) (T : LpR p →L[ℂ] LpR p) {η : SchwartzMap ℝ ℂ}
    (hη : 0 < ∫ x, ‖η x‖ ^ p)
    (hN05 : ∀ A : ℝ → ℝ, Continuous A → Function.Periodic A (2 * Real.pi) →
      Tendsto (fun h : ℝ => h * ∫ x : ℝ, ‖η (h * x)‖ ^ p * A x) (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 ((∫ x : ℝ, ‖η x‖ ^ p) * ((2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), A t))))
    {m : ℝ → ℂ} (hm : ∀ x, ‖m x‖ = 1) (F G : C(Circ, ℂ))
    (hloc : ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ → ∃ Z W : SchwartzMap ℝ ℂ,
      (∀ x, Z x = η (h * x) * m x * F (x : Circ)) ∧ (∀ x, W x = η (h * x) * m x * G (x : Circ)) ∧
      T (Z.toLp (ENNReal.ofReal p) volume) = W.toLp (ENNReal.ofReal p) volume) :
    ‖toLpT p G‖ ≤ ‖T‖ * ‖toLpT p F‖ := by
  have hp0 : 0 < p := by linarith
  obtain ⟨h₀, h₀pos, hb⟩ := hloc
  have hint := limit_step (K := ‖T‖ ^ p) hη (hN05 _ (continuous_weight hp0 G) (periodic_weight G))
    (hN05 _ (continuous_weight hp0 F) (periodic_weight F)) ⟨h₀, h₀pos, fun h h1 h2 => by
      obtain ⟨Z, W, hZ, hW, hTW⟩ := hb h h1 h2
      have hs := real_step hp0 T Z W hTW
      rwa [integral_window η Z h hm F hZ, integral_window η W h hm G hW] at hs⟩
  have hpow : ‖toLpT p G‖ ^ p ≤ (‖T‖ * ‖toLpT p F‖) ^ p := by
    rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Proofs.NormTransference.circle_norm_rpow hp0,
      Proofs.NormTransference.circle_norm_rpow hp0]
    exact hint
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) hp0).mp hpow

/-! ## The circle maps on a trigonometric polynomial `F = Σ c_n e^{inθ}` -/

/-- `αP₊F + βP₋F` (constant frequency to `α`): the pencil's image. -/
noncomputable def plusImage (α β : ℂ) (c : ℤ →₀ ℂ) : C(Circ, ℂ) := α • pC c + β • mC c

/-- `αP₊F + βP₋F + (β − α) c₀` (constant frequency to `β`): circleMinus's image. -/
noncomputable def minusImage (α β : ℂ) (c : ℤ →₀ ℂ) : C(Circ, ℂ) :=
  plusImage α β c + ContinuousMap.const Circ ((β - α) * c 0)

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem plusImage_coe (α β : ℂ) (c : ℤ →₀ ℂ) (x : ℝ) :
    plusImage α β c (x : Circ) = α * Pplus c x + β * Pminus c x := by
  simp [plusImage, pC_coe, mC_coe]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem minusImage_coe (α β : ℂ) (c : ℤ →₀ ℂ) (x : ℝ) :
    minusImage α β c (x : Circ) = α * Pplus c x + β * Pminus c x + (β - α) * c 0 := by
  rw [minusImage, ContinuousMap.add_apply, plusImage_coe, ContinuousMap.const_apply]

theorem pencil_trig (P : RieszProjection p) (α β : ℂ) (c : ℤ →₀ ℂ) :
    pencil P α β (toLpT p (tC c)) = toLpT p (plusImage α β c) := by
  have hlin : toLpT p (plusImage α β c) = α • toLpT p (pC c) + β • toLpT p (mC c) := by
    simp only [plusImage, DensityLp.toLpT, map_add, map_smul]
  refine fourier_ext _ _ fun n => ?_
  rw [coeff_pencil, hlin, coeff_add, coeff_smul, coeff_smul, coeff_toLpT, coeff_toLpT, coeff_toLpT, coeff_tC,
    coeff_pC, coeff_mC]
  split_ifs <;> first | ring1 | (exfalso; omega)

theorem circleMinus_trig (P : RieszProjection p) (α β : ℂ) (c : ℤ →₀ ℂ) :
    circleMinus P α β (toLpT p (tC c)) = toLpT p (minusImage α β c) := by
  have hz : zeroPart p (toLpT p (tC c)) = toLpT p (ContinuousMap.const Circ (c 0)) := by
    unfold zeroPart constantLp
    rw [coeff_toLpT, coeff_tC]
  have hconst : ContinuousMap.const Circ ((β - α) * c 0) = (β - α) • ContinuousMap.const Circ (c 0) := by
    ext x
    simp
  unfold circleMinus
  rw [pencil_trig, hz, minusImage, hconst]
  simp only [DensityLp.toLpT, map_add, map_smul]

/-! ## Density: a bound on trigonometric polynomials holds on all of `L^p(T)` -/

theorem bound_of_trig {S : LpT p → LpT p} (hS : Continuous S) {K : ℝ}
    (htrig : ∀ c, ‖S (toLpT p (tC c))‖ ≤ K * ‖toLpT p (tC c)‖) (f : LpT p) : ‖S f‖ ≤ K * ‖f‖ := by
  obtain ⟨c, hc⟩ := exists_trig_tendsto f
  exact le_of_tendsto_of_tendsto' ((hS.tendsto f).comp hc).norm (hc.norm.const_mul K) fun k => htrig (c k)

end Circle

/-! ## Row slice_N06 -/

/-- **slice_N06**, premise style. GIVEN the exact frozen types of slice_N03 (a nonzero band-limited Schwartz window),
slice_N04 and slice_N04_minus (localization) and slice_N05 (weighted periodic averaging): the circle pencil, circleMinus
and circleMid are bounded by the real-line multiplier's operator norm (d = 1/2; circleMid is the mean). -/
theorem slice_N06_given
    (hN03 : ∃ η : SchwartzMap ℝ ℂ, η ≠ 0 ∧ HasCompactSupport (paperFourier η))
    (hN04 : ∀ {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (_hp : 1 < p) (_P : RieszProjection p) (α β : ℂ)
      (T : RealLinePencil p α β) (d : ℝ) (_hd : 0 < d ∧ d < 1) (η : SchwartzMap ℝ ℂ)
      (_hη : HasCompactSupport (paperFourier η)) (c : ℤ →₀ ℂ),
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∃ Z W : SchwartzMap ℝ ℂ,
          (∀ x, Z x = η (h * x) * Complex.exp (Complex.I * (d : ℂ) * x) * trig c x) ∧
          (∀ x, W x = η (h * x) * Complex.exp (Complex.I * (d : ℂ) * x) *
            (α * Pplus c x + β * Pminus c x)) ∧
          T.map (Z.toLp (ENNReal.ofReal p) volume) = W.toLp (ENNReal.ofReal p) volume)
    (hN04m : ∀ {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (_hp : 1 < p) (α β : ℂ) (T : RealLinePencil p α β)
      (d : ℝ) (_hd : 0 < d ∧ d < 1) (η : SchwartzMap ℝ ℂ)
      (_hη : HasCompactSupport (paperFourier η)) (c : ℤ →₀ ℂ),
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∃ Z W : SchwartzMap ℝ ℂ,
          (∀ x, Z x = η (h * x) * Complex.exp (-(Complex.I * (d : ℂ) * x)) * trig c x) ∧
          (∀ x, W x = η (h * x) * Complex.exp (-(Complex.I * (d : ℂ) * x)) *
            (α * Pplus c x + β * Pminus c x + (β - α) * c 0)) ∧
          T.map (Z.toLp (ENNReal.ofReal p) volume) = W.toLp (ENNReal.ofReal p) volume)
    (hN05 : ∀ {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (_hp : 1 < p) (η : SchwartzMap ℝ ℂ) (A : ℝ → ℝ)
      (_hA : Continuous A) (_hper : Function.Periodic A (2 * Real.pi)),
      Tendsto (fun h : ℝ => h * ∫ x : ℝ, ‖η (h * x)‖ ^ p * A x)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 ((∫ x : ℝ, ‖η x‖ ^ p) * ((2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), A t))))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) (α β : ℂ)
    (T : RealLinePencil p α β) :
    ‖pencil P α β‖ ≤ ‖T.map‖ ∧ functionNorm (circleMinus P α β) ≤ ‖T.map‖ ∧
      functionNorm (circleMid P α β) ≤ ‖T.map‖ := by
  obtain ⟨η, hη0, hηc⟩ := hN03
  have hIη := integral_window_pos (p := p) (by linarith) hη0
  have hd : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by norm_num
  have hav := fun A hA hper => hN05 hp η A hA hper
  have hplus : ∀ f, ‖pencil P α β f‖ ≤ ‖T.map‖ * ‖f‖ := bound_of_trig (pencil P α β).continuous fun c => by
    obtain ⟨h₀, h₀pos, hb⟩ := hN04 hp P α β T (1 / 2) hd η hηc c
    rw [pencil_trig]
    refine circle_bound hp T.map hIη hav (norm_modulation (1 / 2)) (tC c) (plusImage α β c)
      ⟨h₀, h₀pos, fun h h1 h2 => ?_⟩
    obtain ⟨Z, W, hZ, hW, hTW⟩ := hb h h1 h2
    exact ⟨Z, W, fun x => by rw [hZ x, tC_coe], fun x => by rw [hW x, plusImage_coe], hTW⟩
  have hminus : ∀ f, ‖circleMinus P α β f‖ ≤ ‖T.map‖ * ‖f‖ :=
    bound_of_trig (CircleMapNorm.continuous_circleMinus P α β) fun c => by
      obtain ⟨h₀, h₀pos, hb⟩ := hN04m hp α β T (1 / 2) hd η hηc c
      rw [circleMinus_trig]
      refine circle_bound hp T.map hIη hav (norm_modulation_neg (1 / 2)) (tC c) (minusImage α β c)
        ⟨h₀, h₀pos, fun h h1 h2 => ?_⟩
      obtain ⟨Z, W, hZ, hW, hTW⟩ := hb h h1 h2
      exact ⟨Z, W, fun x => by rw [hZ x, tC_coe], fun x => by rw [hW x, minusImage_coe], hTW⟩
  have hmid : ∀ f, ‖circleMid P α β f‖ ≤ ‖T.map‖ * ‖f‖ := fun f => by
    have h := CircleMapNorm.norm_half_add_le (hplus f) (hminus f)
    rwa [add_self_div_two] at h
  exact ⟨ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) hplus,
    CircleMapNorm.functionNorm_le (norm_nonneg _) hminus, CircleMapNorm.functionNorm_le (norm_nonneg _) hmid⟩

end GKSharp.N06
