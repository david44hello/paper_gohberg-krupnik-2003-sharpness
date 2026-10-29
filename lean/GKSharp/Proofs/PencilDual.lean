/- GKSharp/Proofs/PencilDual.lean - the complex L^p-L^p' pairing on the circle: I07 (both projections are
self-adjoint), I10 (N_p(rho) = N_p'(conj rho)) and I11 (reduction to |rho| <= 1, 1 < p < 2).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.PencilSymm

namespace GKSharp

open MeasureTheory Filter Topology

/-- `∫ g dvolume = 2π ∫ g dhaar` on the circle `ℝ/2πℤ`, for complex `g`. -/
theorem integral_volume_eq_complex (g : Circ → ℂ) :
    ∫ x, g x ∂(volume : Measure Circ) = ((2 * Real.pi : ℝ) : ℂ) * ∫ x, g x ∂AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), Complex.real_smul]

/-- `‖h‖ = (∫ |h|^p)^(1/p)` on `LpT p`, `0 < p`. -/
theorem norm_LpT_eq {p : ℝ} (hp : 0 < p) (h : LpT p) : ‖h‖ = (∫ x, ‖h x‖ ^ p) ^ (1 / p) := by
  rw [Lp.norm_def, (Lp.memLp h).eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _), one_div]

section Pairing

variable {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]

/-- The complex pairing `⟨h, g⟩ = ∫ h ḡ` of `LpT p` and `LpT q` (P019_paper.tex:53). -/
noncomputable def pair (h : LpT p) (g : LpT q) : ℂ := ∫ x, h x * (starRingEnd ℂ) (g x)

omit [Fact (1 ≤ ENNReal.ofReal q)] in
theorem memLp_conj (g : LpT q) : MemLp (fun x => (starRingEnd ℂ) (g x)) (ENNReal.ofReal q) volume :=
  (Lp.memLp g).mono (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable g))
    (Filter.Eventually.of_forall fun x => by simp)

omit [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)] in
theorem integrable_pair (hpq : p.HolderConjugate q) (h : LpT p) (g : LpT q) :
    Integrable (fun x => h x * (starRingEnd ℂ) (g x)) volume := by
  have := hpq.ennrealOfReal
  exact (Lp.memLp h).integrable_mul (memLp_conj g)

omit [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)] in
/-- Hölder: `|⟨h, g⟩| ≤ ‖h‖_p ‖g‖_q`. -/
theorem norm_pair_le (hpq : p.HolderConjugate q) (h : LpT p) (g : LpT q) : ‖pair h g‖ ≤ ‖h‖ * ‖g‖ := by
  calc ‖pair h g‖ ≤ ∫ x, ‖h x‖ * ‖g x‖ := by
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        congr 1
        ext x
        rw [norm_mul, Complex.norm_conj]
    _ ≤ (∫ x, ‖h x‖ ^ p) ^ (1 / p) * (∫ x, ‖g x‖ ^ q) ^ (1 / q) :=
        integral_mul_norm_le_Lp_mul_Lq hpq (Lp.memLp h) (Lp.memLp g)
    _ = ‖h‖ * ‖g‖ := by rw [norm_LpT_eq hpq.pos, norm_LpT_eq hpq.symm.pos]

omit [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)] in
theorem pair_add_right (hpq : p.HolderConjugate q) (h : LpT p) (g₁ g₂ : LpT q) :
    pair h (g₁ + g₂) = pair h g₁ + pair h g₂ := by
  unfold pair
  rw [← integral_add (integrable_pair hpq h g₁) (integrable_pair hpq h g₂)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add g₁ g₂] with x hx
  rw [hx, Pi.add_apply, map_add, mul_add]

omit [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)] in
theorem pair_add_left (hpq : p.HolderConjugate q) (h₁ h₂ : LpT p) (g : LpT q) :
    pair (h₁ + h₂) g = pair h₁ g + pair h₂ g := by
  unfold pair
  rw [← integral_add (integrable_pair hpq h₁ g) (integrable_pair hpq h₂ g)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add h₁ h₂] with x hx
  rw [hx, Pi.add_apply, add_mul]

omit [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)] in
theorem pair_smul_right (h : LpT p) (a : ℂ) (g : LpT q) :
    pair h (a • g) = (starRingEnd ℂ) a * pair h g := by
  unfold pair
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul a g] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

omit [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)] in
theorem pair_smul_left (a : ℂ) (h : LpT p) (g : LpT q) : pair (a • h) g = a * pair h g := by
  unfold pair
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul a h] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)] in
theorem pair_sub_right (hpq : p.HolderConjugate q) (h : LpT p) (g₁ g₂ : LpT q) :
    pair h (g₁ - g₂) = pair h g₁ - pair h g₂ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ g₂, pair_add_right hpq, pair_smul_right, map_neg, map_one]
  ring

omit [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)] in
theorem pair_sub_left (hpq : p.HolderConjugate q) (h₁ h₂ : LpT p) (g : LpT q) :
    pair (h₁ - h₂) g = pair h₁ g - pair h₂ g := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ h₂, pair_add_left hpq, pair_smul_left]
  ring

omit [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)] in
theorem pair_zero_right (h : LpT p) : pair h (0 : LpT q) = 0 := by
  simpa using pair_smul_right h (0 : ℂ) (0 : LpT q)

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- `g ↦ ⟨h, g⟩` is continuous (Hölder). -/
theorem pair_tendsto_right (hpq : p.HolderConjugate q) (h : LpT p) {g : ℕ → LpT q} {g₀ : LpT q}
    (hg : Tendsto g atTop (𝓝 g₀)) : Tendsto (fun k => pair h (g k)) atTop (𝓝 (pair h g₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun k => ‖h‖ * ‖g k - g₀‖) atTop (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hg).const_mul ‖h‖
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hb
  rw [← pair_sub_right hpq]
  exact norm_pair_le hpq h _

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- `⟨h, eₙ⟩ = 2π ĥ(n)` (the measure `volume` has mass `2π`). -/
theorem pair_mode (h : LpT p) (n : ℤ) :
    pair h (DensityLp.toLpT q (fourier n)) = ((2 * Real.pi : ℝ) : ℂ) * fourierCoeff (⇑h) n := by
  have hae : (fun x => h x * (starRingEnd ℂ) (DensityLp.toLpT q (fourier n) x)) =ᵐ[volume]
      fun x => fourier (-n) x • h x := by
    filter_upwards [DensityLp.coeFn_toLpT (p := q) (fourier n)] with x hx
    rw [hx, fourier_neg, smul_eq_mul, mul_comm]
  unfold pair fourierCoeff
  rw [integral_congr_ae hae, integral_volume_eq_complex]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem toLpT_zero : DensityLp.toLpT q 0 = 0 := map_zero _

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem toLpT_add (φ ψ : C(Circ, ℂ)) : DensityLp.toLpT q (φ + ψ) = DensityLp.toLpT q φ + DensityLp.toLpT q ψ :=
  map_add _ φ ψ

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem toLpT_smul (a : ℂ) (φ : C(Circ, ℂ)) : DensityLp.toLpT q (a • φ) = a • DensityLp.toLpT q φ :=
  map_smul _ a φ

omit [Fact (1 ≤ ENNReal.ofReal q)] in
theorem plus_mode (P : RieszProjection p) (n : ℤ) :
    P.plus (DensityLp.toLpT p (fourier n)) = (if 0 ≤ n then (1 : ℂ) else 0) • DensityLp.toLpT p (fourier n) := by
  rw [← pencil_one_zero]
  exact pencil_mode P 1 0 n

/-- I07, P019_paper.tex:53: `P₊` is self-adjoint for the complex pairing: `⟨P₊f, g⟩ = ⟨f, P₊g⟩`. -/
theorem pair_plus (hpq : p.HolderConjugate q) (P : RieszProjection p) (Q : RieszProjection q) (f : LpT p)
    (g : LpT q) : pair (P.plus f) g = pair f (Q.plus g) := by
  have htrig : ∀ c : ℤ →₀ ℂ, pair (P.plus f) (DensityLp.toLpT q (DensityLp.tC c)) =
      pair f (Q.plus (DensityLp.toLpT q (DensityLp.tC c))) := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero =>
      have h0 : DensityLp.tC (0 : ℤ →₀ ℂ) = 0 := map_zero _
      rw [h0, toLpT_zero, map_zero, pair_zero_right, pair_zero_right]
    | add c₁ c₂ h₁ h₂ =>
      have hadd : DensityLp.tC (c₁ + c₂) = DensityLp.tC c₁ + DensityLp.tC c₂ := map_add _ c₁ c₂
      rw [hadd, toLpT_add, map_add, pair_add_right hpq, pair_add_right hpq, h₁, h₂]
    | single n a =>
      have hs : DensityLp.tC (Finsupp.single n a) = a • (fourier n : C(Circ, ℂ)) :=
        Finsupp.linearCombination_single _ _ _
      rw [hs, toLpT_smul, map_smul, pair_smul_right, pair_smul_right, pair_mode, plus_mode, pair_smul_right,
        pair_mode, P.coeff_plus]
      split_ifs <;> simp
  obtain ⟨c, hc⟩ := DensityLp.exists_trig_tendsto g
  have h1 := pair_tendsto_right hpq (P.plus f) hc
  have h2 := pair_tendsto_right hpq f ((Q.plus.continuous.tendsto g).comp hc)
  exact tendsto_nhds_unique (h1.congr fun k => htrig (c k)) h2

/-- I07 for `P₋`: `⟨P₋f, g⟩ = ⟨f, P₋g⟩`. -/
theorem pair_minus (hpq : p.HolderConjugate q) (P : RieszProjection p) (Q : RieszProjection q) (f : LpT p)
    (g : LpT q) : pair (rieszMinus P f) g = pair f (rieszMinus Q g) := by
  have hP : rieszMinus P f = f - P.plus f := rfl
  have hQ : rieszMinus Q g = g - Q.plus g := rfl
  rw [hP, hQ, pair_sub_left hpq, pair_sub_right hpq, pair_plus hpq P Q]

/-- The pencil's adjoint: `⟨(αP₊ + βP₋)f, g⟩ = ⟨f, (ᾱP₊ + β̄P₋)g⟩`. -/
theorem pair_pencil (hpq : p.HolderConjugate q) (P : RieszProjection p) (Q : RieszProjection q) (α β : ℂ)
    (f : LpT p) (g : LpT q) :
    pair (pencil P α β f) g = pair f (pencil Q ((starRingEnd ℂ) α) ((starRingEnd ℂ) β) g) := by
  have hP : pencil P α β f = α • P.plus f + β • rieszMinus P f := rfl
  have hQ : pencil Q ((starRingEnd ℂ) α) ((starRingEnd ℂ) β) g =
      (starRingEnd ℂ) α • Q.plus g + (starRingEnd ℂ) β • rieszMinus Q g := rfl
  rw [hP, hQ, pair_add_left hpq, pair_add_right hpq, pair_smul_left, pair_smul_left, pair_smul_right,
    pair_smul_right, Complex.conj_conj, Complex.conj_conj, pair_plus hpq P Q, pair_minus hpq P Q]

end Pairing

/-! ## The norming function `|h|^{p-2} h` -/

/-- `r^{p-2} r^2 = r^p` for `r ≥ 0`, `0 < p` (both sides vanish at `r = 0`). -/
theorem rpow_sub_two_mul_sq {p r : ℝ} (hp : 0 < p) (hr : 0 ≤ r) : r ^ (p - 2) * r ^ 2 = r ^ p := by
  rcases eq_or_lt_of_le hr with h0 | hpos
  · subst h0
    rw [Real.zero_rpow hp.ne', zero_pow two_ne_zero, mul_zero]
  · rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
    norm_num

/-- `r^{p-2} r = r^{p-1}` for `r ≥ 0`, `1 < p`. -/
theorem rpow_sub_two_mul_self {p r : ℝ} (hp : 1 < p) (hr : 0 ≤ r) : r ^ (p - 2) * r = r ^ (p - 1) := by
  rcases eq_or_lt_of_le hr with h0 | hpos
  · subst h0
    rw [Real.zero_rpow (by linarith : p - 1 ≠ 0), mul_zero]
  · rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one hpos.ne']

/-- `r^p = r · r^{p-1}` for `r > 0`. -/
theorem rpow_eq_mul_rpow_sub_one {r p : ℝ} (hr : 0 < r) : r ^ p = r * r ^ (p - 1) := by
  rw [Real.rpow_sub hr, Real.rpow_one]
  field_simp

section Norming

variable {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]

/-- The norming function `x ↦ |h(x)|^{p-2} h(x)` of `h ∈ L^p`. -/
noncomputable def normingFun (h : LpT p) (x : Circ) : ℂ := ((‖h x‖ ^ (p - 2) : ℝ) : ℂ) * h x

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem norm_normingFun (hp : 1 < p) (h : LpT p) (x : Circ) : ‖normingFun h x‖ = ‖h x‖ ^ (p - 1) := by
  rw [normingFun, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    rpow_sub_two_mul_self hp (norm_nonneg _)]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem mul_conj_normingFun (hp : 1 < p) (h : LpT p) (x : Circ) :
    h x * (starRingEnd ℂ) (normingFun h x) = ((‖h x‖ ^ p : ℝ) : ℂ) := by
  have key := rpow_sub_two_mul_sq (by linarith : (0 : ℝ) < p) (norm_nonneg (h x))
  rw [normingFun, map_mul, Complex.conj_ofReal, mul_left_comm, Complex.mul_conj', ← key, Complex.ofReal_mul,
    Complex.ofReal_pow]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem aesm_normingFun (h : LpT p) : AEStronglyMeasurable (normingFun h) volume :=
  (Complex.continuous_ofReal.comp_aestronglyMeasurable
    ((Lp.aestronglyMeasurable h).norm.aemeasurable.pow_const (p - 2)).aestronglyMeasurable).mul
    (Lp.aestronglyMeasurable h)

omit [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)] in
theorem memLp_normingFun (hpq : p.HolderConjugate q) (h : LpT p) :
    MemLp (normingFun h) (ENNReal.ofReal q) volume := by
  have hp1 : 0 ≤ p - 1 := by linarith [hpq.lt]
  have hpow := (Lp.memLp h).norm_rpow_div (ENNReal.ofReal (p - 1))
  rw [ENNReal.toReal_ofReal hp1, ← ENNReal.ofReal_div_of_pos (by linarith [hpq.lt]),
    ← hpq.conjugate_eq] at hpow
  exact hpow.mono (aesm_normingFun h) (Filter.Eventually.of_forall fun x => by
    rw [norm_normingFun hpq.lt, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)])

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- `∫ |h|^p = ‖h‖^p`. -/
theorem integral_norm_rpow_eq {p : ℝ} (hp : 0 < p) (h : LpT p) : ∫ x, ‖h x‖ ^ p = ‖h‖ ^ p := by
  rw [norm_LpT_eq hp, one_div, Real.rpow_inv_rpow (integral_nonneg fun _ => by positivity) hp.ne']

omit [Fact (1 ≤ ENNReal.ofReal q)] in
/-- The norming element: `⟨h, g⟩ = ‖h‖^p` and `‖g‖ = ‖h‖^{p-1}`. -/
theorem exists_norming (hpq : p.HolderConjugate q) (h : LpT p) :
    ∃ g : LpT q, pair h g = ((‖h‖ ^ p : ℝ) : ℂ) ∧ ‖g‖ = ‖h‖ ^ (p - 1) := by
  have hae := (memLp_normingFun hpq h).coeFn_toLp
  refine ⟨(memLp_normingFun hpq h).toLp _, ?_, ?_⟩
  · unfold pair
    rw [integral_congr_ae (hae.mono fun x hx => by rw [hx, mul_conj_normingFun hpq.lt]),
      integral_complex_ofReal, integral_norm_rpow_eq hpq.pos]
  · have hint : ∫ x, ‖((memLp_normingFun hpq h).toLp _ : LpT q) x‖ ^ q = ‖h‖ ^ p := by
      rw [← integral_norm_rpow_eq hpq.pos h]
      refine integral_congr_ae (hae.mono fun x hx => ?_)
      dsimp only
      rw [hx, norm_normingFun hpq.lt, ← Real.rpow_mul (norm_nonneg (h x)), hpq.sub_one_mul_conj]
    rw [norm_LpT_eq hpq.symm.pos, hint, ← Real.rpow_mul (norm_nonneg h), mul_one_div, hpq.div_conj_eq_sub_one]

/-- Duality: `‖h‖_p ≤ C` as soon as `|⟨h, g⟩| ≤ C ‖g‖_q` for every `g ∈ L^q`. -/
theorem norm_le_of_pair_le (hpq : p.HolderConjugate q) (h : LpT p) {C : ℝ}
    (hC : ∀ g : LpT q, ‖pair h g‖ ≤ C * ‖g‖) : ‖h‖ ≤ C := by
  have hC0 : 0 ≤ C := by
    have he : 0 < ‖DensityLp.toLpT q (fourier 0)‖ := norm_pos_iff.mpr (mode_ne_zero 0)
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hC _)) he
  rcases eq_or_lt_of_le (norm_nonneg h) with h0 | hpos
  · rw [← h0]
    exact hC0
  obtain ⟨g, hg1, hg2⟩ := exists_norming hpq h
  have hb := hC g
  rw [hg1, hg2, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hb
  rw [rpow_eq_mul_rpow_sub_one hpos] at hb
  exact le_of_mul_le_mul_right hb (by positivity)

/-- `N_p(ρ) ≤ N_q(ρ̄)` (pair with the norming function, then move the pencil across the pairing). -/
theorem pencilNorm_le_dual (hpq : p.HolderConjugate q) (P : RieszProjection p) (Q : RieszProjection q) (ρ : ℂ) :
    pencilNorm P ρ ≤ pencilNorm Q ((starRingEnd ℂ) ρ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (pencil Q 1 ((starRingEnd ℂ) ρ))) fun f => ?_
  refine norm_le_of_pair_le hpq _ fun g => ?_
  rw [pair_pencil hpq P Q, map_one]
  calc ‖pair f (pencil Q 1 ((starRingEnd ℂ) ρ) g)‖ ≤ ‖f‖ * ‖pencil Q 1 ((starRingEnd ℂ) ρ) g‖ :=
        norm_pair_le hpq _ _
    _ ≤ ‖f‖ * (pencilNorm Q ((starRingEnd ℂ) ρ) * ‖g‖) :=
        mul_le_mul_of_nonneg_left ((pencil Q 1 _).le_opNorm g) (norm_nonneg _)
    _ = pencilNorm Q ((starRingEnd ℂ) ρ) * ‖f‖ * ‖g‖ := by ring

end Norming

/-! ## The rows I10 and I11 -/

theorem one_lt_conjExp {p : ℝ} (hp : 1 < p) : 1 < p / (p - 1) :=
  (one_lt_div (by linarith)).mpr (by linarith)

theorem conjExp_lt_two {p : ℝ} (hp : 2 < p) : p / (p - 1) < 2 :=
  (div_lt_iff₀ (by linarith)).mpr (by linarith)

/-- The `Fact` instance for the conjugate exponent `p' = p/(p-1)`, `1 < p`. -/
theorem fact_conjExp {p : ℝ} (hp : 1 < p) : Fact (1 ≤ ENNReal.ofReal (p / (p - 1))) :=
  ⟨ENNReal.one_le_ofReal.mpr (one_lt_conjExp hp).le⟩

/-- I10, P019_paper.tex:55 (third identity): `N_p(ρ) = N_{p'}(ρ̄)`, `p' = p/(p-1)`. -/
theorem pencilNorm_dual {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal (p / (p - 1)))]
    (hp : 1 < p) (P : RieszProjection p) (Q : RieszProjection (p / (p - 1))) (ρ : ℂ) :
    pencilNorm P ρ = pencilNorm Q (star ρ) := by
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  refine le_antisymm (pencilNorm_le_dual hpq P Q ρ) ?_
  have h := pencilNorm_le_dual hpq.symm Q P ((starRingEnd ℂ) ρ)
  rwa [Complex.conj_conj] at h

/-- I11, P019_paper.tex:57: the identities reduce every case with `ρ ≠ 0`, `p ≠ 2` to a ratio of modulus at most one
and an exponent in `(1, 2)`: `N_p(ρ) = s N_q(r)` with `1 < q < 2`, `|r| ≤ 1`, `s > 0`, for an actual projection on
`L^q`. (For `p > 2`, `q = p'` and the projection on `L^{p'}` is the cited Hollenbeck-Verbitsky one.) -/
theorem pencilNorm_reduce {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p ≠ 2)
    (P : RieszProjection p) (ρ : ℂ) (hρ : ρ ≠ 0) :
    ∃ q : ℝ, ∃ hq : Fact (1 ≤ ENNReal.ofReal q), ∃ Q : @RieszProjection q hq,
      ∃ (r : ℂ) (s : ℝ), 1 < q ∧ q < 2 ∧ ‖r‖ ≤ 1 ∧ 0 < s ∧ pencilNorm P ρ = s * @pencilNorm q hq Q r := by
  -- `|ρ| ≤ 1` after `ρ ↦ 1/ρ` (I09); the conjugation of I10 keeps `|ρ|`.
  have hred : ∀ {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (Q : RieszProjection q) (σ : ℂ), σ ≠ 0 →
      ∃ (r : ℂ) (s : ℝ), ‖r‖ ≤ 1 ∧ 0 < s ∧ pencilNorm Q σ = s * pencilNorm Q r := by
    intro q _ Q σ hσ
    by_cases h1 : ‖σ‖ ≤ 1
    · exact ⟨σ, 1, h1, one_pos, (one_mul _).symm⟩
    · refine ⟨1 / σ, ‖σ‖, ?_, norm_pos_iff.mpr hσ, pencilNorm_inv Q σ hσ⟩
      rw [norm_div, norm_one]
      exact (div_le_one (norm_pos_iff.mpr hσ)).mpr (le_of_not_ge h1)
  rcases lt_or_gt_of_ne hp2 with hlt | hgt
  · obtain ⟨r, s, hr, hs, he⟩ := hred P ρ hρ
    exact ⟨p, inferInstance, P, r, s, hp, hlt, hr, hs, he⟩
  · have := fact_conjExp hp
    obtain ⟨Q, -⟩ := Cited.hv2000_riesz_norm (p / (p - 1)) (one_lt_conjExp hp)
    obtain ⟨r, s, hr, hs, he⟩ := hred Q (star ρ) (star_ne_zero.mpr hρ)
    exact ⟨p / (p - 1), inferInstance, Q, r, s, one_lt_conjExp hp, conjExp_lt_two hgt, hr, hs,
      (pencilNorm_dual hp P Q ρ).trans he⟩

end GKSharp
