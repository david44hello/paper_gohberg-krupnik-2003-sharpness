/- GKSharp/Proofs/PencilSymm.lean - the isometries `U f(t) = e^{-it} f(-t)` and `J f(t) = conj f(-t)` of `L^p(T)` and
the pencil symmetries they give: I05, I06, I08, I09, I12.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.PencilModes
import GKSharp.Proofs.Pencil
import GKSharp.Cited.HV2000

namespace GKSharp

open MeasureTheory

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

theorem measurePreserving_neg_circ : MeasurePreserving (Neg.neg : Circ → Circ) volume volume :=
  Measure.measurePreserving_neg volume

theorem fourier_neg_arg (n : ℤ) (x : Circ) : fourier n (-x) = fourier (-n) x := by
  rw [fourier_apply, smul_neg, fourier_neg', fourier_neg]

theorem norm_fourier_apply (n : ℤ) (x : Circ) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-! ## Twisted reflections `f ↦ χ · Φ(f(-·))` with `|χ| = 1` and `|Φ z| = |z|` -/

/-- The representative `x ↦ χ x · Φ (f (-x))` of a twisted reflection of `f`. -/
noncomputable def twistFun (χ : Circ → ℂ) (Φ : ℂ → ℂ) (f : LpT p) (x : Circ) : ℂ := χ x * Φ (f (-x))

section Twist

variable {χ : Circ → ℂ} {Φ : ℂ → ℂ}

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem norm_twistFun (hχ1 : ∀ x, ‖χ x‖ = 1) (hΦ1 : ∀ z, ‖Φ z‖ = ‖z‖) (f : LpT p) (x : Circ) :
    ‖twistFun χ Φ f x‖ = ‖(⇑f ∘ Neg.neg) x‖ := by
  simp [twistFun, hχ1, hΦ1]

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem aesm_twistFun (hχ : Continuous χ) (hΦ : Continuous Φ) (f : LpT p) :
    AEStronglyMeasurable (twistFun χ Φ f) volume :=
  hχ.aestronglyMeasurable.mul (hΦ.comp_aestronglyMeasurable
    ((Lp.aestronglyMeasurable f).comp_measurePreserving measurePreserving_neg_circ))

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem memLp_twistFun (hχ : Continuous χ) (hχ1 : ∀ x, ‖χ x‖ = 1) (hΦ : Continuous Φ)
    (hΦ1 : ∀ z, ‖Φ z‖ = ‖z‖) (f : LpT p) : MemLp (twistFun χ Φ f) (ENNReal.ofReal p) volume :=
  ((Lp.memLp f).comp_measurePreserving measurePreserving_neg_circ).mono (aesm_twistFun hχ hΦ f)
    (Filter.Eventually.of_forall fun x => (norm_twistFun hχ1 hΦ1 f x).le)

/-- The twisted reflection `f ↦ χ · Φ(f(-·))` on `LpT p`. -/
noncomputable def twist (hχ : Continuous χ) (hχ1 : ∀ x, ‖χ x‖ = 1) (hΦ : Continuous Φ)
    (hΦ1 : ∀ z, ‖Φ z‖ = ‖z‖) (f : LpT p) : LpT p :=
  (memLp_twistFun hχ hχ1 hΦ hΦ1 f).toLp _

variable (hχ : Continuous χ) (hχ1 : ∀ x, ‖χ x‖ = 1) (hΦ : Continuous Φ) (hΦ1 : ∀ z, ‖Φ z‖ = ‖z‖)

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem coeFn_twist (f : LpT p) : ⇑(twist hχ hχ1 hΦ hΦ1 f) =ᵐ[volume] twistFun χ Φ f :=
  MemLp.coeFn_toLp _

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem norm_twist (f : LpT p) : ‖twist hχ hχ1 hΦ hΦ1 f‖ = ‖f‖ := by
  rw [twist, Lp.norm_toLp, Lp.norm_def,
    eLpNorm_congr_norm_ae (aesm_twistFun hχ hΦ f)
      ((Lp.aestronglyMeasurable f).comp_measurePreserving measurePreserving_neg_circ)
      (Filter.Eventually.of_forall (norm_twistFun hχ1 hΦ1 f)),
    eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) measurePreserving_neg_circ]

end Twist

/-! ## `U f(t) = e^{-it} f(-t)`: frequency `n ↦ -n-1` -/

/-- P019_paper.tex:51: `U f(e^{it}) = e^{-it} f(e^{-it})`. -/
noncomputable def reflU (f : LpT p) : LpT p :=
  twist (fourier (-1)).continuous (norm_fourier_apply (-1)) continuous_id (fun _ => rfl) f

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem coeFn_reflU (f : LpT p) : ⇑(reflU f) =ᵐ[volume] fun x => fourier (-1) x * f (-x) :=
  coeFn_twist _ _ _ _ f

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem norm_reflU (f : LpT p) : ‖reflU f‖ = ‖f‖ := norm_twist _ _ _ _ f

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- `U` sends frequency `-n-1` to frequency `n`. -/
theorem coeff_reflU (f : LpT p) (n : ℤ) : fourierCoeff (⇑(reflU f)) n = fourierCoeff (⇑f) (-n - 1) := by
  rw [coeff_congr_volume (coeFn_reflU f)]
  unfold fourierCoeff
  rw [← integral_neg_eq_self]
  congr 1
  ext x
  have hn : -(-n - 1) = n + 1 := by ring
  simp only [neg_neg, fourier_neg_arg, smul_eq_mul, hn, fourier_add]
  ring

theorem reflU_reflU (f : LpT p) : reflU (reflU f) = f := by
  apply DensityLp.fourier_ext
  intro n
  rw [coeff_reflU, coeff_reflU]
  congr 1
  ring

theorem reflU_add (f g : LpT p) : reflU (f + g) = reflU f + reflU g := by
  apply DensityLp.fourier_ext
  intro n
  rw [coeff_add, coeff_reflU, coeff_reflU, coeff_reflU, coeff_add]

theorem reflU_smul (a : ℂ) (f : LpT p) : reflU (a • f) = a • reflU f := by
  apply DensityLp.fourier_ext
  intro n
  rw [coeff_smul, coeff_reflU, coeff_reflU, coeff_smul]

theorem reflU_sub (f g : LpT p) : reflU (f - g) = reflU f - reflU g := by
  apply DensityLp.fourier_ext
  intro n
  rw [coeff_sub, coeff_reflU, coeff_reflU, coeff_reflU, coeff_sub]

/-- `U (αP₊ + βP₋) = (βP₊ + αP₋) U`: `U` interchanges the two projections. -/
theorem reflU_pencil (P : RieszProjection p) (α β : ℂ) (f : LpT p) :
    reflU (pencil P α β f) = pencil P β α (reflU f) := by
  apply DensityLp.fourier_ext
  intro n
  rw [coeff_reflU, coeff_pencil, coeff_pencil, coeff_reflU]
  split_ifs <;> first | rfl | (exfalso; omega)

/-! ## `J f(t) = conj f(-t)`: coefficients are conjugated, each frequency is kept -/

/-- P019_paper.tex:52: `J f(e^{it}) = conj f(e^{-it})`. -/
noncomputable def conjRefl (f : LpT p) : LpT p :=
  twist (χ := fun _ => 1) continuous_const (fun _ => norm_one) Complex.continuous_conj Complex.norm_conj f

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem coeFn_conjRefl (f : LpT p) : ⇑(conjRefl f) =ᵐ[volume] fun x => (starRingEnd ℂ) (f (-x)) := by
  filter_upwards [coeFn_twist (χ := fun _ => 1) continuous_const (fun _ => norm_one) Complex.continuous_conj
    Complex.norm_conj f] with x hx
  exact hx.trans (one_mul _)

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem norm_conjRefl (f : LpT p) : ‖conjRefl f‖ = ‖f‖ := norm_twist _ _ _ _ f

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- `J` conjugates every Fourier coefficient. -/
theorem coeff_conjRefl (f : LpT p) (n : ℤ) :
    fourierCoeff (⇑(conjRefl f)) n = (starRingEnd ℂ) (fourierCoeff (⇑f) n) := by
  rw [coeff_congr_volume (coeFn_conjRefl f)]
  unfold fourierCoeff
  rw [← integral_neg_eq_self, ← integral_conj]
  congr 1
  ext x
  simp only [neg_neg, fourier_neg_arg, smul_eq_mul, map_mul, fourier_neg, Complex.conj_conj]

theorem conjRefl_conjRefl (f : LpT p) : conjRefl (conjRefl f) = f := by
  apply DensityLp.fourier_ext
  intro n
  rw [coeff_conjRefl, coeff_conjRefl, Complex.conj_conj]

theorem conjRefl_add (f g : LpT p) : conjRefl (f + g) = conjRefl f + conjRefl g := by
  apply DensityLp.fourier_ext
  intro n
  rw [coeff_add, coeff_conjRefl, coeff_conjRefl, coeff_conjRefl, coeff_add, map_add]

theorem conjRefl_smul (a : ℂ) (f : LpT p) : conjRefl (a • f) = (starRingEnd ℂ) a • conjRefl f := by
  apply DensityLp.fourier_ext
  intro n
  rw [coeff_smul, coeff_conjRefl, coeff_conjRefl, coeff_smul, map_mul]

theorem conjRefl_sub (f g : LpT p) : conjRefl (f - g) = conjRefl f - conjRefl g := by
  apply DensityLp.fourier_ext
  intro n
  rw [coeff_sub, coeff_conjRefl, coeff_conjRefl, coeff_conjRefl, coeff_sub, map_sub]

/-- `J (αP₊ + βP₋) = (ᾱP₊ + β̄P₋) J`. -/
theorem conjRefl_pencil (P : RieszProjection p) (α β : ℂ) (f : LpT p) :
    conjRefl (pencil P α β f) = pencil P ((starRingEnd ℂ) α) ((starRingEnd ℂ) β) (conjRefl f) := by
  apply DensityLp.fourier_ext
  intro n
  rw [coeff_conjRefl, coeff_pencil, coeff_pencil, coeff_conjRefl, map_mul]
  split_ifs <;> rfl

/-! ## Operator norms under norm-preserving intertwiners -/

/-- If a norm-preserving surjection `V` satisfies `V ∘ A = B ∘ V`, then `‖B‖ ≤ ‖A‖`. -/
theorem opNorm_le_of_intertwine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A B : E →L[ℂ] E}
    {V : E → E} (hV : ∀ x, ‖V x‖ = ‖x‖) (hsurj : Function.Surjective V) (h : ∀ x, V (A x) = B (V x)) :
    ‖B‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  rw [← h, hV, hV]
  exact A.le_opNorm x

theorem reflU_surjective : Function.Surjective (reflU (p := p)) :=
  fun f => ⟨reflU f, reflU_reflU f⟩

theorem conjRefl_surjective : Function.Surjective (conjRefl (p := p)) :=
  fun f => ⟨conjRefl f, conjRefl_conjRefl f⟩

/-- `‖αP₊ + βP₋‖ = ‖βP₊ + αP₋‖` (conjugate by `U`). -/
theorem norm_pencil_swap (P : RieszProjection p) (α β : ℂ) : ‖pencil P α β‖ = ‖pencil P β α‖ :=
  le_antisymm (opNorm_le_of_intertwine norm_reflU reflU_surjective (reflU_pencil P β α))
    (opNorm_le_of_intertwine norm_reflU reflU_surjective (reflU_pencil P α β))

/-- `‖αP₊ + βP₋‖ = ‖ᾱP₊ + β̄P₋‖` (conjugate by `J`). -/
theorem norm_pencil_conj (P : RieszProjection p) (α β : ℂ) :
    ‖pencil P α β‖ = ‖pencil P ((starRingEnd ℂ) α) ((starRingEnd ℂ) β)‖ := by
  refine le_antisymm ?_ (opNorm_le_of_intertwine norm_conjRefl conjRefl_surjective (conjRefl_pencil P α β))
  have h := opNorm_le_of_intertwine norm_conjRefl conjRefl_surjective
    (conjRefl_pencil P ((starRingEnd ℂ) α) ((starRingEnd ℂ) β))
  rwa [Complex.conj_conj, Complex.conj_conj] at h

/-! ## The rows -/

/-- I05, P019_paper.tex:51: `U f(t) = e^{-it} f(-t)` is a complex-linear involutive isometry of `L^p(T)` that
interchanges `P₊` and `P₋`. -/
theorem exists_U (P : RieszProjection p) :
    ∃ U : LpT p → LpT p, Isometry U ∧ Function.Involutive U ∧
      (∀ f g, U (f + g) = U f + U g) ∧ (∀ (a : ℂ) f, U (a • f) = a • U f) ∧
      (∀ f, ∀ᵐ x ∂(volume : Measure Circ), U f x = fourier (-1) x * f (-x)) ∧
      (∀ f, U (P.plus f) = rieszMinus P (U f)) ∧
      (∀ f, U (rieszMinus P f) = P.plus (U f)) := by
  refine ⟨reflU, Isometry.of_dist_eq fun f g => ?_, reflU_reflU, reflU_add, reflU_smul, coeFn_reflU,
    fun f => ?_, fun f => ?_⟩
  · rw [dist_eq_norm, dist_eq_norm, ← reflU_sub, norm_reflU]
  · simpa [pencil_one_zero, pencil_zero_one] using reflU_pencil P 1 0 f
  · simpa [pencil_one_zero, pencil_zero_one] using reflU_pencil P 0 1 f

/-- I06, P019_paper.tex:52: `J f(t) = conj f(-t)` is a conjugate-linear involutive isometry of `L^p(T)` that
preserves both frequency halves. -/
theorem exists_J (P : RieszProjection p) :
    ∃ J : LpT p → LpT p, Isometry J ∧ Function.Involutive J ∧
      (∀ f g, J (f + g) = J f + J g) ∧ (∀ (a : ℂ) f, J (a • f) = star a • J f) ∧
      (∀ f, ∀ᵐ x ∂(volume : Measure Circ), J f x = star (f (-x))) ∧
      (∀ f, J (P.plus f) = P.plus (J f)) ∧
      (∀ f, J (rieszMinus P f) = rieszMinus P (J f)) := by
  refine ⟨conjRefl, Isometry.of_dist_eq fun f g => ?_, conjRefl_conjRefl, conjRefl_add, conjRefl_smul,
    coeFn_conjRefl, fun f => ?_, fun f => ?_⟩
  · rw [dist_eq_norm, dist_eq_norm, ← conjRefl_sub, norm_conjRefl]
  · simpa [pencil_one_zero] using conjRefl_pencil P 1 0 f
  · simpa [pencil_zero_one] using conjRefl_pencil P 0 1 f

/-- I08, P019_paper.tex:55: `N_p(ρ) = N_p(ρ̄)`. -/
theorem pencilNorm_conj (P : RieszProjection p) (ρ : ℂ) : pencilNorm P ρ = pencilNorm P (star ρ) := by
  simpa [pencilNorm] using norm_pencil_conj P 1 ρ

/-- I09, P019_paper.tex:55: `N_p(ρ) = |ρ| N_p(1/ρ)` for `ρ ≠ 0`. -/
theorem pencilNorm_inv (P : RieszProjection p) (ρ : ℂ) (hρ : ρ ≠ 0) :
    pencilNorm P ρ = ‖ρ‖ * pencilNorm P (1 / ρ) := by
  rw [← pencil_norm_homogeneous P ρ 1 hρ, ← norm_pencil_swap]
  rfl

/-- `‖P₋‖ = ‖P₊‖` (`P₋` is isometrically conjugate to `P₊` by `U`). -/
theorem norm_rieszMinus (P : RieszProjection p) : ‖rieszMinus P‖ = ‖P.plus‖ := by
  rw [← pencil_zero_one, ← pencil_one_zero, norm_pencil_swap]

/-- I12, P019_paper.tex:58: `‖βP₋‖ = |β| / sin(π/p)` (the case `α = 0`, including `β = 0`), from the cited
Hollenbeck-Verbitsky norm of `P₊`. -/
theorem norm_pencil_zero_left_eq (hp : 1 < p) (P : RieszProjection p) (β : ℂ) :
    ‖pencil P 0 β‖ = ‖β‖ / Real.sin (Real.pi / p) := by
  obtain ⟨Q, hQ⟩ := Cited.hv2000_riesz_norm p hp
  rw [pencil_norm_zero_left, norm_rieszMinus, riesz_unique P Q, hQ, mul_one_div]

end GKSharp
