/- GKSharp/Proofs/PencilModes.lean - the projection pencil on single Fourier modes: O10, I03 (H1 = -i), the lower half
of I13, and N12.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.FourierDensity

namespace GKSharp

open MeasureTheory

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-! ## Fourier coefficients of `LpT` elements are linear -/

omit [Fact (1 ≤ ENNReal.ofReal p)] in
/-- Fourier coefficients of an `LpT` element only see its `volume`-a.e. class. -/
theorem coeff_congr_volume {u : LpT p} {g : Circ → ℂ} (h : ⇑u =ᵐ[volume] g) :
    fourierCoeff (⇑u) = fourierCoeff g :=
  fourierCoeff_congr_ae (DensityLp.ae_haar_iff.mp h)

theorem coeff_add (u v : LpT p) (n : ℤ) :
    fourierCoeff (⇑(u + v)) n = fourierCoeff (⇑u) n + fourierCoeff (⇑v) n := by
  rw [coeff_congr_volume (Lp.coeFn_add u v),
    fourierCoeff.add (DensityLp.integrable_haar_of_lp u) (DensityLp.integrable_haar_of_lp v)]
  rfl

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem coeff_smul (a : ℂ) (u : LpT p) (n : ℤ) :
    fourierCoeff (⇑(a • u)) n = a * fourierCoeff (⇑u) n := by
  rw [coeff_congr_volume (Lp.coeFn_smul a u), fourierCoeff.const_smul]
  rfl

theorem coeff_sub (u v : LpT p) (n : ℤ) :
    fourierCoeff (⇑(u - v)) n = fourierCoeff (⇑u) n - fourierCoeff (⇑v) n := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ v, coeff_add, coeff_smul]
  ring

omit [Fact (1 ≤ ENNReal.ofReal p)] in
theorem coeff_zero (n : ℤ) : fourierCoeff (⇑(0 : LpT p)) n = 0 := by
  rw [coeff_congr_volume (Lp.coeFn_zero ℂ _ _)]
  simp [fourierCoeff]

/-! ## The pencil acts on Fourier coefficients by the two-valued mask -/

/-- The complementary projection keeps exactly the negative frequencies. -/
theorem coeff_rieszMinus (P : RieszProjection p) (f : LpT p) (n : ℤ) :
    fourierCoeff (⇑(rieszMinus P f)) n = if 0 ≤ n then 0 else fourierCoeff (⇑f) n := by
  have h : rieszMinus P f = f - P.plus f := rfl
  rw [h, coeff_sub, P.coeff_plus]
  split_ifs <;> ring

/-- `αP₊ + βP₋` multiplies the `n`-th coefficient by `α` (`n ≥ 0`) or `β` (`n < 0`). -/
theorem coeff_pencil (P : RieszProjection p) (α β : ℂ) (f : LpT p) (n : ℤ) :
    fourierCoeff (⇑(pencil P α β f)) n = (if 0 ≤ n then α else β) * fourierCoeff (⇑f) n := by
  have h : pencil P α β f = α • P.plus f + β • rieszMinus P f := rfl
  rw [h, coeff_add, coeff_smul, coeff_smul, P.coeff_plus, coeff_rieszMinus]
  split_ifs <;> ring

theorem pencil_one_zero (P : RieszProjection p) : pencil P 1 0 = P.plus := by
  ext f
  simp [pencil]

theorem pencil_zero_one (P : RieszProjection p) : pencil P 0 1 = rieszMinus P := by
  ext f
  simp [pencil]

/-! ## Single modes `eₙ(t) = e^{int}` -/

/-- The Fourier coefficients of the single mode `eₙ` in `LpT p`. -/
theorem coeff_mode (n m : ℤ) :
    fourierCoeff (⇑(DensityLp.toLpT p (fourier n))) m = if m = n then 1 else 0 := by
  rw [DensityLp.coeff_toLpT, fourierCoeff_fourier, Pi.single_apply]

theorem mode_ne_zero (n : ℤ) : DensityLp.toLpT p (fourier n) ≠ 0 := by
  intro h
  have hc := coeff_mode (p := p) n n
  rw [h, coeff_zero] at hc
  simp at hc

/-- The pencil maps `eₙ` to `α eₙ` (`n ≥ 0`) or `β eₙ` (`n < 0`). -/
theorem pencil_mode (P : RieszProjection p) (α β : ℂ) (n : ℤ) :
    pencil P α β (DensityLp.toLpT p (fourier n)) =
      (if 0 ≤ n then α else β) • DensityLp.toLpT p (fourier n) := by
  apply DensityLp.fourier_ext
  intro m
  rw [coeff_pencil, coeff_smul, coeff_mode]
  by_cases hm : m = n
  · rw [hm]
  · simp [hm]

/-- Each coefficient of the pencil is at most its operator norm (test on the mode `eₙ`). -/
theorem norm_le_pencil_of_mode (P : RieszProjection p) (α β : ℂ) (n : ℤ) :
    ‖(if 0 ≤ n then α else β)‖ ≤ ‖pencil P α β‖ := by
  have he : 0 < ‖DensityLp.toLpT p (fourier n)‖ := norm_pos_iff.mpr (mode_ne_zero n)
  have h := (pencil P α β).le_opNorm (DensityLp.toLpT p (fourier n))
  rw [pencil_mode, norm_smul] at h
  exact le_of_mul_le_mul_right h he

/-- `max(|α|, |β|) ≤ ‖αP₊ + βP₋‖`, from the modes `e₀` and `e₋₁` (the lower half of I13). -/
theorem max_le_norm_pencil (P : RieszProjection p) (α β : ℂ) : max ‖α‖ ‖β‖ ≤ ‖pencil P α β‖ :=
  max_le (by simpa using norm_le_pencil_of_mode P α β 0)
    (by simpa using norm_le_pencil_of_mode P α β (-1))

/-- O10, sec2_obstacle.tex:48-49: `N_p(ρ) ≥ max(1, |ρ|)`, by single-frequency tests. -/
theorem max_one_le_pencilNorm (P : RieszProjection p) (ρ : ℂ) : max 1 ‖ρ‖ ≤ pencilNorm P ρ := by
  simpa [pencilNorm] using max_le_norm_pencil P 1 ρ

/-- `e₀` is the constant function one. -/
theorem fourier_zero_eq_one : (fourier 0 : C(Circ, ℂ)) = 1 :=
  ContinuousMap.ext fun _ => fourier_zero

/-- I03, P019_paper.tex:47: `H1 = -i` for `H = -i(P₊ - P₋)` and the constant function `1`. -/
theorem shiftedHilbert_one (P : RieszProjection p) :
    shiftedHilbert P (DensityLp.toLpT p 1) = (-Complex.I) • DensityLp.toLpT p 1 := by
  have hP : P.plus (DensityLp.toLpT p (fourier 0)) = DensityLp.toLpT p (fourier 0) := by
    simpa [pencil_one_zero] using pencil_mode P 1 0 0
  have hM : rieszMinus P (DensityLp.toLpT p (fourier 0)) = 0 := by
    simpa [pencil_zero_one] using pencil_mode P 0 1 0
  rw [← fourier_zero_eq_one]
  change (-Complex.I) • (P.plus _ - rieszMinus P _) = _
  rw [hP, hM, sub_zero]

/-- N12, norm_correspondence.tex:56: for real `a, b` with `a - ib ≠ 0`, the ratio `(a+ib)/(a-ib)` has modulus one. -/
theorem norm_ratio_of_real (a b : ℝ) (h : (a : ℂ) - Complex.I * b ≠ 0) :
    ‖((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b)‖ = 1 := by
  have hc : (a : ℂ) - Complex.I * b = (starRingEnd ℂ) ((a : ℂ) + Complex.I * b) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hn : ‖(a : ℂ) - Complex.I * b‖ ≠ 0 := norm_ne_zero_iff.mpr h
  rw [norm_div, div_eq_one_iff_eq hn, hc, Complex.norm_conj]

end GKSharp
