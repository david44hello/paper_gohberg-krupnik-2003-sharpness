/- GKSharp/Proofs/PencilL2.lean - the pencil at p = 2: Parseval on LpT 2 and I13 `‖αP₊ + βP₋‖₂ = max(|α|, |β|)`.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.PencilModes

namespace GKSharp

open MeasureTheory

theorem ofReal_two_eq : ENNReal.ofReal 2 = 2 := by simp

/-- `∫ g dvolume = 2π ∫ g dhaar` on the circle `ℝ/2πℤ`. -/
theorem integral_volume_eq (g : Circ → ℝ) :
    ∫ x, g x ∂(volume : Measure Circ) = 2 * Real.pi * ∫ x, g x ∂AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

variable [Fact (1 ≤ ENNReal.ofReal 2)]

omit [Fact (1 ≤ ENNReal.ofReal 2)] in
/-- `‖u‖² = 2π ∫ |u|² dhaar` for `u ∈ LpT 2`. -/
theorem norm_sq_LpT2 (u : LpT 2) :
    ‖u‖ ^ 2 = 2 * Real.pi * ∫ x, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle := by
  have h2 : (ENNReal.ofReal 2).toReal = 2 := ENNReal.toReal_ofReal (by norm_num)
  have hint : 0 ≤ ∫ x, ‖u x‖ ^ (2 : ℝ) ∂(volume : Measure Circ) :=
    integral_nonneg fun x => by positivity
  rw [Lp.norm_def, (Lp.memLp u).eLpNorm_eq_integral_rpow_norm (by simp) (by simp), h2,
    ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hint]
  norm_num
  simp_rw [← Real.rpow_natCast, Nat.cast_ofNat]
  exact integral_volume_eq _

omit [Fact (1 ≤ ENNReal.ofReal 2)] in
/-- Parseval on `LpT 2`: `Σₙ |û(n)|² = ‖u‖² / 2π`. -/
theorem hasSum_sq_coeff_LpT2 (u : LpT 2) :
    HasSum (fun n => ‖fourierCoeff (⇑u) n‖ ^ 2) (‖u‖ ^ 2 / (2 * Real.pi)) := by
  have hvol : MemLp (⇑u) 2 volume := by
    convert Lp.memLp u
    exact ofReal_two_eq.symm
  have hmem : MemLp (⇑u) 2 AddCircle.haarAddCircle := hvol.mono_measure DensityLp.haar_le_volume
  have hae := hmem.coeFn_toLp
  have hint : ∫ t, ‖(hmem.toLp ⇑u : Lp ℂ 2 AddCircle.haarAddCircle) t‖ ^ 2 ∂AddCircle.haarAddCircle =
      ∫ t, ‖u t‖ ^ 2 ∂AddCircle.haarAddCircle :=
    integral_congr_ae (hae.mono fun x hx => by simp only [hx])
  have H := hasSum_sq_fourierCoeff (hmem.toLp ⇑u)
  rw [fourierCoeff_congr_ae hae, hint] at H
  rwa [norm_sq_LpT2, mul_div_cancel_left₀ _ (by positivity)]

/-- I13, P019_paper.tex:59, upper half: `‖αP₊ + βP₋‖₂ ≤ max(|α|, |β|)` (orthogonality via Parseval). -/
theorem norm_pencil_two_le (P : RieszProjection 2) (α β : ℂ) : ‖pencil P α β‖ ≤ max ‖α‖ ‖β‖ := by
  have hM : 0 ≤ max ‖α‖ ‖β‖ := le_max_of_le_left (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun f => ?_
  have hle : ‖pencil P α β f‖ ^ 2 / (2 * Real.pi) ≤ max ‖α‖ ‖β‖ ^ 2 * (‖f‖ ^ 2 / (2 * Real.pi)) := by
    refine hasSum_le (fun n => ?_) (hasSum_sq_coeff_LpT2 _) ((hasSum_sq_coeff_LpT2 f).mul_left _)
    rw [coeff_pencil, norm_mul, mul_pow]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (sq_nonneg _)
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hsq : ‖pencil P α β f‖ ^ 2 ≤ (max ‖α‖ ‖β‖ * ‖f‖) ^ 2 := by
    rw [mul_pow]
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)] at hle
    exact hle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _)) two_ne_zero).mp hsq

omit [Fact (1 ≤ ENNReal.ofReal 2)] in
/-- I13, P019_paper.tex:59: at `p = 2`, `‖αP₊ + βP₋‖ = max(|α|, |β|)` for all complex `α, β`. -/
theorem norm_pencil_two {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : p = 2) (P : RieszProjection p) (α β : ℂ) :
    ‖pencil P α β‖ = max ‖α‖ ‖β‖ := by
  subst hp
  exact le_antisymm (norm_pencil_two_le P α β) (max_le_norm_pencil P α β)

end GKSharp
