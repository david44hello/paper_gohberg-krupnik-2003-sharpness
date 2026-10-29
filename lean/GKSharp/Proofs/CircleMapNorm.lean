/- GKSharp/Proofs/CircleMapNorm.lean - the circle maps circleMinus/circleMid are bounded and continuous, and their
actual functionNorm (sSup of ‖S f‖/‖f‖ over f ≠ 0) bounds them pointwise. Shared groundwork for N06 and N11.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.PencilModes

namespace GKSharp.CircleMapNorm

open GKSharp MeasureTheory

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-! ## The constant-frequency part `zeroPart f = f̂(0) · 1` is a bounded rank-one map -/

theorem constantLp_eq_smul (a : ℂ) : constantLp p a = a • constantLp p 1 := by
  unfold constantLp
  rw [← map_smul]
  congr 1
  ext x
  simp

theorem norm_coeff_zero_le (f : LpT p) : ‖fourierCoeff (⇑f) 0‖ ≤ ‖f‖ := by
  have h := DensityLp.norm_coeff_sub_le f 0 0
  rwa [coeff_zero, sub_zero, sub_zero] at h

theorem continuous_coeff_zero : Continuous fun f : LpT p => fourierCoeff (⇑f) 0 :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun u v => by
    simpa [dist_eq_norm] using DensityLp.norm_coeff_sub_le u v 0).continuous

theorem zeroPart_eq (f : LpT p) : zeroPart p f = fourierCoeff (⇑f) 0 • constantLp p 1 :=
  constantLp_eq_smul _

theorem continuous_zeroPart : Continuous (zeroPart p) := by
  have h : zeroPart p = fun f : LpT p => fourierCoeff (⇑f) 0 • constantLp p 1 := funext zeroPart_eq
  rw [h]
  exact continuous_coeff_zero.smul continuous_const

theorem norm_zeroPart_le (f : LpT p) : ‖zeroPart p f‖ ≤ ‖constantLp p 1‖ * ‖f‖ := by
  rw [zeroPart_eq, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_coeff_zero_le f) (norm_nonneg _)

theorem zeroPart_zero : zeroPart p (0 : LpT p) = 0 := by
  rw [zeroPart_eq, coeff_zero, zero_smul]

/-! ## circleMinus and circleMid: zero, continuity, explicit bounds -/

theorem circleMinus_zero (P : RieszProjection p) (α β : ℂ) : circleMinus P α β 0 = 0 := by
  simp [circleMinus, zeroPart_zero]

theorem circleMid_zero (P : RieszProjection p) (α β : ℂ) : circleMid P α β 0 = 0 := by
  simp [circleMid, circleMinus_zero]

theorem continuous_circleMinus (P : RieszProjection p) (α β : ℂ) : Continuous (circleMinus P α β) :=
  (pencil P α β).continuous.add (continuous_zeroPart.const_smul (β - α))

theorem continuous_circleMid (P : RieszProjection p) (α β : ℂ) : Continuous (circleMid P α β) :=
  ((pencil P α β).continuous.add (continuous_circleMinus P α β)).const_smul (1 / 2 : ℂ)

/-- An explicit bound constant for circleMinus: `‖αP₊ + βP₋‖ + |β − α| ‖1‖`. -/
noncomputable def minusBound (P : RieszProjection p) (α β : ℂ) : ℝ :=
  ‖pencil P α β‖ + ‖β - α‖ * ‖constantLp p 1‖

theorem norm_circleMinus_le (P : RieszProjection p) (α β : ℂ) (f : LpT p) :
    ‖circleMinus P α β f‖ ≤ minusBound P α β * ‖f‖ := by
  unfold circleMinus minusBound
  calc ‖pencil P α β f + (β - α) • zeroPart p f‖
      ≤ ‖pencil P α β f‖ + ‖β - α‖ * ‖zeroPart p f‖ := by
        rw [← norm_smul]; exact norm_add_le _ _
    _ ≤ ‖pencil P α β‖ * ‖f‖ + ‖β - α‖ * (‖constantLp p 1‖ * ‖f‖) := by
        gcongr
        · exact (pencil P α β).le_opNorm f
        · exact norm_zeroPart_le f
    _ = (‖pencil P α β‖ + ‖β - α‖ * ‖constantLp p 1‖) * ‖f‖ := by ring

/-- `‖½ (u + v)‖ ≤ ½ (K₁ + K₂) ‖f‖` from `‖u‖ ≤ K₁ ‖f‖` and `‖v‖ ≤ K₂ ‖f‖`. -/
theorem norm_half_add_le {u v f : LpT p} {K₁ K₂ : ℝ} (hu : ‖u‖ ≤ K₁ * ‖f‖) (hv : ‖v‖ ≤ K₂ * ‖f‖) :
    ‖(1 / 2 : ℂ) • (u + v)‖ ≤ (K₁ + K₂) / 2 * ‖f‖ := by
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [norm_smul, hhalf]
  calc 1 / 2 * ‖u + v‖ ≤ 1 / 2 * (K₁ * ‖f‖ + K₂ * ‖f‖) := by
        gcongr; exact (norm_add_le u v).trans (add_le_add hu hv)
    _ = (K₁ + K₂) / 2 * ‖f‖ := by ring

theorem norm_circleMid_le (P : RieszProjection p) (α β : ℂ) (f : LpT p) :
    ‖circleMid P α β f‖ ≤ (‖pencil P α β‖ + minusBound P α β) / 2 * ‖f‖ :=
  norm_half_add_le ((pencil P α β).le_opNorm f) (norm_circleMinus_le P α β f)

/-! ## functionNorm: the actual sSup of the ratios, for any map `S` -/

theorem functionNorm_nonneg (S : LpT p → LpT p) : 0 ≤ functionNorm S := by
  unfold functionNorm
  refine Real.sSup_nonneg fun r hr => ?_
  obtain ⟨f, -, rfl⟩ := hr
  positivity

theorem bddAbove_ratio {S : LpT p → LpT p} {K : ℝ} (h : ∀ f, ‖S f‖ ≤ K * ‖f‖) :
    BddAbove {r : ℝ | ∃ f : LpT p, f ≠ 0 ∧ r = ‖S f‖ / ‖f‖} := by
  refine ⟨K, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  rw [div_le_iff₀ (norm_pos_iff.mpr hf)]
  exact h f

theorem functionNorm_le {S : LpT p → LpT p} {K : ℝ} (hK : 0 ≤ K) (h : ∀ f, ‖S f‖ ≤ K * ‖f‖) :
    functionNorm S ≤ K := by
  unfold functionNorm
  refine Real.sSup_le ?_ hK
  rintro r ⟨f, -, rfl⟩
  exact div_le_of_le_mul₀ (norm_nonneg _) hK (h f)

theorem norm_le_functionNorm_mul {S : LpT p → LpT p} (hS : S 0 = 0)
    (hB : BddAbove {r : ℝ | ∃ f : LpT p, f ≠ 0 ∧ r = ‖S f‖ / ‖f‖}) (f : LpT p) :
    ‖S f‖ ≤ functionNorm S * ‖f‖ := by
  by_cases hf : f = 0
  · rw [hf, hS, norm_zero, mul_zero]
  · have hle : ‖S f‖ / ‖f‖ ≤ functionNorm S := le_csSup hB ⟨f, hf, rfl⟩
    rwa [div_le_iff₀ (norm_pos_iff.mpr hf)] at hle

/-! ## The exports for N11: BddAbove and the pointwise bounds by the actual functionNorm -/

theorem bddAbove_circleMinus (P : RieszProjection p) (α β : ℂ) :
    BddAbove {r : ℝ | ∃ f : LpT p, f ≠ 0 ∧ r = ‖circleMinus P α β f‖ / ‖f‖} :=
  bddAbove_ratio (norm_circleMinus_le P α β)

theorem bddAbove_circleMid (P : RieszProjection p) (α β : ℂ) :
    BddAbove {r : ℝ | ∃ f : LpT p, f ≠ 0 ∧ r = ‖circleMid P α β f‖ / ‖f‖} :=
  bddAbove_ratio (norm_circleMid_le P α β)

theorem norm_circleMinus_le_functionNorm (P : RieszProjection p) (α β : ℂ) (u : LpT p) :
    ‖circleMinus P α β u‖ ≤ functionNorm (circleMinus P α β) * ‖u‖ :=
  norm_le_functionNorm_mul (circleMinus_zero P α β) (bddAbove_circleMinus P α β) u

theorem norm_circleMid_le_functionNorm (P : RieszProjection p) (α β : ℂ) (u : LpT p) :
    ‖circleMid P α β u‖ ≤ functionNorm (circleMid P α β) * ‖u‖ :=
  norm_le_functionNorm_mul (circleMid_zero P α β) (bddAbove_circleMid P α β) u

end GKSharp.CircleMapNorm
