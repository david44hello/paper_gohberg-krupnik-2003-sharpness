/- GKSharp/Proofs/Sec4Quad.lean - slice (b): quadratic error at the minimizer, cosine kink slopes (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v0.90, each as `<row>_proved` with the row's exact type.
- fixed_s_quadratic_error (B:135): `g(0, s) - Ω = ω₁(s) - ω₁(s*)` (shared row g_zero). With `u = s(1 - s)`,
  `ω₁'(s) = p u^{q-1} sQuad(s)/u^{2q}` and `sQuad(s) = (s - s*)(A(s + s*) + B)` (`sQuad(s*) = 0`), so
  `ω₁'(s) = (s - s*) R(s)` with `R` continuous on `J = [s* - ε, s* + ε] ⊂ (0, 1)`, `|R| ≤ M` there. On the segment
  from `s*` to `s`, `|ω₁'| ≤ M |s - s*|`, and the mean value inequality gives `|ω₁(s) - ω₁(s*)| ≤ M (s - s*)²`.
- cosine_kink_derivatives (A:22-23): chain rule; `sin(q(π - 2π)) = -sin(qπ)`.
-/
import GKSharp.Proofs.Sec4aOmega
import GKSharp.Proofs.StripLeaves

namespace GKSharp

open Set GKSharp.Threshold

/-- B:135, row `fixed_s_quadratic_error`. -/
theorem fixed_s_quadratic_error_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ∃ bound > 0, ∃ eps > 0, ∀ s ∈ Ioo (sStar p - eps) (sStar p + eps),
      |g p 0 s - omega p| ≤ bound * (s - sStar p) ^ 2 := by
  obtain ⟨⟨hr0, hr1⟩, hroot, -⟩ := sStar_spec_proved p hp hp2
  unfold sQuad at hroot
  obtain ⟨r, hr⟩ : ∃ r, r = sStar p := ⟨_, rfl⟩
  rw [← hr] at hr0 hr1 hroot ⊢
  obtain ⟨eps, heps⟩ : ∃ e, e = min r (1 - r) / 2 := ⟨_, rfl⟩
  have he1 := min_le_left r (1 - r)
  have he2 := min_le_right r (1 - r)
  have heps0 : 0 < eps := by rw [heps]; exact half_pos (lt_min hr0 (by linarith))
  have hJ : ∀ x ∈ Icc (r - eps) (r + eps), 0 < x ∧ x < 1 := fun x hx => by
    obtain ⟨hx1, hx2⟩ := hx
    constructor <;> linarith
  have hJu : ∀ x ∈ Icc (r - eps) (r + eps), 0 < x * (1 - x) := fun x hx =>
    mul_pos (hJ x hx).1 (by linarith [(hJ x hx).2])
  -- `ω₁' = (s - s*) R`
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, R = fun x => p * (x * (1 - x)) ^ (q p - 1) *
      ((2 * q p - 1) * (x + r) + bConst p) / ((x * (1 - x)) ^ q p) ^ 2 := ⟨_, rfl⟩
  have hD : ∀ x ∈ Icc (r - eps) (r + eps), HasDerivAt (omegaFirst p) ((x - r) * R x) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hJ x hx
    have hu := hJu x hx
    refine (sec4a_omegaFirst_hasDerivAt p hx0 hx1).congr_deriv ?_
    have he : (x * (1 - x)) ^ q p = (x * (1 - x)) ^ (q p - 1) * (x * (1 - x)) := by
      rw [Real.rpow_sub_one hu.ne', div_mul_cancel₀ _ hu.ne']
    have hsq : (2 * q p - 1) * x ^ 2 + bConst p * x - q p * aConst p =
        (x - r) * ((2 * q p - 1) * (x + r) + bConst p) := by
      linear_combination hroot
    have hnum : p * (x * (1 - x)) ^ q p - p * (aConst p + x) * ((1 - 2 * x) * q p * (x * (1 - x)) ^ (q p - 1)) =
        p * (x * (1 - x)) ^ (q p - 1) * ((x - r) * ((2 * q p - 1) * (x + r) + bConst p)) := by
      rw [← hsq, he]
      simp only [bConst]
      ring
    rw [hnum]
    simp only [hR]
    ring
  have hRc : ContinuousOn R (Icc (r - eps) (r + eps)) := by
    rw [hR]
    have hu : ContinuousOn (fun x : ℝ => x * (1 - x)) (Icc (r - eps) (r + eps)) := by fun_prop
    have hU1 := hu.rpow_const (p := q p - 1) fun x hx => Or.inl (hJu x hx).ne'
    have hU2 := hu.rpow_const (p := q p) fun x hx => Or.inl (hJu x hx).ne'
    refine ContinuousOn.div ((continuousOn_const.mul hU1).mul (by fun_prop)) (hU2.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (Real.rpow_pos_of_pos (hJu x hx) _).ne'
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hRc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM r ⟨by linarith, by linarith⟩)
  refine ⟨M + 1, by linarith, eps, heps0, fun s hs => ?_⟩
  have hsJ : s ∈ Icc (r - eps) (r + eps) := ⟨hs.1.le, hs.2.le⟩
  have hsub : uIcc r s ⊆ Icc (r - eps) (r + eps) := uIcc_subset_Icc ⟨by linarith, by linarith⟩ hsJ
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := omegaFirst p)
    (f' := fun x => (x - r) * R x) (C := |s - r| * M)
    (fun x hx => (hD x (hsub hx)).hasDerivWithinAt)
    (fun x hx => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (abs_sub_left_of_mem_uIcc hx) (hM x (hsub hx)) (norm_nonneg _) (abs_nonneg _))
    (convex_uIcc r s) left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have heq : g p 0 s - omega p = omegaFirst p s - omegaFirst p r := by
    rw [GKSharp.g_zero_proved p s hp hp2, hr]
    show omegaFirst p s - kappaZero p - (omegaFirst p (sStar p) - kappaZero p) = _
    ring
  rw [heq]
  calc |omegaFirst p s - omegaFirst p r| ≤ |s - r| * M * |s - r| := hmvt
    _ = M * (s - r) ^ 2 := by rw [mul_right_comm, abs_mul_abs_self]; ring
    _ ≤ (M + 1) * (s - r) ^ 2 := by nlinarith [sq_nonneg (s - r)]

/-- A:22-23, row `cosine_kink_derivatives`. -/
theorem cosine_kink_derivatives_proved (qq KK : ℝ) :
    HasDerivAt (fun t : ℝ => KK * Real.cos (qq * t)) (-KK * qq * Real.sin (qq * Real.pi)) Real.pi ∧
    HasDerivAt (fun t : ℝ => KK * Real.cos (qq * (t - 2 * Real.pi)))
      (KK * qq * Real.sin (qq * Real.pi)) Real.pi := by
  constructor
  · refine ((((hasDerivAt_id' Real.pi).const_mul qq).cos).const_mul KK).congr_deriv ?_
    ring
  · refine (((((hasDerivAt_id' Real.pi).sub_const (2 * Real.pi)).const_mul qq).cos).const_mul KK).congr_deriv ?_
    rw [show qq * (Real.pi - 2 * Real.pi) = -(qq * Real.pi) by ring, Real.sin_neg]
    ring

end GKSharp
