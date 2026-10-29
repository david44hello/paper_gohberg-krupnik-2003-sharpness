/- GKSharp/Proofs/Sec3Geom.lean - Section 3 of paper 019 (sec3_nonreal.tex l.13-78): the window of the obstacle
(`m_C < 0` exactly on `(arg c - ψ, arg c + ψ)`), the radial limits, the two tangent points from `0` at arch distance
`2π/p`, the first-order term at them (Step 3), "only a real ratio balances" (Step 4), the real-ratio Remark, and
Theorem A. Rows (types verbatim from PROPOSAL_slice_c_019.lean v0.21): sec3_window, sec3_radial_limits, thmA_step1..4,
thmA_remark_real PROVED; sec3_arch from the chord-lemma row slice_O30; eq_3_2 from Theorem R (slice_O18) and sec3_arch;
thm_A from eq_3_2 (`_given`: the leading arguments are those rows' exact types).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.Window
import GKSharp.Proofs.Gamma
import GKSharp.Proofs.ObstacleMinimum
import GKSharp.Defs.Pencil

namespace GKSharp.Sec3Geom

open GKSharp

/-! ### The ray `r e^{it}` and the disk -/

theorem unitPoint_re (t : ℝ) : (unitPoint t).re = Real.cos t := by
  simp [unitPoint, Complex.exp_ofReal_mul_I_re]

theorem unitPoint_im (t : ℝ) : (unitPoint t).im = Real.sin t := by
  simp [unitPoint, Complex.exp_ofReal_mul_I_im]

/-- `|r e^{it} - z|² = r² - 2r(z₁ cos t + z₂ sin t) + |z|²`. -/
theorem normSq_ray_sub (r t : ℝ) (z : ℂ) :
    ‖(r : ℂ) * unitPoint t - z‖ ^ 2 = r ^ 2 - 2 * r * (z.re * Real.cos t + z.im * Real.sin t) + ‖z‖ ^ 2 := by
  rw [norm_sq_eq, norm_sq_eq z]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    unitPoint_re, unitPoint_im, zero_mul, sub_zero, add_zero]
  linear_combination r ^ 2 * Real.sin_sq_add_cos_sq t

/-- `z₁ cos t + z₂ sin t = |z| cos(t - arg z)`. -/
theorem re_cos_add_im_sin (z : ℂ) (t : ℝ) :
    z.re * Real.cos t + z.im * Real.sin t = ‖z‖ * Real.cos (t - Complex.arg z) := by
  rw [Real.cos_sub, ← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z]
  ring

/-- `|r e^{it} - c|² = r² - 2r|c| cos(t - arg c) + |c|²`. -/
theorem normSq_ray_sub' (r t : ℝ) (z : ℂ) :
    ‖(r : ℂ) * unitPoint t - z‖ ^ 2 = r ^ 2 - 2 * r * (‖z‖ * Real.cos (t - Complex.arg z)) + ‖z‖ ^ 2 := by
  rw [normSq_ray_sub, re_cos_add_im_sin]

/-! ### The standing data: `C > max(1, |ρ|)`, `ρ ≠ 1` -/

section Data

variable {C : ℝ} {ρ : ℂ}

theorem one_lt (hC : max 1 ‖ρ‖ < C) : 1 < C := lt_of_le_of_lt (le_max_left _ _) hC

theorem radius_pos (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) : 0 < diskRadiusSq C ρ :=
  lt_of_le_of_lt (sq_nonneg _) ((disk_of_obstacle one_pos ρ hC).2.2.1 hρ)

theorem radius_lt (hC : max 1 ‖ρ‖ < C) : diskRadiusSq C ρ < ‖diskCentre C ρ‖ ^ 2 :=
  (disk_of_obstacle one_pos ρ hC).2.2.2

theorem centre_pos (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) : 0 < ‖diskCentre C ρ‖ := by
  have h := (radius_pos hρ hC).trans (radius_lt hC)
  exact lt_of_le_of_ne (norm_nonneg _) fun e => by rw [← e] at h; norm_num at h

/-- The common modulus `r = (|c|² - R²)^{1/2}` of the two tangent points (sec3 l.47). -/
noncomputable def tangentRadius (C : ℝ) (ρ : ℂ) : ℝ := Real.sqrt (‖diskCentre C ρ‖ ^ 2 - diskRadiusSq C ρ)

theorem tangentRadius_pos (hC : max 1 ‖ρ‖ < C) : 0 < tangentRadius C ρ :=
  Real.sqrt_pos.2 (sub_pos.2 (radius_lt hC))

theorem tangentRadius_sq (hC : max 1 ‖ρ‖ < C) :
    tangentRadius C ρ ^ 2 = ‖diskCentre C ρ‖ ^ 2 - diskRadiusSq C ρ :=
  Real.sq_sqrt (sub_pos.2 (radius_lt hC)).le

theorem sin_window (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    Real.sin (windowHalfAngle C ρ) = Real.sqrt (diskRadiusSq C ρ) / ‖diskCentre C ρ‖ := by
  have hc := centre_pos hρ hC
  have hs0 : 0 ≤ Real.sqrt (diskRadiusSq C ρ) / ‖diskCentre C ρ‖ := div_nonneg (Real.sqrt_nonneg _) hc.le
  have hs1 : Real.sqrt (diskRadiusSq C ρ) / ‖diskCentre C ρ‖ ≤ 1 := by
    rw [div_le_one hc, ← Real.sqrt_sq hc.le]
    exact Real.sqrt_le_sqrt (radius_lt hC).le
  exact Real.sin_arcsin (by linarith) hs1

/-- `cos ψ = r/|c|`. -/
theorem cos_window (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    Real.cos (windowHalfAngle C ρ) = tangentRadius C ρ / ‖diskCentre C ρ‖ := by
  have hc := centre_pos hρ hC
  have hpos := (window_cos_sq hρ hC).1
  have hlt := (window_cos_sq hρ hC).2.1
  have hcos : 0 < Real.cos (windowHalfAngle C ρ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩
  have hsq : Real.cos (windowHalfAngle C ρ) ^ 2 = (tangentRadius C ρ / ‖diskCentre C ρ‖) ^ 2 := by
    have h1 := Real.sin_sq_add_cos_sq (windowHalfAngle C ρ)
    rw [sin_window hρ hC, div_pow, Real.sq_sqrt (radius_pos hρ hC).le] at h1
    rw [div_pow, tangentRadius_sq hC, sub_div, div_self (pow_ne_zero 2 hc.ne')]
    linarith
  exact (pow_left_inj₀ hcos.le (div_nonneg (tangentRadius_pos hC).le hc.le) two_ne_zero).1 hsq

/-- `|c| cos ψ = r`. -/
theorem centre_mul_cos (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    ‖diskCentre C ρ‖ * Real.cos (windowHalfAngle C ρ) = tangentRadius C ρ := by
  rw [cos_window hρ hC]
  field_simp [(centre_pos hρ hC).ne']

/-- `|c| sin ψ = R`. -/
theorem centre_mul_sin (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    ‖diskCentre C ρ‖ * Real.sin (windowHalfAngle C ρ) = Real.sqrt (diskRadiusSq C ρ) := by
  rw [sin_window hρ hC]
  field_simp [(centre_pos hρ hC).ne']

/-! ### Which rays meet the disk -/

/-- A ray meets the open disk `|ζ - c| < R` iff its direction is inside the window: `cos ψ < cos(t - arg c)`. -/
theorem exists_ray_in_disk_iff (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) (t : ℝ) :
    (∃ r : ℝ, 0 < r ∧ ‖(r : ℂ) * unitPoint t - diskCentre C ρ‖ ^ 2 < diskRadiusSq C ρ) ↔
      Real.cos (windowHalfAngle C ρ) < Real.cos (t - Complex.arg (diskCentre C ρ)) := by
  have hc := centre_pos hρ hC
  have hRc := radius_lt hC
  have hr0 := tangentRadius_pos hC
  have hr2 := tangentRadius_sq hC
  have hcm := centre_mul_cos hρ hC
  have hψ := window_cos_sq hρ hC
  have hcos0 : 0 < Real.cos (windowHalfAngle C ρ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hψ.1], hψ.2.1⟩
  simp only [normSq_ray_sub']
  constructor
  · rintro ⟨r, hr, hlt⟩
    by_contra hn
    have hn' := not_lt.1 hn
    have hcd : ‖diskCentre C ρ‖ * Real.cos (t - Complex.arg (diskCentre C ρ)) ≤ tangentRadius C ρ := by
      rw [← hcm]; exact mul_le_mul_of_nonneg_left hn' hc.le
    by_cases hd0 : Real.cos (t - Complex.arg (diskCentre C ρ)) ≤ 0
    · nlinarith [mul_nonneg hr.le (mul_nonneg hc.le (neg_nonneg.2 hd0))]
    · have hd0 := lt_of_not_ge hd0
      nlinarith [sq_nonneg (r - ‖diskCentre C ρ‖ * Real.cos (t - Complex.arg (diskCentre C ρ))),
        mul_le_mul hcd hcd (mul_pos hc hd0).le hr0.le]
  · intro hlt
    have hcd : tangentRadius C ρ < ‖diskCentre C ρ‖ * Real.cos (t - Complex.arg (diskCentre C ρ)) := by
      rw [← hcm]; exact mul_lt_mul_of_pos_left hlt hc
    refine ⟨_, hr0.trans hcd, ?_⟩
    nlinarith [mul_lt_mul hcd hcd.le hr0 (hr0.trans hcd).le]

/-- Outside the open window, the whole ray stays outside the open disk. -/
theorem ray_outside (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) {t : ℝ}
    (ht : Real.cos (t - Complex.arg (diskCentre C ρ)) ≤ Real.cos (windowHalfAngle C ρ)) (r : ℝ) (hr : 0 < r) :
    diskRadiusSq C ρ ≤ ‖(r : ℂ) * unitPoint t - diskCentre C ρ‖ ^ 2 := by
  by_contra hn
  exact absurd ((exists_ray_in_disk_iff hρ hC t).1 ⟨r, hr, not_le.1 hn⟩) (not_lt.2 ht)

/-- On the edge of the window, the tangent point `r e^{it}` lies on the circle `|ζ - c| = R`. -/
theorem tangent_on_circle (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) {t : ℝ}
    (ht : Real.cos (t - Complex.arg (diskCentre C ρ)) = Real.cos (windowHalfAngle C ρ)) :
    ‖(tangentRadius C ρ : ℂ) * unitPoint t - diskCentre C ρ‖ ^ 2 = diskRadiusSq C ρ := by
  rw [normSq_ray_sub', ht, centre_mul_cos hρ hC]
  linear_combination -(tangentRadius_sq hC)

end Data

/-! ### `G_C` on and off the disk -/

section Obstacle

variable {p C : ℝ} {ρ : ℂ}

theorem G_neg_iff (hp : 0 < p) (hC : max 1 ‖ρ‖ < C) (ζ : ℂ) :
    obstacleG p C ρ ζ < 0 ↔ ‖ζ - diskCentre C ρ‖ ^ 2 < diskRadiusSq C ρ :=
  ((disk_of_obstacle hp ρ hC).1 ζ).trans ((disk_of_obstacle hp ρ hC).2.1 ζ)

theorem G_nonneg_iff (hp : 0 < p) (hC : max 1 ‖ρ‖ < C) (ζ : ℂ) :
    0 ≤ obstacleG p C ρ ζ ↔ diskRadiusSq C ρ ≤ ‖ζ - diskCentre C ρ‖ ^ 2 := by
  rw [← not_lt, G_neg_iff hp hC, not_lt]

/-- On the circle `|ζ - c| = R`: `|ζ + ρ| = C|ζ + 1|`. -/
theorem norm_add_rho_of_circle (hC : max 1 ‖ρ‖ < C) {ζ : ℂ}
    (h : ‖ζ - diskCentre C ρ‖ ^ 2 = diskRadiusSq C ρ) : ‖ζ + ρ‖ = C * ‖ζ + 1‖ := by
  have hid := disk_identity (one_lt hC) ρ ζ
  rw [h, sub_self, mul_zero] at hid
  have hC0 : 0 ≤ C := (zero_lt_one.trans (one_lt hC)).le
  have hsq : ‖ζ + ρ‖ ^ 2 = (C * ‖ζ + 1‖) ^ 2 := by linear_combination -hid
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _)) two_ne_zero).1 hsq

theorem G_eq_zero_of_circle (hC : max 1 ‖ρ‖ < C) {ζ : ℂ}
    (h : ‖ζ - diskCentre C ρ‖ ^ 2 = diskRadiusSq C ρ) : obstacleG p C ρ ζ = 0 := by
  have hC0 : 0 ≤ C := (zero_lt_one.trans (one_lt hC)).le
  unfold obstacleG
  rw [add_comm ρ ζ, norm_add_rho_of_circle hC h, Real.mul_rpow hC0 (norm_nonneg _), add_comm ζ 1, sub_self]

/-- `m_C(t) ≤ r^{-q} G_C(r e^{it})` for every `r > 0`. -/
theorem obstacle_le (hp : 1 < p) (hC : max 1 ‖ρ‖ < C) (t r : ℝ) (hr : 0 < r) :
    obstacle p C ρ t ≤ r ^ (-(p / 2)) * obstacleG p C ρ ((r : ℂ) * unitPoint t) := by
  have hb := (slice_O12_proved hp C ρ hC).2.1 t
  have h : obstacle p C ρ t ≤ gamma p C ρ (Real.log r) t := csInf_le hb (Set.mem_range_self _)
  rw [gamma_radial, Real.exp_log hr] at h
  exact h

/-- `m_C(t) < 0` iff `G_C(r e^{it}) < 0` for some `r > 0` (sec3 l.21-22, first half). -/
theorem obstacle_neg_iff (hp : 1 < p) (hC : max 1 ‖ρ‖ < C) (t : ℝ) :
    obstacle p C ρ t < 0 ↔ ∃ r : ℝ, 0 < r ∧ obstacleG p C ρ ((r : ℂ) * unitPoint t) < 0 := by
  constructor
  · intro h
    have h' : sInf (Set.range fun y : ℝ => gamma p C ρ y t) < 0 := h
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := exists_lt_of_csInf_lt (Set.range_nonempty _) h'
    have hy' : gamma p C ρ y t < 0 := hy
    refine ⟨Real.exp y, Real.exp_pos y, ?_⟩
    rw [gamma_radial] at hy'
    by_contra hG
    exact absurd hy' (not_lt.2 (mul_nonneg (Real.rpow_nonneg (Real.exp_pos y).le _) (not_lt.1 hG)))
  · rintro ⟨r, hr, hG⟩
    exact lt_of_le_of_lt (obstacle_le hp hC t r hr)
      (mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hr _) hG)

/-- On the edge of the window, `m_C(t) = 0`, attained at the tangent radius (sec3 l.22-23). -/
theorem obstacle_eq_zero_of_edge (hp : 1 < p) (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) {t : ℝ}
    (ht : Real.cos (t - Complex.arg (diskCentre C ρ)) = Real.cos (windowHalfAngle C ρ)) :
    obstacle p C ρ t = 0 ∧ obstacleG p C ρ ((tangentRadius C ρ : ℂ) * unitPoint t) = 0 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hG := G_eq_zero_of_circle (p := p) hC (tangent_on_circle hρ hC ht)
  refine ⟨le_antisymm ?_ ?_, hG⟩
  · have h := obstacle_le hp hC t _ (tangentRadius_pos hC)
    rwa [hG, mul_zero] at h
  · show 0 ≤ sInf (Set.range fun y : ℝ => gamma p C ρ y t)
    refine le_csInf (Set.range_nonempty _) ?_
    rintro _ ⟨y, rfl⟩
    show 0 ≤ gamma p C ρ y t
    rw [gamma_radial]
    exact mul_nonneg (Real.rpow_nonneg (Real.exp_pos y).le _)
      ((G_nonneg_iff hp0 hC _).2 (ray_outside hρ hC ht.le _ (Real.exp_pos y)))

/-- The window: `m_C(t) < 0` iff `cos ψ < cos(t - arg c)` (sec3 l.21-24). -/
theorem obstacle_neg_iff_window (hp : 1 < p) (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) (t : ℝ) :
    obstacle p C ρ t < 0 ↔ Real.cos (windowHalfAngle C ρ) < Real.cos (t - Complex.arg (diskCentre C ρ)) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  rw [obstacle_neg_iff hp hC, ← exists_ray_in_disk_iff hρ hC]
  simp only [G_neg_iff hp0 hC]

end Obstacle


/-! ### Step 3: the first-order term at the tangent points -/

section Deriv

variable {p C : ℝ} {ρ : ℂ}

theorem norm_rpow_eq_sq (z : ℂ) (p : ℝ) : ‖z‖ ^ p = (‖z‖ ^ 2) ^ (p / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
  congr 1
  push_cast
  ring

/-- `A(t) = |1 + re^{it}|² = 1 + 2r cos t + r²`. -/
noncomputable def sqA (r t : ℝ) : ℝ := 1 + 2 * r * Real.cos t + r ^ 2

/-- `B(t) = |ρ + re^{it}|² = |ρ|² + 2r(ρ₁ cos t + ρ₂ sin t) + r²`. -/
noncomputable def sqB (ρ : ℂ) (r t : ℝ) : ℝ := ‖ρ‖ ^ 2 + 2 * r * (ρ.re * Real.cos t + ρ.im * Real.sin t) + r ^ 2

theorem normSq_one_add_ray (r t : ℝ) : ‖1 + (r : ℂ) * unitPoint t‖ ^ 2 = sqA r t := by
  unfold sqA
  rw [norm_sq_eq]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, unitPoint_re, unitPoint_im, zero_mul, sub_zero, add_zero, zero_add]
  linear_combination r ^ 2 * Real.sin_sq_add_cos_sq t

theorem normSq_rho_add_ray (ρ : ℂ) (r t : ℝ) : ‖ρ + (r : ℂ) * unitPoint t‖ ^ 2 = sqB ρ r t := by
  unfold sqB
  rw [norm_sq_eq, norm_sq_eq ρ]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    unitPoint_re, unitPoint_im, zero_mul, sub_zero, add_zero]
  linear_combination r ^ 2 * Real.sin_sq_add_cos_sq t

theorem G_ray_eq (p C : ℝ) (ρ : ℂ) (r : ℝ) :
    (fun s : ℝ => obstacleG p C ρ ((r : ℂ) * unitPoint s)) =
      fun s => C ^ p * sqA r s ^ (p / 2) - sqB ρ r s ^ (p / 2) := by
  funext s
  unfold obstacleG
  rw [norm_rpow_eq_sq, norm_rpow_eq_sq (ρ + _), normSq_one_add_ray, normSq_rho_add_ray]

theorem hasDerivAt_sqA (r t : ℝ) : HasDerivAt (fun s => sqA r s) (-2 * r * Real.sin t) t := by
  have h : HasDerivAt (fun s => 1 + 2 * r * Real.cos s + r ^ 2) (2 * r * -Real.sin t) t :=
    (((Real.hasDerivAt_cos t).const_mul (2 * r)).const_add 1).add_const (r ^ 2)
  unfold sqA
  convert h using 1
  ring

theorem hasDerivAt_sqB (ρ : ℂ) (r t : ℝ) :
    HasDerivAt (fun s => sqB ρ r s) (2 * r * (ρ.im * Real.cos t - ρ.re * Real.sin t)) t := by
  have h : HasDerivAt (fun s => ‖ρ‖ ^ 2 + 2 * r * (ρ.re * Real.cos s + ρ.im * Real.sin s) + r ^ 2)
      (2 * r * (ρ.re * -Real.sin t + ρ.im * Real.cos t)) t :=
    (((((Real.hasDerivAt_cos t).const_mul ρ.re).add ((Real.hasDerivAt_sin t).const_mul ρ.im)).const_mul
      (2 * r)).const_add (‖ρ‖ ^ 2)).add_const (r ^ 2)
  unfold sqB
  convert h using 1
  ring

/-- The derivative of `t ↦ G_C(r e^{it})` where both `|1 + re^{it}|` and `|ρ + re^{it}|` are nonzero. -/
theorem hasDerivAt_G_ray (C : ℝ) (ρ : ℂ) (r t : ℝ) (hA : 0 < sqA r t) (hB : 0 < sqB ρ r t) :
    HasDerivAt (fun s : ℝ => obstacleG p C ρ ((r : ℂ) * unitPoint s))
      (C ^ p * (-2 * r * Real.sin t * (p / 2) * sqA r t ^ (p / 2 - 1)) -
        2 * r * (ρ.im * Real.cos t - ρ.re * Real.sin t) * (p / 2) * sqB ρ r t ^ (p / 2 - 1)) t := by
  rw [G_ray_eq]
  exact (((hasDerivAt_sqA r t).rpow_const (Or.inl hA.ne')).const_mul (C ^ p)).sub
    ((hasDerivAt_sqB ρ r t).rpow_const (Or.inl hB.ne'))

/-- `C²A' - B' = 2r(C² - 1)|c| sin(t - arg c)`. -/
theorem combo_eq (hC : 1 < C) (ρ : ℂ) (r t : ℝ) :
    C ^ 2 * (-2 * r * Real.sin t) - 2 * r * (ρ.im * Real.cos t - ρ.re * Real.sin t) =
      2 * r * (C ^ 2 - 1) * (‖diskCentre C ρ‖ * Real.sin (t - Complex.arg (diskCentre C ρ))) := by
  obtain ⟨hre, him⟩ := diskCentre_coords hC ρ
  have hcos := Complex.norm_mul_cos_arg (diskCentre C ρ)
  have hsin := Complex.norm_mul_sin_arg (diskCentre C ρ)
  rw [Real.sin_sub]
  linear_combination (-2 * r * Real.sin t) * hre + (2 * r * Real.cos t) * him +
    (-2 * r * (C ^ 2 - 1) * Real.sin t) * hcos + (2 * r * (C ^ 2 - 1) * Real.cos t) * hsin

/-- `R(C² - 1) = C|1 - ρ|`. -/
theorem sqrt_radius_mul (hC : 1 < C) (ρ : ℂ) :
    Real.sqrt (diskRadiusSq C ρ) * (C ^ 2 - 1) = C * ‖1 - ρ‖ := by
  obtain ⟨hre, him⟩ := diskCentre_coords hC ρ
  have hX : 0 < C ^ 2 - 1 := by nlinarith
  have hd : (C ^ 2 - 1) * ((C ^ 2 - ‖ρ‖ ^ 2) / (C ^ 2 - 1)) = C ^ 2 - ‖ρ‖ ^ 2 := mul_div_cancel₀ _ hX.ne'
  have hsq : diskRadiusSq C ρ = (C * ‖1 - ρ‖ / (C ^ 2 - 1)) ^ 2 := by
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hX.ne'), mul_pow]
    have hρ := norm_sq_eq ρ
    unfold diskRadiusSq
    rw [norm_sq_eq (diskCentre C ρ), norm_sq_eq (1 - ρ)]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    linear_combination ((diskCentre C ρ).re * (C ^ 2 - 1) - (C ^ 2 - ρ.re)) * hre +
      ((diskCentre C ρ).im * (C ^ 2 - 1) + ρ.im) * him - (C ^ 2 - 1) * hd + (C ^ 2 - 1) * hρ
  rw [hsq, Real.sqrt_sq (div_nonneg (mul_nonneg (by linarith) (norm_nonneg _)) hX.le), div_mul_cancel₀ _ hX.ne']

end Deriv


/-! ### The tangent points `ζ₁, ζ₂` -/

section Tangent

variable {p C : ℝ} {ρ : ℂ}

/-- At a tangent point: `A > 0` (it is not `-1`) and `B = C²A` (`|ζ + ρ| = C|ζ + 1|`). -/
theorem tangent_sq (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) {t : ℝ}
    (ht : Real.cos (t - Complex.arg (diskCentre C ρ)) = Real.cos (windowHalfAngle C ρ)) :
    0 < sqA (tangentRadius C ρ) t ∧ sqB ρ (tangentRadius C ρ) t = C ^ 2 * sqA (tangentRadius C ρ) t := by
  have hcirc := tangent_on_circle hρ hC ht
  have hnorm := norm_add_rho_of_circle hC hcirc
  rw [← normSq_one_add_ray, ← normSq_rho_add_ray]
  refine ⟨pow_pos (norm_pos_iff.2 fun h0 => ?_) 2, ?_⟩
  · have hz : (tangentRadius C ρ : ℂ) * unitPoint t = -1 := by linear_combination h0
    have hin := (disk_of_obstacle one_pos ρ hC).2.2.1 hρ
    rw [← hz] at hin
    linarith
  · rw [add_comm ρ, hnorm, mul_pow, add_comm _ (1 : ℂ)]

theorem rpow_sq_sub_one (hC0 : 0 < C) (p : ℝ) : (C ^ 2) ^ (p / 2 - 1) = C ^ (p - 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hC0.le]
  congr 1
  push_cast
  ring

theorem rpow_split_two (hC0 : 0 < C) (p : ℝ) : C ^ p = C ^ 2 * C ^ (p - 2) := by
  conv_lhs => rw [show p = 2 + (p - 2) by ring]
  rw [Real.rpow_add hC0, Real.rpow_two]

theorem rpow_split_one (hC0 : 0 < C) (p : ℝ) : C ^ (p - 1) = C ^ (p - 2) * C := by
  conv_lhs => rw [show p - 1 = (p - 2) + 1 by ring]
  rw [Real.rpow_add hC0, Real.rpow_one]

/-- Step 3 at a point of the window's edge: the derivative of `μ(t) = G_C(re^{it})/r^q` (r the tangent radius) is
`p|1 - ρ| r^{1-q} C^{p-1} |ζ + 1|^{p-2}` times `|c| sin(t - arg c)/R`, which is `∓1` at `arg c ∓ ψ`. -/
theorem hasDerivAt_edge (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) {t : ℝ}
    (ht : Real.cos (t - Complex.arg (diskCentre C ρ)) = Real.cos (windowHalfAngle C ρ)) :
    HasDerivAt (fun s : ℝ => obstacleG p C ρ ((tangentRadius C ρ : ℂ) * unitPoint s) / tangentRadius C ρ ^ (p / 2))
      (p * ‖1 - ρ‖ * tangentRadius C ρ ^ (1 - p / 2) * C ^ (p - 1) *
        ‖(tangentRadius C ρ : ℂ) * unitPoint t + 1‖ ^ (p - 2) *
        (‖diskCentre C ρ‖ * Real.sin (t - Complex.arg (diskCentre C ρ)) / Real.sqrt (diskRadiusSq C ρ))) t := by
  obtain ⟨hA, hB⟩ := tangent_sq hρ hC ht
  have hC1 := one_lt hC
  have hC0 : 0 < C := by linarith
  have hr := tangentRadius_pos hC
  have hR := Real.sqrt_pos.2 (radius_pos hρ hC)
  have hrq : 0 < tangentRadius C ρ ^ (p / 2) := Real.rpow_pos_of_pos hr _
  have hd := (hasDerivAt_G_ray (p := p) C ρ (tangentRadius C ρ) t hA
    (by rw [hB]; exact mul_pos (by positivity) hA)).div_const (tangentRadius C ρ ^ (p / 2))
  convert hd using 1
  have hR' := hR.ne'
  have hrq' := hrq.ne'
  have hC0' := hC0.ne'
  have e4 : ‖(tangentRadius C ρ : ℂ) * unitPoint t + 1‖ ^ (p - 2) = sqA (tangentRadius C ρ) t ^ (p / 2 - 1) := by
    rw [norm_rpow_eq_sq, add_comm _ (1 : ℂ), normSq_one_add_ray]
    congr 1
    ring
  have e5 : tangentRadius C ρ ^ (1 - p / 2) = tangentRadius C ρ / tangentRadius C ρ ^ (p / 2) := by
    rw [Real.rpow_sub hr, Real.rpow_one]
  have e6 : ‖1 - ρ‖ = Real.sqrt (diskRadiusSq C ρ) * (C ^ 2 - 1) / C := by
    rw [sqrt_radius_mul hC1 ρ, mul_div_cancel_left₀ _ hC0.ne']
  have hD : C ^ 2 * C ^ (p - 2) * (-2 * tangentRadius C ρ * Real.sin t * (p / 2) * sqA (tangentRadius C ρ) t ^
        (p / 2 - 1)) - 2 * tangentRadius C ρ * (ρ.im * Real.cos t - ρ.re * Real.sin t) * (p / 2) *
        (C ^ (p - 2) * sqA (tangentRadius C ρ) t ^ (p / 2 - 1)) =
      (p / 2) * C ^ (p - 2) * sqA (tangentRadius C ρ) t ^ (p / 2 - 1) *
        (C ^ 2 * (-2 * tangentRadius C ρ * Real.sin t) -
          2 * tangentRadius C ρ * (ρ.im * Real.cos t - ρ.re * Real.sin t)) := by ring
  rw [hB, Real.mul_rpow (sq_nonneg C) hA.le, rpow_sq_sub_one hC0, rpow_split_two hC0 p, hD, combo_eq hC1,
    rpow_split_one hC0, e4, e5, e6]
  field_simp

end Tangent

/-! ### Step 4: only a real ratio balances -/

section Step4

variable {C : ℝ} {ρ : ℂ}

/-- `|ζ₁ + 1| = |ζ₂ + 1|` iff `ρ ∈ ℝ`, for the tangent points `ζ_{1,2} = r e^{i(arg c ∓ ψ)}` (sec3 l.69-71). -/
theorem tangent_norm_eq_iff (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    ‖(tangentRadius C ρ : ℂ) * unitPoint (Complex.arg (diskCentre C ρ) - windowHalfAngle C ρ) + 1‖ =
        ‖(tangentRadius C ρ : ℂ) * unitPoint (Complex.arg (diskCentre C ρ) + windowHalfAngle C ρ) + 1‖ ↔
      ρ.im = 0 := by
  have hr := tangentRadius_pos hC
  have hψ := window_cos_sq hρ hC
  have hsψ : 0 < Real.sin (windowHalfAngle C ρ) :=
    Real.sin_pos_of_pos_of_lt_pi hψ.1 (by linarith [Real.pi_pos, hψ.2.1])
  have hc := centre_pos hρ hC
  obtain ⟨-, him⟩ := diskCentre_coords (one_lt hC) ρ
  have hX : C ^ 2 - 1 ≠ 0 := by nlinarith [one_lt hC]
  have hsin := Complex.norm_mul_sin_arg (diskCentre C ρ)
  rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, add_comm _ (1 : ℂ), add_comm _ (1 : ℂ),
    normSq_one_add_ray, normSq_one_add_ray]
  unfold sqA
  rw [Real.cos_sub, Real.cos_add]
  constructor
  · intro h
    have h1 : tangentRadius C ρ * Real.sin (windowHalfAngle C ρ) *
        Real.sin (Complex.arg (diskCentre C ρ)) = 0 := by linarith
    have h2 : Real.sin (Complex.arg (diskCentre C ρ)) = 0 :=
      (mul_eq_zero.1 h1).resolve_left (mul_ne_zero hr.ne' hsψ.ne')
    rw [h2, mul_zero] at hsin
    rw [← hsin, zero_mul] at him
    exact him.symm
  · intro h
    have him0 : (diskCentre C ρ).im = 0 := by
      rw [h] at him
      exact (mul_eq_zero.1 him).resolve_right hX
    have h2 : Real.sin (Complex.arg (diskCentre C ρ)) = 0 := by
      rw [him0] at hsin
      exact (mul_eq_zero.1 hsin).resolve_left hc.ne'
    rw [h2]
    ring

end Step4

/-! ### Step 1: the contact pair is at arch distance `2π/p` -/

section Step1

variable {p : ℝ} {ρ : ℂ}

theorem max_conj_of_gt (hp : 2 < p) : max p (p / (p - 1)) = p := by
  apply max_eq_left
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem max_conj_of_lt (hp : 1 < p) (hp2 : p < 2) : max p (p / (p - 1)) = p / (p - 1) := by
  apply max_eq_right
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- With `C = GK_p(ρ)`, the tangent directions `arg c ∓ ψ` differ by `2π/p` modulo `2π` (sec3 l.47-50). -/
theorem tangent_arch (hp : 1 < p) (hp2 : p ≠ 2) (hρ : ρ ≠ 1) :
    (Complex.arg (diskCentre (gk p ρ) ρ) + windowHalfAngle (gk p ρ) ρ =
        (Complex.arg (diskCentre (gk p ρ) ρ) - windowHalfAngle (gk p ρ) ρ) + 2 * Real.pi / p) ∨
      (Complex.arg (diskCentre (gk p ρ) ρ) - windowHalfAngle (gk p ρ) ρ =
        (Complex.arg (diskCentre (gk p ρ) ρ) + windowHalfAngle (gk p ρ) ρ) + 2 * Real.pi / p - 2 * Real.pi) := by
  have hW := (lemma_W hp hp2 hρ (gk_gt_max hp hp2 hρ)).2 rfl
  have hp0 : 0 < p := by linarith
  rcases lt_or_gt_of_ne hp2 with hlt | hgt
  · right
    rw [max_conj_of_lt hp hlt] at hW
    have hp1 : p - 1 ≠ 0 := by linarith
    have hp0' := hp0.ne'
    have e : 2 * Real.pi / (p / (p - 1)) = 2 * Real.pi - 2 * Real.pi / p := by
      field_simp
    linarith
  · left
    rw [max_conj_of_gt hgt] at hW
    linarith

end Step1


/-! ### The frozen-radius function `μ(t) = G_C(re^{it})/r^q` at the contact pair -/

section Contact

variable {p C : ℝ} {ρ : ℂ}

theorem tangentRadius_eq (C : ℝ) (ρ : ℂ) :
    Real.sqrt (‖diskCentre C ρ‖ ^ 2 - diskRadiusSq C ρ) = tangentRadius C ρ := rfl

theorem edge_left (a ψ : ℝ) : Real.cos ((a - ψ) - a) = Real.cos ψ := by
  rw [show a - ψ - a = -ψ by ring, Real.cos_neg]

theorem edge_right (a ψ : ℝ) : Real.cos ((a + ψ) - a) = Real.cos ψ := by
  rw [show a + ψ - a = ψ by ring]

theorem unitPoint_add_int (t : ℝ) (k : ℤ) : unitPoint (t + 2 * Real.pi * k) = unitPoint t := by
  unfold unitPoint
  rw [show ((t + 2 * Real.pi * k : ℝ) : ℂ) * Complex.I = (t : ℂ) * Complex.I + (k : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `μ(t) = G_C(re^{it})/r^q` with `r` the tangent radius. -/
noncomputable def muR (p C : ℝ) (ρ : ℂ) (t : ℝ) : ℝ :=
  obstacleG p C ρ ((tangentRadius C ρ : ℂ) * unitPoint t) / tangentRadius C ρ ^ (p / 2)

theorem muR_add_int (t : ℝ) (k : ℤ) : muR p C ρ (t + 2 * Real.pi * k) = muR p C ρ t := by
  unfold muR
  rw [unitPoint_add_int]

/-- `K₀ = p|1 - ρ| r^{1-q} C^{p-1}` (sec3 l.63). -/
noncomputable def kZero (p C : ℝ) (ρ : ℂ) : ℝ :=
  p * ‖1 - ρ‖ * tangentRadius C ρ ^ (1 - p / 2) * C ^ (p - 1)

/-- `K₀|ζ + 1|^{p-2}` at the tangent point in direction `t`. -/
noncomputable def kAt (p C : ℝ) (ρ : ℂ) (t : ℝ) : ℝ :=
  kZero p C ρ * ‖(tangentRadius C ρ : ℂ) * unitPoint t + 1‖ ^ (p - 2)

theorem kAt_pos (hp : 1 < p) (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) {t : ℝ}
    (ht : Real.cos (t - Complex.arg (diskCentre C ρ)) = Real.cos (windowHalfAngle C ρ)) : 0 < kAt p C ρ t := by
  have hC0 : 0 < C := zero_lt_one.trans (one_lt hC)
  have hA := (tangent_sq hρ hC ht).1
  rw [← normSq_one_add_ray, add_comm] at hA
  have hz : 0 < ‖(tangentRadius C ρ : ℂ) * unitPoint t + 1‖ := by
    rcases (norm_nonneg ((tangentRadius C ρ : ℂ) * unitPoint t + 1)).lt_or_eq with h | h
    · exact h
    · rw [← h] at hA; norm_num at hA
  have h1 : 0 < ‖1 - ρ‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hρ))
  unfold kAt kZero
  have := Real.rpow_pos_of_pos (tangentRadius_pos hC) (1 - p / 2)
  have := Real.rpow_pos_of_pos hC0 (p - 1)
  have := Real.rpow_pos_of_pos hz (p - 2)
  have : 0 < p := by linarith
  positivity

/-- `|c| sin(t - arg c)/R = ∓1` at `t = arg c ∓ ψ`. -/
theorem edge_factor_left (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    ‖diskCentre C ρ‖ * Real.sin ((Complex.arg (diskCentre C ρ) - windowHalfAngle C ρ) - Complex.arg (diskCentre C ρ)) /
      Real.sqrt (diskRadiusSq C ρ) = -1 := by
  have hR := (Real.sqrt_pos.2 (radius_pos hρ hC)).ne'
  rw [show Complex.arg (diskCentre C ρ) - windowHalfAngle C ρ - Complex.arg (diskCentre C ρ) =
    -windowHalfAngle C ρ by ring, Real.sin_neg, mul_neg, centre_mul_sin hρ hC, neg_div, div_self hR]

theorem edge_factor_right (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    ‖diskCentre C ρ‖ * Real.sin ((Complex.arg (diskCentre C ρ) + windowHalfAngle C ρ) - Complex.arg (diskCentre C ρ)) /
      Real.sqrt (diskRadiusSq C ρ) = 1 := by
  have hR := (Real.sqrt_pos.2 (radius_pos hρ hC)).ne'
  rw [show Complex.arg (diskCentre C ρ) + windowHalfAngle C ρ - Complex.arg (diskCentre C ρ) =
    windowHalfAngle C ρ by ring, centre_mul_sin hρ hC, div_self hR]

/-- `μ′(t₁) = -K₀|ζ₁ + 1|^{p-2}` at `t₁ = arg c - ψ`. -/
theorem muR_hasDerivAt_left (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    HasDerivAt (muR p C ρ) (-kAt p C ρ (Complex.arg (diskCentre C ρ) - windowHalfAngle C ρ))
      (Complex.arg (diskCentre C ρ) - windowHalfAngle C ρ) := by
  have h := hasDerivAt_edge (p := p) hρ hC (edge_left _ _)
  rw [edge_factor_left hρ hC, mul_neg_one] at h
  exact h

/-- `μ′(t₂) = K₀|ζ₂ + 1|^{p-2}` at `t₂ = arg c + ψ`. -/
theorem muR_hasDerivAt_right (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    HasDerivAt (muR p C ρ) (kAt p C ρ (Complex.arg (diskCentre C ρ) + windowHalfAngle C ρ))
      (Complex.arg (diskCentre C ρ) + windowHalfAngle C ρ) := by
  have h := hasDerivAt_edge (p := p) hρ hC (edge_right _ _)
  rw [edge_factor_right hρ hC, mul_one] at h
  exact h

/-- `μ` vanishes at both tangent directions. -/
theorem muR_edge_zero (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) {t : ℝ}
    (ht : Real.cos (t - Complex.arg (diskCentre C ρ)) = Real.cos (windowHalfAngle C ρ)) : muR p C ρ t = 0 := by
  unfold muR
  rw [G_eq_zero_of_circle hC (tangent_on_circle hρ hC ht), zero_div]

/-- A pair `(s, s')` = `(t₁, t₂)` or `(t₂, t₁)` with `s' = s + 2π/p + 2πk`. -/
def IsArchPair (p C : ℝ) (ρ : ℂ) (s s' : ℝ) : Prop :=
  (s = Complex.arg (diskCentre C ρ) - windowHalfAngle C ρ ∧ s' = Complex.arg (diskCentre C ρ) + windowHalfAngle C ρ ∨
    s = Complex.arg (diskCentre C ρ) + windowHalfAngle C ρ ∧ s' = Complex.arg (diskCentre C ρ) - windowHalfAngle C ρ) ∧
  ∃ k : ℤ, s' = s + 2 * Real.pi / p + 2 * Real.pi * k

/-- `M̃(t) = μ(t) + μ(t + 2π/p)` has derivative `μ′(t₁) + μ′(t₂) = K₀(|ζ₂ + 1|^{p-2} - |ζ₁ + 1|^{p-2})` at `s`. -/
theorem sum_hasDerivAt (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) {s s' : ℝ} (h : IsArchPair p C ρ s s') :
    HasDerivAt (fun t => muR p C ρ t + muR p C ρ (t + 2 * Real.pi / p))
      (-kAt p C ρ (Complex.arg (diskCentre C ρ) - windowHalfAngle C ρ) +
        kAt p C ρ (Complex.arg (diskCentre C ρ) + windowHalfAngle C ρ)) s := by
  obtain ⟨hss, k, hk⟩ := h
  have hshift : (fun t => muR p C ρ (t + 2 * Real.pi / p)) =
      fun t => muR p C ρ (t + (2 * Real.pi / p + 2 * Real.pi * k)) := by
    funext t
    rw [← add_assoc, muR_add_int]
  have hL := muR_hasDerivAt_left (p := p) hρ hC
  have hR := muR_hasDerivAt_right (p := p) hρ hC
  rcases hss with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h2 : HasDerivAt (fun t => muR p C ρ (t + 2 * Real.pi / p))
        (kAt p C ρ (Complex.arg (diskCentre C ρ) + windowHalfAngle C ρ))
        (Complex.arg (diskCentre C ρ) - windowHalfAngle C ρ) := by
      rw [hshift]
      exact HasDerivAt.comp_add_const _ _ (by rw [← add_assoc, ← hk]; exact hR)
    exact hL.add h2
  · have h2 : HasDerivAt (fun t => muR p C ρ (t + 2 * Real.pi / p))
        (-kAt p C ρ (Complex.arg (diskCentre C ρ) - windowHalfAngle C ρ))
        (Complex.arg (diskCentre C ρ) + windowHalfAngle C ρ) := by
      rw [hshift]
      exact HasDerivAt.comp_add_const _ _ (by rw [← add_assoc, ← hk]; exact hL)
    rw [add_comm (-kAt p C ρ _)]
    exact hR.add h2

/-- `M̃(s) = 0` at the relabelled `s`. -/
theorem sum_zero (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) {s s' : ℝ} (h : IsArchPair p C ρ s s') :
    muR p C ρ s + muR p C ρ (s + 2 * Real.pi / p) = 0 := by
  obtain ⟨hss, k, hk⟩ := h
  have e : s + 2 * Real.pi / p = s' + 2 * Real.pi * (-k : ℤ) := by rw [hk]; push_cast; ring
  rw [e, muR_add_int]
  rcases hss with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [muR_edge_zero hρ hC (edge_left _ _), muR_edge_zero hρ hC (edge_right _ _), add_zero]
  · rw [muR_edge_zero hρ hC (edge_right _ _), muR_edge_zero hρ hC (edge_left _ _), add_zero]

/-- With `C = GK_p(ρ)` an arch pair exists (Step 1's relabelling). -/
theorem exists_archPair (hp : 1 < p) (hp2 : p ≠ 2) (hρ : ρ ≠ 1) :
    ∃ s s' : ℝ, IsArchPair p (gk p ρ) ρ s s' := by
  rcases tangent_arch hp hp2 hρ with h | h
  · exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, 0, by push_cast; linarith⟩
  · exact ⟨_, _, Or.inr ⟨rfl, rfl⟩, -1, by push_cast; linarith⟩

theorem obstacle_le_muR (hp : 1 < p) (hC : max 1 ‖ρ‖ < C) (t : ℝ) : obstacle p C ρ t ≤ muR p C ρ t := by
  have h := obstacle_le hp hC t _ (tangentRadius_pos hC)
  rwa [Real.rpow_neg (tangentRadius_pos hC).le, inv_mul_eq_div] at h

end Contact


/-! ### sec3_radial_limits: `G_C(re^{it})/r^q → +∞` as `r → 0⁺` and as `r → ∞` -/

section Radial

open Filter Topology

variable {p C : ℝ} {ρ : ℂ}

theorem continuous_G_ray (hp0 : 0 < p) (C : ℝ) (ρ : ℂ) (t : ℝ) :
    Continuous fun r : ℝ => obstacleG p C ρ ((r : ℂ) * unitPoint t) := by
  unfold obstacleG
  exact (continuous_const.mul ((by fun_prop : Continuous fun r : ℝ => ‖1 + (r : ℂ) * unitPoint t‖).rpow_const
    fun _ => Or.inr hp0.le)).sub
    ((by fun_prop : Continuous fun r : ℝ => ‖ρ + (r : ℂ) * unitPoint t‖).rpow_const fun _ => Or.inr hp0.le)

/-- `H(s) = C^p|s + e^{it}|^p - |ρs + e^{it}|^p`, so that `G_C(re^{it}) = r^p H(1/r)`. -/
noncomputable def farH (p C : ℝ) (ρ : ℂ) (t s : ℝ) : ℝ :=
  C ^ p * ‖(s : ℂ) + unitPoint t‖ ^ p - ‖ρ * s + unitPoint t‖ ^ p

theorem continuous_farH (hp0 : 0 < p) (C : ℝ) (ρ : ℂ) (t : ℝ) : Continuous (farH p C ρ t) := by
  unfold farH
  exact (continuous_const.mul ((by fun_prop : Continuous fun s : ℝ => ‖(s : ℂ) + unitPoint t‖).rpow_const
    fun _ => Or.inr hp0.le)).sub
    ((by fun_prop : Continuous fun s : ℝ => ‖ρ * s + unitPoint t‖).rpow_const fun _ => Or.inr hp0.le)

theorem G_ray_far (C : ℝ) (ρ : ℂ) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    obstacleG p C ρ ((r : ℂ) * unitPoint t) / r ^ (p / 2) = r ^ (p / 2) * farH p C ρ t r⁻¹ := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  have e1 : ‖1 + (r : ℂ) * unitPoint t‖ = r * ‖((r⁻¹ : ℝ) : ℂ) + unitPoint t‖ := by
    have h : (1 : ℂ) + (r : ℂ) * unitPoint t = (r : ℂ) * (((r⁻¹ : ℝ) : ℂ) + unitPoint t) := by
      push_cast
      rw [mul_add, mul_inv_cancel₀ hr']
    rw [h, norm_mul, hn]
  have e2 : ‖ρ + (r : ℂ) * unitPoint t‖ = r * ‖ρ * ((r⁻¹ : ℝ) : ℂ) + unitPoint t‖ := by
    have h : ρ + (r : ℂ) * unitPoint t = (r : ℂ) * (ρ * ((r⁻¹ : ℝ) : ℂ) + unitPoint t) := by
      push_cast
      rw [mul_add, mul_left_comm, mul_inv_cancel₀ hr', mul_one]
    rw [h, norm_mul, hn]
  have hq : r ^ p = r ^ (p / 2) * r ^ (p / 2) := by
    rw [← Real.rpow_add hr]
    ring_nf
  have hrq : 0 < r ^ (p / 2) := Real.rpow_pos_of_pos hr _
  unfold obstacleG farH
  rw [e1, e2, Real.mul_rpow hr.le (norm_nonneg _), Real.mul_rpow hr.le (norm_nonneg _), hq]
  field_simp

theorem sec3_radial_limits_proved {p C : ℝ} (hp : 1 < p) {ρ : ℂ} (hC : max 1 ‖ρ‖ < C) (t : ℝ) :
    Tendsto (fun r : ℝ => obstacleG p C ρ ((r : ℂ) * unitPoint t) / r ^ (p / 2)) (𝓝[>] 0) atTop ∧
    Tendsto (fun r : ℝ => obstacleG p C ρ ((r : ℂ) * unitPoint t) / r ^ (p / 2)) atTop atTop := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < p / 2 := by linarith
  have hC1 : 1 < C := one_lt hC
  have hρC : ‖ρ‖ < C := lt_of_le_of_lt (le_max_right _ _) hC
  refine ⟨?_, ?_⟩
  · -- near 0: `G_C(re^{it}) → C^p - |ρ|^p > 0` and `r^{-q} → +∞`
    have h0 : obstacleG p C ρ (((0 : ℝ) : ℂ) * unitPoint t) = C ^ p - ‖ρ‖ ^ p := by
      simp [obstacleG]
    have hpos : 0 < C ^ p - ‖ρ‖ ^ p := sub_pos.2 (Real.rpow_lt_rpow (norm_nonneg _) hρC hp0)
    have hf : Tendsto (fun r : ℝ => obstacleG p C ρ ((r : ℂ) * unitPoint t)) (𝓝[>] 0) (𝓝 (C ^ p - ‖ρ‖ ^ p)) := by
      rw [← h0]
      exact tendsto_nhdsWithin_of_tendsto_nhds ((continuous_G_ray hp0 C ρ t).tendsto 0)
    have hpow : Tendsto (fun r : ℝ => r ^ (p / 2)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun r hr => Real.rpow_pos_of_pos hr _⟩
      have h := (Real.continuous_rpow_const hq.le).tendsto 0
      rw [Real.zero_rpow hq.ne'] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    have hg := tendsto_inv_nhdsGT_zero.comp hpow
    have h := hf.pos_mul_atTop hpos hg
    simpa only [Function.comp_def, div_eq_mul_inv] using h
  · -- near ∞: `G_C(re^{it})/r^q = r^q H(1/r)`, `H(1/r) → C^p - 1 > 0`
    have hH0 : farH p C ρ t 0 = C ^ p - 1 := by
      simp [farH, norm_unitPoint]
    have hpos : 0 < C ^ p - 1 := sub_pos.2 (Real.one_lt_rpow hC1 hp0)
    have hH : Tendsto (fun r : ℝ => farH p C ρ t r⁻¹) atTop (𝓝 (C ^ p - 1)) := by
      rw [← hH0]
      exact ((continuous_farH hp0 C ρ t).tendsto 0).comp tendsto_inv_atTop_zero
    have h := (tendsto_rpow_atTop hq).atTop_mul_pos hpos hH
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    exact (G_ray_far (p := p) C ρ t hr).symm

end Radial

/-! ### The rows of Section 3 (types verbatim from PROPOSAL_slice_c_019.lean v0.21) -/

section Rows

/-- **sec3_window** (sec3_nonreal.tex l.21-24). -/
theorem sec3_window_proved {p C : ℝ} (hp : 1 < p) {ρ : ℂ} (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    (∀ t : ℝ, obstacle p C ρ t < 0 ↔ ∃ r : ℝ, 0 < r ∧ obstacleG p C ρ ((r : ℂ) * unitPoint t) < 0) ∧
    (∀ t : ℝ, obstacle p C ρ t < 0 ↔
      Real.cos (windowHalfAngle C ρ) < Real.cos (t - Complex.arg (diskCentre C ρ))) ∧
    (∀ t : ℝ, Real.cos (t - Complex.arg (diskCentre C ρ)) = Real.cos (windowHalfAngle C ρ) →
      obstacle p C ρ t = 0 ∧ ∃ r : ℝ, 0 < r ∧ obstacleG p C ρ ((r : ℂ) * unitPoint t) = 0 ∧
        obstacle p C ρ t = r ^ (-(p / 2)) * obstacleG p C ρ ((r : ℂ) * unitPoint t)) := by
  refine ⟨obstacle_neg_iff hp hC, obstacle_neg_iff_window hp hρ hC, fun t ht => ?_⟩
  obtain ⟨h0, hG⟩ := obstacle_eq_zero_of_edge hp hρ hC ht
  exact ⟨h0, tangentRadius C ρ, tangentRadius_pos hC, hG, by rw [h0, hG, mul_zero]⟩

/-- **thmA_step1** (sec3_nonreal.tex l.48-51). -/
theorem thmA_step1_proved {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {ρ : ℂ} (hρ : ρ ≠ 1) :
    let C := gk p ρ
    let c := diskCentre C ρ
    let r := Real.sqrt (‖c‖ ^ 2 - diskRadiusSq C ρ)
    let t₁ := Complex.arg c - windowHalfAngle C ρ
    let t₂ := Complex.arg c + windowHalfAngle C ρ
    0 < r ∧ obstacleG p C ρ ((r : ℂ) * unitPoint t₁) = 0 ∧ obstacleG p C ρ ((r : ℂ) * unitPoint t₂) = 0 ∧
    obstacle p C ρ t₁ = 0 ∧ obstacle p C ρ t₂ = 0 ∧
    ∃ k : ℤ, t₂ = t₁ + 2 * Real.pi / p + 2 * Real.pi * k ∨ t₁ = t₂ + 2 * Real.pi / p + 2 * Real.pi * k := by
  dsimp only
  rw [tangentRadius_eq]
  have hC := gk_gt_max hp hp2 hρ
  obtain ⟨h1o, h1G⟩ := obstacle_eq_zero_of_edge hp hρ hC (edge_left _ _)
  obtain ⟨h2o, h2G⟩ := obstacle_eq_zero_of_edge hp hρ hC (edge_right _ _)
  refine ⟨tangentRadius_pos hC, h1G, h2G, h1o, h2o, ?_⟩
  rcases tangent_arch hp hp2 hρ with h | h
  · exact ⟨0, Or.inl (by push_cast; linarith)⟩
  · exact ⟨-1, Or.inr (by push_cast; linarith)⟩

/-- **thmA_step2** (sec3_nonreal.tex l.53-55). -/
theorem thmA_step2_proved {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {ρ : ℂ} (hρ : ρ ≠ 1) :
    let C := gk p ρ
    let c := diskCentre C ρ
    let r := Real.sqrt (‖c‖ ^ 2 - diskRadiusSq C ρ)
    let t₁ := Complex.arg c - windowHalfAngle C ρ
    let t₂ := Complex.arg c + windowHalfAngle C ρ
    let μ := fun t : ℝ => obstacleG p C ρ ((r : ℂ) * unitPoint t) / r ^ (p / 2)
    (∀ t : ℝ, obstacle p C ρ t ≤ μ t) ∧ μ t₁ = obstacle p C ρ t₁ ∧ μ t₁ = 0 ∧
    μ t₂ = obstacle p C ρ t₂ ∧ μ t₂ = 0 ∧
    (∀ t : ℝ, obstacle p C ρ t + obstacle p C ρ (t + 2 * Real.pi / p) ≤ μ t + μ (t + 2 * Real.pi / p)) ∧
    ∀ s s' : ℝ, (s = t₁ ∧ s' = t₂ ∨ s = t₂ ∧ s' = t₁) → (∃ k : ℤ, s' = s + 2 * Real.pi / p + 2 * Real.pi * k) →
      μ s + μ (s + 2 * Real.pi / p) = 0 := by
  dsimp only
  have hC := gk_gt_max hp hp2 hρ
  have hle := obstacle_le_muR (ρ := ρ) hp hC
  have h1 := muR_edge_zero (p := p) hρ hC (edge_left _ _)
  have h2 := muR_edge_zero (p := p) hρ hC (edge_right _ _)
  have o1 := (obstacle_eq_zero_of_edge hp hρ hC (edge_left _ _)).1
  have o2 := (obstacle_eq_zero_of_edge hp hρ hC (edge_right _ _)).1
  unfold muR at hle h1 h2
  rw [tangentRadius_eq]
  refine ⟨hle, by rw [h1, o1], h1, by rw [h2, o2], h2, fun t => add_le_add (hle t) (hle _),
    fun s s' hss hk => ?_⟩
  have h := sum_zero (p := p) hρ hC ⟨hss, hk⟩
  unfold muR at h
  exact h

/-- **thmA_step3** (sec3_nonreal.tex l.57-65). -/
theorem thmA_step3_proved {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {ρ : ℂ} (hρ : ρ ≠ 1) :
    let C := gk p ρ
    let c := diskCentre C ρ
    let r := Real.sqrt (‖c‖ ^ 2 - diskRadiusSq C ρ)
    let t₁ := Complex.arg c - windowHalfAngle C ρ
    let t₂ := Complex.arg c + windowHalfAngle C ρ
    let ζ₁ : ℂ := (r : ℂ) * unitPoint t₁
    let ζ₂ : ℂ := (r : ℂ) * unitPoint t₂
    let μ := fun t : ℝ => obstacleG p C ρ ((r : ℂ) * unitPoint t) / r ^ (p / 2)
    let K₀ := p * ‖1 - ρ‖ * r ^ (1 - p / 2) * C ^ (p - 1)
    |deriv μ t₁| = K₀ * ‖ζ₁ + 1‖ ^ (p - 2) ∧ 0 < K₀ * ‖ζ₁ + 1‖ ^ (p - 2) ∧
    |deriv μ t₂| = K₀ * ‖ζ₂ + 1‖ ^ (p - 2) ∧ 0 < K₀ * ‖ζ₂ + 1‖ ^ (p - 2) ∧
    deriv μ t₁ * deriv μ t₂ < 0 ∧
    (∀ s s' : ℝ, (s = t₁ ∧ s' = t₂ ∨ s = t₂ ∧ s' = t₁) → (∃ k : ℤ, s' = s + 2 * Real.pi / p + 2 * Real.pi * k) →
      HasDerivAt (fun t => μ t + μ (t + 2 * Real.pi / p)) (deriv μ t₁ + deriv μ t₂) s) ∧
    (deriv μ t₁ + deriv μ t₂ = K₀ * (‖ζ₁ + 1‖ ^ (p - 2) - ‖ζ₂ + 1‖ ^ (p - 2)) ∨
      deriv μ t₁ + deriv μ t₂ = -(K₀ * (‖ζ₁ + 1‖ ^ (p - 2) - ‖ζ₂ + 1‖ ^ (p - 2)))) := by
  dsimp only
  have hC := gk_gt_max hp hp2 hρ
  have hL := muR_hasDerivAt_left (p := p) hρ hC
  have hR := muR_hasDerivAt_right (p := p) hρ hC
  have k1 := kAt_pos hp hρ hC (edge_left _ _)
  have k2 := kAt_pos hp hρ hC (edge_right _ _)
  have hsum : ∀ s s' : ℝ, IsArchPair p (gk p ρ) ρ s s' → HasDerivAt (fun t => muR p (gk p ρ) ρ t +
      muR p (gk p ρ) ρ (t + 2 * Real.pi / p)) (-kAt p (gk p ρ) ρ (Complex.arg (diskCentre (gk p ρ) ρ) -
        windowHalfAngle (gk p ρ) ρ) + kAt p (gk p ρ) ρ (Complex.arg (diskCentre (gk p ρ) ρ) +
          windowHalfAngle (gk p ρ) ρ)) s := fun s s' h => sum_hasDerivAt hρ hC h
  unfold muR at hL hR hsum
  unfold kAt kZero at hL hR k1 k2 hsum
  rw [tangentRadius_eq, hL.deriv, hR.deriv]
  refine ⟨by rw [abs_neg, abs_of_pos k1], k1, abs_of_pos k2, k2, by nlinarith, fun s s' hss hk => hsum s s' ⟨hss, hk⟩,
    Or.inr (by ring)⟩

/-- **thmA_step4** (sec3_nonreal.tex l.67-70). -/
theorem thmA_step4_proved {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {ρ : ℂ} (hρ : ρ ≠ 1) :
    let C := gk p ρ
    let c := diskCentre C ρ
    let r := Real.sqrt (‖c‖ ^ 2 - diskRadiusSq C ρ)
    ‖(r : ℂ) * unitPoint (Complex.arg c - windowHalfAngle C ρ) + 1‖ =
        ‖(r : ℂ) * unitPoint (Complex.arg c + windowHalfAngle C ρ) + 1‖ ↔ ρ.im = 0 := by
  dsimp only
  rw [tangentRadius_eq]
  exact tangent_norm_eq_iff hρ (gk_gt_max hp hp2 hρ)

/-- **thmA_remark_real** (sec3_nonreal.tex l.76-78). -/
theorem thmA_remark_real_proved {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {lam : ℝ} (hl : lam ≠ 1) :
    let C := gk p lam
    let c := diskCentre C lam
    let r := Real.sqrt (‖c‖ ^ 2 - diskRadiusSq C lam)
    let t₁ := Complex.arg c - windowHalfAngle C lam
    let t₂ := Complex.arg c + windowHalfAngle C lam
    let μ := fun t : ℝ => obstacleG p C lam ((r : ℂ) * unitPoint t) / r ^ (p / 2)
    ∀ s s' : ℝ, (s = t₁ ∧ s' = t₂ ∨ s = t₂ ∧ s' = t₁) → (∃ k : ℤ, s' = s + 2 * Real.pi / p + 2 * Real.pi * k) →
      HasDerivAt (fun t => μ t + μ (t + 2 * Real.pi / p)) 0 s := by
  dsimp only
  intro s s' hss hk
  have hl' : (lam : ℂ) ≠ 1 := fun h => hl (by exact_mod_cast h)
  have hC := gk_gt_max hp hp2 hl'
  have h := sum_hasDerivAt (p := p) hl' hC ⟨hss, hk⟩
  have heq := (tangent_norm_eq_iff hl' hC).2 (Complex.ofReal_im lam)
  unfold kAt at h
  rw [heq, neg_add_cancel] at h
  unfold muR at h
  rw [tangentRadius_eq]
  exact h

/-- **sec3_arch** (sec3_nonreal.tex l.13-14; `1/2 < q` is the section's standing `q = p/2`, `p > 1`, l.7), from the
exact type of the chord-lemma row `slice_O30` (sec2_obstacle.tex l.108-110) with `s = π/(2q)`. -/
theorem sec3_arch_given
    (hchord : ∀ (q : ℝ), 1 / 2 < q → ∀ (φ : ℝ → ℝ), QSubtrig q φ → ∀ (c s : ℝ), 0 < s ∧ s ≤ Real.pi / q →
      2 * Real.cos (q * s) * φ c ≤ φ (c - s) + φ (c + s))
    {q : ℝ} (hq : 1 / 2 < q) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) (t : ℝ) :
    0 ≤ φ t + φ (t + Real.pi / q) := by
  have hq0 : 0 < q := by linarith
  have hs : 0 < Real.pi / (2 * q) ∧ Real.pi / (2 * q) ≤ Real.pi / q := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ (by positivity) hq0]
    nlinarith [Real.pi_pos]
  have h := hchord q hq φ hφ (t + Real.pi / (2 * q)) (Real.pi / (2 * q)) hs
  have e1 : q * (Real.pi / (2 * q)) = Real.pi / 2 := by field_simp
  have e2 : t + Real.pi / (2 * q) + Real.pi / (2 * q) = t + Real.pi / q := by field_simp; ring
  rw [e1, Real.cos_pi_div_two, mul_zero, zero_mul, add_sub_cancel_right, e2] at h
  exact h

/-- **eq_3_2** (sec3_nonreal.tex l.14-15), from the exact types of Theorem R (`slice_O18`, sec2_obstacle.tex
l.62-65; only its "only if" half is used) and of `sec3_arch`. -/
theorem eq_3_2_given
    (hR : ∀ {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)], 1 < p → ∀ (P : RieszProjection p) (ρ : ℂ) (C : ℝ),
      max 1 ‖ρ‖ < C →
      (pencilNorm P ρ ≤ C ↔ ∃ φ : ℝ → ℝ, QSubtrig (p / 2) φ ∧ ∀ t, φ t ≤ obstacle p C ρ t) ∧
      pencilNorm P ρ = sInf {D : ℝ | max 1 ‖ρ‖ < D ∧ ∃ φ : ℝ → ℝ,
        QSubtrig (p / 2) φ ∧ ∀ t, φ t ≤ obstacle p D ρ t})
    (harch : ∀ {q : ℝ}, 1 / 2 < q → ∀ {φ : ℝ → ℝ}, QSubtrig q φ → ∀ (t : ℝ), 0 ≤ φ t + φ (t + Real.pi / q))
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) (ρ : ℂ)
    {C : ℝ} (hC : max 1 ‖ρ‖ < C)
    (h : ∃ t₁ : ℝ, obstacle p C ρ t₁ + obstacle p C ρ (t₁ + 2 * Real.pi / p) < 0) :
    C < pencilNorm P ρ := by
  by_contra hn
  obtain ⟨φ, hφ, hle⟩ := (hR hp P ρ C hC).1.1 (not_lt.1 hn)
  obtain ⟨t₁, ht⟩ := h
  have ha := harch (by linarith : (1 : ℝ) / 2 < p / 2) hφ t₁
  have e : Real.pi / (p / 2) = 2 * Real.pi / p := by field_simp
  rw [e] at ha
  linarith [hle t₁, hle (t₁ + 2 * Real.pi / p)]

/-- **Theorem A** (sec3_nonreal.tex l.42-73), from the exact type of the row `eq_3_2`. -/
theorem thm_A_given
    (h32 : ∀ {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)], 1 < p → ∀ (P : RieszProjection p) (ρ : ℂ) {C : ℝ},
      max 1 ‖ρ‖ < C → (∃ t₁ : ℝ, obstacle p C ρ t₁ + obstacle p C ρ (t₁ + 2 * Real.pi / p) < 0) →
      C < pencilNorm P ρ)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p ≠ 2)
    (P : RieszProjection p) {ρ : ℂ} (hρ : ρ.im ≠ 0) : gk p ρ < pencilNorm P ρ := by
  have hρ1 : ρ ≠ 1 := fun h => hρ (by rw [h, Complex.one_im])
  have hC := gk_gt_max hp hp2 hρ1
  obtain ⟨s, s', hpair⟩ := exists_archPair hp hp2 hρ1
  have hd := sum_hasDerivAt hρ1 hC hpair
  have hz := sum_zero hρ1 hC hpair
  have k1 := kAt_pos hp hρ1 hC (edge_left _ _)
  have k2 := kAt_pos hp hρ1 hC (edge_right _ _)
  -- the slope is not zero: `|ζ₁ + 1| ≠ |ζ₂ + 1|` since `ρ ∉ ℝ`, and `x ↦ x^{p-2}` is injective (`p ≠ 2`)
  have hne : -kAt p (gk p ρ) ρ (Complex.arg (diskCentre (gk p ρ) ρ) - windowHalfAngle (gk p ρ) ρ) +
      kAt p (gk p ρ) ρ (Complex.arg (diskCentre (gk p ρ) ρ) + windowHalfAngle (gk p ρ) ρ) ≠ 0 := by
    intro h0
    have hk : kAt p (gk p ρ) ρ (Complex.arg (diskCentre (gk p ρ) ρ) - windowHalfAngle (gk p ρ) ρ) =
        kAt p (gk p ρ) ρ (Complex.arg (diskCentre (gk p ρ) ρ) + windowHalfAngle (gk p ρ) ρ) := by linarith
    unfold kAt at hk k1
    have hK0 : kZero p (gk p ρ) ρ ≠ 0 := fun h => by rw [h, zero_mul] at k1; exact lt_irrefl 0 k1
    have hpow := mul_left_cancel₀ hK0 hk
    have hp2' : p - 2 ≠ 0 := sub_ne_zero.2 hp2
    have hn := congrArg (fun x : ℝ => x ^ (p - 2)⁻¹) hpow
    rw [Real.rpow_rpow_inv (norm_nonneg _) hp2', Real.rpow_rpow_inv (norm_nonneg _) hp2'] at hn
    exact hρ ((tangent_norm_eq_iff hρ1 hC).1 hn)
  -- so `s` is not a minimum of `M̃`, and `M̃ < 0` somewhere
  obtain ⟨t, ht⟩ : ∃ t, muR p (gk p ρ) ρ t + muR p (gk p ρ) ρ (t + 2 * Real.pi / p) < 0 := by
    by_contra hn
    push Not at hn
    have hmin : IsLocalMin (fun t => muR p (gk p ρ) ρ t + muR p (gk p ρ) ρ (t + 2 * Real.pi / p)) s :=
      Filter.Eventually.of_forall fun x => by beta_reduce; rw [hz]; exact hn x
    exact hne (hmin.hasDerivAt_eq_zero hd)
  exact h32 hp P ρ hC ⟨t, lt_of_le_of_lt (add_le_add (obstacle_le_muR hp hC t) (obstacle_le_muR hp hC _)) ht⟩

end Rows

end GKSharp.Sec3Geom

