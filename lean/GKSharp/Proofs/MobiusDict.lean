/- GKSharp/Proofs/MobiusDict.lean - the Moebius dictionary of Section 5: Q(w(z)), Re Q^q and D_C in the w-plane
(5.1), the bijection, the ellipses E_rho, the critical-point equation w = tau v iff D(theta, r) = 0 ((5.3), algebraic
part) and the identities (5.4) (sec5_sharp_inequality.tex l.18-41).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.CriticalCurve

namespace GKSharp

open ComplexConjugate

section Basic

theorem mobW_re (lam : ℝ) (z : ℂ) :
    (mobW lam z).re = (1 + (1 + lam) * z.re + lam * Complex.normSq z) / Complex.normSq (1 + z) := by
  unfold mobW
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.one_im, Complex.mul_im, Complex.normSq_apply]
  ring

theorem mobW_im (lam : ℝ) (z : ℂ) : (mobW lam z).im = -((1 - lam) * z.im) / Complex.normSq (1 + z) := by
  unfold mobW
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.one_im, Complex.mul_im, Complex.normSq_apply]
  ring

theorem polar_re_im (r θ : ℝ) :
    ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)).re = r * Real.cos θ ∧
    ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)).im = -(r * Real.sin θ) := by
  have he : -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg]
  constructor <;> ring

theorem polar_normSq (r θ : ℝ) : Complex.normSq ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)) = r ^ 2 := by
  obtain ⟨h1, h2⟩ := polar_re_im r θ
  rw [Complex.normSq_apply, h1, h2]
  linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ

theorem curveV_re_im (p lam θ : ℝ) :
    (curveV p lam θ).re = (1 + lam) * Real.cos ((1 - p / 2) * θ) ∧
    (curveV p lam θ).im = (1 - lam) * Real.sin ((1 - p / 2) * θ) := by
  unfold curveV
  have he : -((((1 - p / 2) * θ : ℝ) : ℂ)) * Complex.I = ((-((1 - p / 2) * θ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [he]
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  constructor <;> ring

theorem reQPow_real_mul_conj {c : ℝ} (hc : 0 < c) (z : ℂ) (q : ℝ) :
    reQPow ((c : ℂ) * conj z) q = c ^ q * reQPow z q := by
  unfold reQPow
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, Complex.norm_conj,
    Real.mul_rpow hc.le (norm_nonneg _), Complex.arg_real_mul _ hc, Complex.arg_conj]
  split_ifs with h
  · rw [h]; ring
  · rw [mul_neg, Real.cos_neg]; ring

theorem sq_rpow_half {x : ℝ} (hx : 0 ≤ x) (p : ℝ) : (x ^ 2) ^ (p / 2) = x ^ p := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  congr 1; push_cast; ring

end Basic

section Dictionary

variable {lam : ℝ}

theorem one_add_ne_zero {z : ℂ} (hz : z ≠ -1) : (1 : ℂ) + z ≠ 0 := by
  intro h; apply hz; linear_combination h

/-- sec5_sharp_inequality.tex l.19-20: `w - λ = (1-λ)/(1+z)`, `1 - w = (1-λ)z/(1+z)`. -/
theorem mobW_sub (lam : ℝ) {z : ℂ} (hz : z ≠ -1) :
    mobW lam z - lam = (1 - lam) / (1 + z) ∧ 1 - mobW lam z = (1 - lam) * z / (1 + z) := by
  have h1 := one_add_ne_zero hz
  unfold mobW
  constructor <;> field_simp <;> ring

/-- (5.1), first identity: `Q(w(z)) = (1-λ)² z̄ / |1+z|²`. -/
theorem mobQ_mobW (lam : ℝ) {z : ℂ} (hz : z ≠ -1) :
    mobQ lam (mobW lam z) = (((1 - lam) ^ 2 / ‖1 + z‖ ^ 2 : ℝ) : ℂ) * conj z := by
  have h1 := one_add_ne_zero hz
  have h2 : 1 + conj z ≠ 0 := by
    intro h; apply h1; have := congrArg conj h; simpa using this
  have hn : ((‖1 + z‖ : ℂ)) ^ 2 = (1 + z) * (1 + conj z) := by
    rw [← Complex.mul_conj', map_add, map_one]
  obtain ⟨ha, hb⟩ := mobW_sub lam hz
  unfold mobQ
  rw [ha, show (1 : ℂ) - conj (mobW lam z) = conj (1 - mobW lam z) by simp, hb]
  push_cast
  rw [hn]
  simp only [map_div₀, map_mul, map_sub, map_one, map_add, Complex.conj_ofReal]
  field_simp

/-- (5.1), second identity: `Re Q^q = (1-λ)^p Re z^q / |1+z|^p`, `q = p/2`. -/
theorem reQPow_mobQ (p : ℝ) (hl : lam < 1) {z : ℂ} (hz : z ≠ -1) :
    reQPow (mobQ lam (mobW lam z)) (p / 2) = (1 - lam) ^ p * reQPow z (p / 2) / ‖1 + z‖ ^ p := by
  have h1 : 0 < ‖1 + z‖ := norm_pos_iff.2 (one_add_ne_zero hz)
  have hc : 0 < (1 - lam) ^ 2 / ‖1 + z‖ ^ 2 := by
    have : 0 < 1 - lam := by linarith
    positivity
  rw [mobQ_mobW lam hz, reQPow_real_mul_conj hc, Real.div_rpow (by positivity) (by positivity),
    sq_rpow_half (by linarith) p, sq_rpow_half h1.le p]
  ring

/-- (5.1), third identity: `𝒟_C(z) = |1+z|^p / (1-λ)^p · Φ(w)`. -/
theorem critD_eq_mobPhi (p C K : ℝ) (hl : lam < 1) {z : ℂ} (hz : z ≠ -1) :
    critD p C K lam z = ‖1 + z‖ ^ p / (1 - lam) ^ p * mobPhi p C K lam (mobW lam z) := by
  have h1 : 0 < ‖1 + z‖ := norm_pos_iff.2 (one_add_ne_zero hz)
  have hl' : 0 < 1 - lam := by linarith
  have hw : ‖mobW lam z‖ ^ p = ‖1 + (lam : ℂ) * z‖ ^ p / ‖1 + z‖ ^ p := by
    unfold mobW; rw [norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
  have hA : 0 < ‖1 + z‖ ^ p := Real.rpow_pos_of_pos h1 p
  have hB : 0 < (1 - lam) ^ p := Real.rpow_pos_of_pos hl' p
  unfold critD mobPhi
  rw [hw, reQPow_mobQ p hl hz]
  field_simp

/-- sec5_sharp_inequality.tex l.19: `w` is a bijection of `ℂ \ {-1}` onto `ℂ \ {λ}`. -/
theorem mobW_bijOn (hl : lam ≠ 1) : Set.BijOn (mobW lam) {z | z ≠ -1} {w | w ≠ (lam : ℂ)} := by
  have hl' : (1 : ℂ) - lam ≠ 0 := by
    intro h; apply hl; have := congrArg Complex.re h; simp at this; linarith
  refine ⟨fun z hz => ?_, fun z1 hz1 z2 hz2 h => ?_, fun w hw => ?_⟩
  · have h1 := one_add_ne_zero (show z ≠ -1 from hz)
    show mobW lam z ≠ lam
    intro h; unfold mobW at h; rw [div_eq_iff h1] at h; apply hl'; linear_combination h
  · have h1 := one_add_ne_zero (show z1 ≠ -1 from hz1)
    have h2 := one_add_ne_zero (show z2 ≠ -1 from hz2)
    unfold mobW at h
    rw [div_eq_div_iff h1 h2] at h
    have h3 : (1 - (lam : ℂ)) * (z1 - z2) = 0 := by linear_combination -h
    have := (mul_eq_zero.1 h3).resolve_left hl'
    linear_combination this
  · have hw' : w - (lam : ℂ) ≠ 0 := sub_ne_zero.2 hw
    refine ⟨(1 - w) / (w - lam), ?_, ?_⟩
    · show (1 - w) / (w - lam) ≠ -1
      intro h; rw [div_eq_iff hw'] at h; apply hl'; linear_combination h
    · have h1 : (1 : ℂ) + (1 - w) / (w - lam) ≠ 0 := by
        rw [show (1 : ℂ) + (1 - w) / (w - lam) = (1 - lam) / (w - lam) by field_simp; ring]
        exact div_ne_zero hl' hw'
      unfold mobW
      rw [div_eq_iff h1]
      field_simp
      ring

/-- sec5_sharp_inequality.tex l.19: `Im w = -(1-λ) Im z / |1+z|²`. -/
theorem mobW_im_norm (lam : ℝ) (z : ℂ) : (mobW lam z).im = -(1 - lam) * z.im / ‖1 + z‖ ^ 2 := by
  rw [mobW_im, Complex.sq_norm]; ring

/-- sec5_sharp_inequality.tex l.26-28: for `w = ρ e^{iφ}`, `Q = -(ρ²+λ) + (1+λ)ρ cos φ + i(1-λ)ρ sin φ`, and
`Q(w̄) = conj Q(w)`. -/
theorem mobQ_polar (lam ρ φ : ℝ) :
    mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) =
      ((-(ρ ^ 2 + lam) + (1 + lam) * ρ * Real.cos φ : ℝ) : ℂ) + (((1 - lam) * ρ * Real.sin φ : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp only [mobQ, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.I_re, Complex.I_im, Complex.mul_im]
    linear_combination (-ρ ^ 2) * Real.sin_sq_add_cos_sq φ
  · simp only [mobQ, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.I_re, Complex.I_im, Complex.mul_re]
    ring

theorem mobQ_conj (lam : ℝ) (w : ℂ) : mobQ lam (conj w) = conj (mobQ lam w) := by
  unfold mobQ
  simp only [map_mul, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]

end Dictionary

section Critical

variable {p lam θ : ℝ}

theorem sin_q_eq (p θ : ℝ) :
    Real.sin (p / 2 * θ) =
      Real.sin θ * Real.cos ((1 - p / 2) * θ) - Real.cos θ * Real.sin ((1 - p / 2) * θ) := by
  rw [← Real.sin_sub]; congr 1; ring

/-- (5.3), algebraic core: for `z = r e^{-iθ}`, `Im(v̄ w) = (1-λ) D(θ, r) / |1+z|²`. -/
theorem cross_curveD (p lam θ r : ℝ) :
    (conj (curveV p lam θ) * mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I))).im =
      (1 - lam) * curveD p lam θ r / ‖1 + (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)‖ ^ 2 := by
  obtain ⟨hzr, hzi⟩ := polar_re_im r θ
  obtain ⟨hvr, hvi⟩ := curveV_re_im p lam θ
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, mobW_re, mobW_im, hvr, hvi, hzr, hzi, polar_normSq,
    Complex.sq_norm]
  unfold curveD
  rw [sin_q_eq]
  ring

theorem polar_one_add_ne_zero {r θ : ℝ} (hr : 0 < r) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (1 : ℂ) + (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [Complex.add_im, Complex.one_im, (polar_re_im r θ).2, Complex.zero_im] at this
  have : 0 < r * Real.sin θ := mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ0 hθ)
  linarith

/-- sec5_sharp_inequality.tex l.39-40: for `z = r e^{-iθ}`, `0 < θ < π`, `r > 0`: `w = τ v` with `τ > 0` if and only
if `D(θ, r) = 0`. -/
theorem critical_iff (hp1 : 1 < p) (hp2 : p < 2) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    {r : ℝ} (hr : 0 < r) :
    (∃ τ : ℝ, 0 < τ ∧ mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)) = (τ : ℂ) * curveV p lam θ) ↔
      curveD p lam θ r = 0 := by
  set z := (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) with hzdef
  have hz1 : (1 : ℂ) + z ≠ 0 := polar_one_add_ne_zero hr hθ0 hθ
  have hN : 0 < ‖1 + z‖ ^ 2 := by have := norm_pos_iff.2 hz1; positivity
  have hcross := cross_curveD p lam θ r
  rw [← hzdef] at hcross
  obtain ⟨hvr, hvi⟩ := curveV_re_im p lam θ
  obtain ⟨hs1, -, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  have hl' : 0 < 1 - lam := by linarith
  have hvpos : 0 < (curveV p lam θ).im := by rw [hvi]; exact mul_pos hl' hs1
  constructor
  · rintro ⟨τ, -, hw⟩
    have h0 : (conj (curveV p lam θ) * mobW lam z).im = 0 := by
      rw [hw, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
      ring
    rw [hcross] at h0
    have := (div_eq_zero_iff.1 h0).resolve_right hN.ne'
    exact (mul_eq_zero.1 this).resolve_left hl'.ne'
  · intro hD
    have h0 : (conj (curveV p lam θ) * mobW lam z).im = 0 := by rw [hcross, hD]; simp
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
    have hwi : 0 < (mobW lam z).im := by
      rw [mobW_im_norm, hzdef, (polar_re_im r θ).2, ← hzdef]
      have : 0 < r * Real.sin θ := mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ0 hθ)
      have : 0 < (1 - lam) * (r * Real.sin θ) := mul_pos hl' this
      rw [show -(1 - lam) * -(r * Real.sin θ) = (1 - lam) * (r * Real.sin θ) by ring]
      positivity
    refine ⟨(mobW lam z).im / (curveV p lam θ).im, div_pos hwi hvpos, ?_⟩
    apply Complex.ext
    · rw [Complex.re_ofReal_mul]
      field_simp
      linarith
    · rw [Complex.im_ofReal_mul]
      field_simp

/-- (5.4): at `w = τ v`: `Im Q = (1-λ) Im w = (1-λ)² τ sin δ`, `|w| = τ |v|`, `w - λ w̄ = (1-λ²) τ e^{iδ}`,
`Re[e^{-iδ}(w + λ w̄)] = τ |v|²`; and `v = (1+λ) cos δ + i(1-λ) sin δ`, `|v|² = 1 + λ² + 2λ cos 2δ`; `|Q| sin(arg Q) = Im Q`. -/
theorem curve_identities (p lam θ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    curveV p lam θ = (((1 + lam) * Real.cos ((1 - p / 2) * θ) : ℝ) : ℂ) +
      (((1 - lam) * Real.sin ((1 - p / 2) * θ) : ℝ) : ℂ) * Complex.I ∧
    ‖curveV p lam θ‖ ^ 2 = 1 + lam ^ 2 + 2 * lam * Real.cos (2 * ((1 - p / 2) * θ)) ∧
    (mobQ lam ((τ : ℂ) * curveV p lam θ)).im = (1 - lam) * ((τ : ℂ) * curveV p lam θ).im ∧
    (1 - lam) * ((τ : ℂ) * curveV p lam θ).im = (1 - lam) ^ 2 * τ * Real.sin ((1 - p / 2) * θ) ∧
    ‖(τ : ℂ) * curveV p lam θ‖ = τ * ‖curveV p lam θ‖ ∧
    (τ : ℂ) * curveV p lam θ - lam * conj ((τ : ℂ) * curveV p lam θ) =
      (((1 - lam ^ 2) * τ : ℝ) : ℂ) * Complex.exp ((((1 - p / 2) * θ : ℝ) : ℂ) * Complex.I) ∧
    (Complex.exp (-((((1 - p / 2) * θ : ℝ) : ℂ)) * Complex.I) *
      ((τ : ℂ) * curveV p lam θ + lam * conj ((τ : ℂ) * curveV p lam θ))).re = τ * ‖curveV p lam θ‖ ^ 2 ∧
    ∀ Q : ℂ, ‖Q‖ * Real.sin (Complex.arg Q) = Q.im := by
  obtain ⟨hvr, hvi⟩ := curveV_re_im p lam θ
  set δ := (1 - p / 2) * θ with hδ
  have hv : curveV p lam θ = (((1 + lam) * Real.cos δ : ℝ) : ℂ) + (((1 - lam) * Real.sin δ : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hvr, hvi] <;> ring
  have hnv : ‖curveV p lam θ‖ ^ 2 = 1 + lam ^ 2 + 2 * lam * Real.cos (2 * δ) := by
    rw [Complex.sq_norm, Complex.normSq_apply, hvr, hvi, Real.cos_two_mul]
    linear_combination (1 - lam) ^ 2 * Real.sin_sq_add_cos_sq δ
  have hnv' : ‖curveV p lam θ‖ ^ 2 = ((1 + lam) * Real.cos δ) ^ 2 + ((1 - lam) * Real.sin δ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hvr, hvi]; ring
  have hneg : -((δ : ℂ)) * Complex.I = ((-δ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  refine ⟨hv, hnv, ?_, ?_, ?_, ?_, ?_, Complex.norm_mul_sin_arg⟩
  · simp only [mobQ, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · rw [Complex.im_ofReal_mul, hvi]; ring
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]
  · apply Complex.ext
    · simp only [Complex.sub_re, Complex.mul_re, Complex.im_ofReal_mul, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, hvr, hvi]
      ring
    · simp only [Complex.sub_im, Complex.mul_im, Complex.re_ofReal_mul, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im, hvr, hvi]
      ring
  · rw [hneg, hnv']
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.mul_im, hvr, hvi, Real.cos_neg, Real.sin_neg]
    ring

end Critical

end GKSharp
