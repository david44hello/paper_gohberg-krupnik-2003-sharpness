/- GKSharp/Proofs/LemmaA.lean - the scalar core of Lemma A / A+ (sec5_sharp_inequality.tex l.57-80): the bracket of
(5.6) is negative for 1 < p < 2, -1 ≤ λ < 1, 0 < θ < π.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MobiusDict

namespace GKSharp

open Real

/-! ## Two trigonometric identities (polynomial identities in `sin a, cos a, sin b, cos b`) -/

/-- Paper l.75-77: with `δ = a - b` (`a = θ`, `b = qθ`), `4(cos²δ sin δ - (1-q) cos b sin a) = J`. -/
theorem four_g_eq_J (a b q : ℝ) :
    4 * (cos (a - b) ^ 2 * sin (a - b) - (1 - q) * cos b * sin a) =
      2 * (2 * q - 1) * (sin a * cos b) - 2 * (cos (2 * a - b) * sin (2 * b - a)) := by
  simp only [Real.sin_sub, Real.cos_sub, Real.sin_two_mul, Real.cos_two_mul]
  linear_combination (-4 * sin b * (cos a * sin b ^ 2 - cos a - cos b * sin a * sin b)) * Real.sin_sq_add_cos_sq a
    + (4 * (cos a - 1) * (cos a + 1) * (cos a * sin b - cos b * sin a)) * Real.sin_sq_add_cos_sq b

/-- Paper l.79: the derivative of `J` (chain rule form, left) equals `(1-q)[2(2q-1) sin θ sin qθ + 6 sin((2-q)θ) sin((2q-1)θ)]`. -/
theorem Jderiv_eq (a b q : ℝ) :
    2 * (2 * q - 1) * (cos a * cos b - q * (sin a * sin b)) + 2 * (2 - q) * (sin (2 * a - b) * sin (2 * b - a))
      - 2 * (2 * q - 1) * (cos (2 * a - b) * cos (2 * b - a)) =
    (1 - q) * (2 * (2 * q - 1) * (sin a * sin b) + 6 * (sin (2 * a - b) * sin (2 * b - a))) := by
  simp only [Real.sin_sub, Real.cos_sub, Real.sin_two_mul, Real.cos_two_mul]
  linear_combination (-4 * cos a * cos b * (2 * q - 1) * (2 * cos b ^ 2 + 2 * sin b ^ 2 - 1)) * Real.sin_sq_add_cos_sq a
    + (-4 * cos a * cos b * (2 * q - 1)) * Real.sin_sq_add_cos_sq b

/-! ## Case `λ ≤ 0`: `h(θ) = q sin θ cos qθ - cos θ sin qθ > 0` on `(0, π)` -/

theorem hasDerivAt_hfun (q x : ℝ) :
    HasDerivAt (fun x => q * (sin x * cos (q * x)) - cos x * sin (q * x))
      ((1 - q ^ 2) * (sin x * sin (q * x))) x := by
  have hb : HasDerivAt (fun x => q * x) q x := by simpa using (hasDerivAt_id x).const_mul q
  have H := (((Real.hasDerivAt_sin x).mul hb.cos).const_mul q).sub ((Real.hasDerivAt_cos x).mul hb.sin)
  refine H.congr_deriv ?_
  ring

/-- `h(0) = 0` and `h' = (1 - q²) sin θ sin qθ > 0` on `(0, π)` (this replaces "tan y / y increases"). -/
theorem hfun_pos {q θ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hθ0 : 0 < θ) (hθ : θ < π) :
    0 < q * (sin θ * cos (q * θ)) - cos θ * sin (q * θ) := by
  have hmono : StrictMonoOn (fun x => q * (sin x * cos (q * x)) - cos x * sin (q * x)) (Set.Icc 0 π) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 π)
      (fun x _ => (hasDerivAt_hfun q x).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hasDerivAt_hfun q x).deriv]
    have h1 : 0 < sin x := sin_pos_of_pos_of_lt_pi hx.1 hx.2
    have h2 : 0 < sin (q * x) :=
      sin_pos_of_pos_of_lt_pi (mul_pos hq0 hx.1) ((mul_lt_of_lt_one_left hx.1 hq1).trans hx.2)
    have h3 : 0 < 1 - q ^ 2 := by nlinarith
    exact mul_pos h3 (mul_pos h1 h2)
  have h := hmono ⟨le_refl 0, pi_pos.le⟩ ⟨hθ0.le, hθ.le⟩ hθ0
  simpa using h

/-! ## Case `λ > 0`: `g = cos²δ sin δ - (1-q) cos qθ sin θ ≥ 0` on `(0, π)`, `1/2 < q < 1` -/

theorem hasDerivAt_Jfun (q x : ℝ) :
    HasDerivAt
      (fun x => 2 * (2 * q - 1) * (sin x * cos (q * x)) - 2 * (cos (2 * x - q * x) * sin (2 * (q * x) - x)))
      ((1 - q) * (2 * (2 * q - 1) * (sin x * sin (q * x)) + 6 * (sin (2 * x - q * x) * sin (2 * (q * x) - x))))
      x := by
  have hb : HasDerivAt (fun x => q * x) q x := by simpa using (hasDerivAt_id x).const_mul q
  have hc : HasDerivAt (fun x => 2 * x - q * x) (2 - q) x := by
    convert (hasDerivAt_id x).const_mul (2 - q) using 1
    · ext y
      simp only [id]
      ring
    · ring
  have hs : HasDerivAt (fun x => 2 * (q * x) - x) (2 * q - 1) x := by
    convert (hasDerivAt_id x).const_mul (2 * q - 1) using 1
    · ext y
      simp only [id]
      ring
    · ring
  have H := (((Real.hasDerivAt_sin x).mul hb.cos).const_mul (2 * (2 * q - 1))).sub
    ((hc.cos.mul hs.sin).const_mul 2)
  refine H.congr_deriv ?_
  linear_combination Jderiv_eq x (q * x) q

/-- `J > 0` on `(0, π/(2(2-q))]`: `J(0) = 0` and `J' > 0` there (all angles in `(0, π)`). -/
theorem Jfun_pos_small {q θ : ℝ} (hq1 : 1 / 2 < q) (hq2 : q < 1) (hθ0 : 0 < θ)
    (hθ : θ ≤ π / (2 * (2 - q))) :
    0 < 2 * (2 * q - 1) * (sin θ * cos (q * θ)) - 2 * (cos (2 * θ - q * θ) * sin (2 * (q * θ) - θ)) := by
  set T := π / (2 * (2 - q)) with hTdef
  have h2q : 0 < 2 - q := by linarith
  have hT : (2 - q) * T = π / 2 := by rw [hTdef]; field_simp
  have hTpi : T < π := by
    rw [hTdef, div_lt_iff₀ (by positivity)]
    nlinarith [pi_pos]
  have hmono : StrictMonoOn
      (fun x => 2 * (2 * q - 1) * (sin x * cos (q * x)) - 2 * (cos (2 * x - q * x) * sin (2 * (q * x) - x)))
      (Set.Icc 0 T) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 T)
      (fun x _ => (hasDerivAt_Jfun q x).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hasDerivAt_Jfun q x).deriv]
    obtain ⟨hx0, hxT⟩ := hx
    have hxpi : x < π := hxT.trans hTpi
    have hqx : q * x < x := mul_lt_of_lt_one_left hx0 hq2
    have h1 : 0 < sin x := sin_pos_of_pos_of_lt_pi hx0 hxpi
    have h2 : 0 < sin (q * x) := sin_pos_of_pos_of_lt_pi (by nlinarith) (hqx.trans hxpi)
    have h3 : 0 < sin (2 * x - q * x) := by
      refine sin_pos_of_pos_of_lt_pi (by nlinarith) ?_
      have : (2 - q) * x < (2 - q) * T := mul_lt_mul_of_pos_left hxT h2q
      nlinarith [pi_pos]
    have h4 : 0 < sin (2 * (q * x) - x) := sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
    have h5 : 0 < 2 * q - 1 := by linarith
    have h6 : 0 < 1 - q := by linarith
    positivity
  have h := hmono ⟨le_refl 0, by positivity⟩ ⟨hθ0.le, hθ⟩ hθ0
  simpa using h

/-- Paper l.76-79: `g ≥ 0` for `1/2 < q < 1`, `0 < θ < π` (via `4g = J`). -/
theorem gfun_nonneg {q θ : ℝ} (hq1 : 1 / 2 < q) (hq2 : q < 1) (hθ0 : 0 < θ) (hθ : θ < π) :
    0 ≤ cos ((1 - q) * θ) ^ 2 * sin ((1 - q) * θ) - (1 - q) * cos (q * θ) * sin θ := by
  have hq0 : 0 < q := by linarith
  have hδ : (1 - q) * θ = θ - q * θ := by ring
  have h4 := four_g_eq_J θ (q * θ) q
  rw [hδ]
  have hqθ : q * θ < θ := mul_lt_of_lt_one_left hθ0 hq2
  have hsθ : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ0 hθ
  have hqθ0 : 0 < q * θ := mul_pos hq0 hθ0
  have hsδ : 0 < sin (θ - q * θ) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  by_cases h0 : π / (2 * q) ≤ θ
  · -- `qθ ∈ [π/2, π)`: `cos qθ ≤ 0`
    rw [div_le_iff₀ (by positivity)] at h0
    have hc : cos (q * θ) ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le (by nlinarith) (by linarith [pi_pos])
    have hA : 0 ≤ cos (θ - q * θ) ^ 2 * sin (θ - q * θ) := mul_nonneg (sq_nonneg _) hsδ.le
    have hB : (1 - q) * cos (q * θ) * sin θ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) hc) hsθ.le
    linarith
  · rw [not_le, lt_div_iff₀ (by positivity)] at h0
    have hJ : 0 < 2 * (2 * q - 1) * (sin θ * cos (q * θ)) - 2 * (cos (2 * θ - q * θ) * sin (2 * (q * θ) - θ)) := by
      by_cases h1 : θ ≤ π / (2 * (2 - q))
      · exact Jfun_pos_small hq1 hq2 hθ0 h1
      · -- `(2-q)θ ∈ [π/2, 3π/2)`: both terms of `J` are `≥ 0`, the first `> 0`
        rw [not_le, div_lt_iff₀ (by nlinarith)] at h1
        have hcq : 0 < cos (q * θ) := cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], by nlinarith⟩
        have hsum : 2 * θ - q * θ ≤ π + π / 2 := by nlinarith
        have hC : cos (2 * θ - q * θ) ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le (by nlinarith) hsum
        have hS : 0 < sin (2 * (q * θ) - θ) := sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
        have hP : 0 < (2 * q - 1) * (sin θ * cos (q * θ)) := mul_pos (by linarith) (mul_pos hsθ hcq)
        have hN : 0 ≤ -cos (2 * θ - q * θ) * sin (2 * (q * θ) - θ) := mul_nonneg (by linarith) hS.le
        linarith
    linarith

/-! ## Lemma A / A+: the bracket of (5.6) is negative -/

theorem norm_curveV_sq (p lam θ : ℝ) :
    ‖curveV p lam θ‖ ^ 2 =
      (1 + lam) ^ 2 * cos ((1 - p / 2) * θ) ^ 2 + (1 - lam) ^ 2 * sin ((1 - p / 2) * θ) ^ 2 := by
  obtain ⟨hre, him⟩ := curveV_re_im p lam θ
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  ring

/-- Lemma A (`λ ≤ 0`) and A+ (`λ > 0`), sec5_sharp_inequality.tex l.57-80, the bracket of (5.6):
`(1-q)(1+λ)² cos(qθ) - |v|² sin δ / sin θ < 0` with `q = p/2`, `δ = (1-q)θ`. -/
theorem lemmaA_bracket {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (1 - p / 2) * (1 + lam) ^ 2 * Real.cos (p / 2 * θ) -
      ‖curveV p lam θ‖ ^ 2 * (Real.sin ((1 - p / 2) * θ) / Real.sin θ) < 0 := by
  have hsθ : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ0 hθ
  have hsδ : 0 < sin ((1 - p / 2) * θ) :=
    sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  rw [sub_neg, ← mul_div_assoc, lt_div_iff₀ hsθ, norm_curveV_sq]
  set s := sin ((1 - p / 2) * θ) with hs
  set c := cos ((1 - p / 2) * θ) with hc
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  rcases le_or_gt lam 0 with hl0 | hl0
  · -- `λ ≤ 0`: `(1-q) cos qθ sin θ < sin δ` and `(1+λ)² ≤ |v|²`
    have hh := hfun_pos (q := p / 2) (by linarith) (by linarith) hθ0 hθ
    have hX : (1 - p / 2) * cos (p / 2 * θ) * sin θ < s := by
      have e : s = sin θ * cos (p / 2 * θ) - cos θ * sin (p / 2 * θ) := by
        rw [hs, show (1 - p / 2) * θ = θ - p / 2 * θ by ring, Real.sin_sub]
      rw [e]
      linarith
    have hV : (1 + lam) ^ 2 ≤ (1 + lam) ^ 2 * c ^ 2 + (1 - lam) ^ 2 * s ^ 2 := by
      nlinarith [sq_nonneg s]
    rcases eq_or_lt_of_le hl with he | hgt
    · subst he
      nlinarith [sq_pos_of_pos hsδ]
    · have hpos : 0 < (1 + lam) ^ 2 := pow_pos (by linarith) 2
      calc (1 - p / 2) * (1 + lam) ^ 2 * cos (p / 2 * θ) * sin θ
          = (1 + lam) ^ 2 * ((1 - p / 2) * cos (p / 2 * θ) * sin θ) := by ring
        _ < (1 + lam) ^ 2 * s := mul_lt_mul_of_pos_left hX hpos
        _ ≤ ((1 + lam) ^ 2 * c ^ 2 + (1 - lam) ^ 2 * s ^ 2) * s := mul_le_mul_of_nonneg_right hV hsδ.le
  · -- `λ > 0`: `|v|² > (1+λ)² cos²δ` and `g ≥ 0`
    have hg := gfun_nonneg (q := p / 2) (by linarith) (by linarith) hθ0 hθ
    rw [← hs, ← hc] at hg
    have hsq : 0 < (1 - lam) ^ 2 * s ^ 2 * s := by
      have : 0 < 1 - lam := by linarith
      positivity
    calc (1 - p / 2) * (1 + lam) ^ 2 * cos (p / 2 * θ) * sin θ
        = (1 + lam) ^ 2 * ((1 - p / 2) * cos (p / 2 * θ) * sin θ) := by ring
      _ ≤ (1 + lam) ^ 2 * (c ^ 2 * s) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
      _ < ((1 + lam) ^ 2 * c ^ 2 + (1 - lam) ^ 2 * s ^ 2) * s := by nlinarith

end GKSharp
