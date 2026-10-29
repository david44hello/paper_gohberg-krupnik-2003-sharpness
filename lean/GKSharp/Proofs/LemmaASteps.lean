/- GKSharp/Proofs/LemmaASteps.lean - the paper's own named steps in the proof of Lemma A / A+
(sec5_sharp_inequality.tex l.65-80), each as a proved statement.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.LemmaA

namespace GKSharp

open Real

/-- l.68: `sin δ - (1-q) cos(qθ) sin θ = q sin θ cos(qθ) - cos θ sin(qθ)`, `δ = (1-q)θ`. -/
theorem lemmaA_sin_identity (q θ : ℝ) :
    sin ((1 - q) * θ) - (1 - q) * cos (q * θ) * sin θ = q * sin θ * cos (q * θ) - cos θ * sin (q * θ) := by
  rw [show (1 - q) * θ = θ - q * θ by ring, Real.sin_sub]
  ring

theorem hasDerivAt_tan_div_self {y : ℝ} (hy : y ≠ 0) (hc : cos y ≠ 0) :
    HasDerivAt (fun y => tan y / y) ((1 / cos y ^ 2 * y - tan y * 1) / y ^ 2) y :=
  (Real.hasDerivAt_tan hc).div (hasDerivAt_id y) hy

/-- l.69: `tan y / y` is strictly increasing on `(0, π/2)`. -/
theorem tan_div_self_strictMonoOn : StrictMonoOn (fun y => tan y / y) (Set.Ioo 0 (π / 2)) := by
  have hcos : ∀ y ∈ Set.Ioo 0 (π / 2), 0 < cos y := fun y hy =>
    cos_pos_of_mem_Ioo ⟨by linarith [hy.1, pi_pos], hy.2⟩
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 (π / 2)) (fun y hy =>
    (hasDerivAt_tan_div_self hy.1.ne' (hcos y hy).ne').continuousAt.continuousWithinAt) fun y hy => ?_
  rw [interior_Ioo] at hy
  have hc := hcos y hy
  rw [(hasDerivAt_tan_div_self hy.1.ne' hc.ne').deriv]
  have hsin : sin y * cos y < y := by
    have h2 := Real.sin_lt (by linarith [hy.1] : 0 < 2 * y)
    rw [Real.sin_two_mul] at h2
    linarith
  have hnum : 0 < 1 / cos y ^ 2 * y - tan y * 1 := by
    rw [Real.tan_eq_sin_div_cos, mul_one, div_mul_eq_mul_div, one_mul, sub_pos,
      div_lt_div_iff₀ hc (pow_pos hc 2)]
    nlinarith
  exact div_pos hnum (pow_pos hy.1 2)

/-- l.68-69, the case `θ < π/2`: `tan(qθ)/(qθ) < tan θ/θ` for `0 < q < 1`. -/
theorem tan_div_lt_of_lt {q θ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hθ0 : 0 < θ) (hθ : θ < π / 2) :
    tan (q * θ) / (q * θ) < tan θ / θ :=
  tan_div_self_strictMonoOn ⟨mul_pos hq0 hθ0, (mul_lt_of_lt_one_left hθ0 hq1).trans hθ⟩ ⟨hθ0, hθ⟩
    (mul_lt_of_lt_one_left hθ0 hq1)

/-- l.67: for `λ ≤ 0`, `|v|² ≥ (1+λ)²`. -/
theorem norm_curveV_sq_ge {p lam θ : ℝ} (hl : lam ≤ 0) : (1 + lam) ^ 2 ≤ ‖curveV p lam θ‖ ^ 2 := by
  rw [norm_curveV_sq]
  nlinarith [Real.sin_sq_add_cos_sq ((1 - p / 2) * θ), sq_nonneg (Real.sin ((1 - p / 2) * θ))]

/-- l.72: for `λ < 1`, `|v|² - (1+λ)² cos²δ = (1-λ)² sin²δ`, so `|v|² > (1+λ)² cos²δ` when `sin δ ≠ 0`. -/
theorem norm_curveV_sq_gt {p lam θ : ℝ} (hl1 : lam < 1) (hs : Real.sin ((1 - p / 2) * θ) ≠ 0) :
    (1 + lam) ^ 2 * Real.cos ((1 - p / 2) * θ) ^ 2 < ‖curveV p lam θ‖ ^ 2 := by
  rw [norm_curveV_sq]
  have : 0 < (1 - lam) ^ 2 * Real.sin ((1 - p / 2) * θ) ^ 2 :=
    mul_pos (pow_pos (by linarith) 2) (pow_pos (abs_pos.mpr hs) 2 |>.trans_eq (sq_abs _))
  linarith

/-- l.73: `cos²δ sin δ = (sin δ + sin 3δ)/4`. -/
theorem cos_sq_mul_sin (δ : ℝ) : cos δ ^ 2 * sin δ = (sin δ + sin (3 * δ)) / 4 := by
  rw [Real.sin_three_mul]
  linear_combination sin δ * Real.sin_sq_add_cos_sq δ

/-- l.73: `2 sin θ cos(qθ) = sin((1+q)θ) + sin δ`. -/
theorem two_sin_mul_cos (q θ : ℝ) :
    2 * sin θ * cos (q * θ) = sin ((1 + q) * θ) + sin ((1 - q) * θ) := by
  rw [show (1 + q) * θ = θ + q * θ by ring, show (1 - q) * θ = θ - q * θ by ring, Real.sin_add, Real.sin_sub]
  ring

/-- l.73-74: `sin 3δ - sin((1+q)θ) = -2 cos((2-q)θ) sin((2q-1)θ)`. -/
theorem sin_three_delta_sub (q θ : ℝ) :
    sin (3 * ((1 - q) * θ)) - sin ((1 + q) * θ) = -2 * cos ((2 - q) * θ) * sin ((2 * q - 1) * θ) := by
  rw [Real.sin_sub_sin, show (3 * ((1 - q) * θ) - (1 + q) * θ) / 2 = -((2 * q - 1) * θ) by ring,
    show (3 * ((1 - q) * θ) + (1 + q) * θ) / 2 = (2 - q) * θ by ring, Real.sin_neg]
  ring

/-- l.74-75: `4g = J` with the paper's angles `(2-q)θ` and `(2q-1)θ`. -/
theorem four_g_eq_J_paper (q θ : ℝ) :
    4 * (cos ((1 - q) * θ) ^ 2 * sin ((1 - q) * θ) - (1 - q) * cos (q * θ) * sin θ) =
      2 * (2 * q - 1) * sin θ * cos (q * θ) - 2 * cos ((2 - q) * θ) * sin ((2 * q - 1) * θ) := by
  have h := four_g_eq_J θ (q * θ) q
  rw [show θ - q * θ = (1 - q) * θ by ring, show 2 * θ - q * θ = (2 - q) * θ by ring,
    show 2 * (q * θ) - θ = (2 * q - 1) * θ by ring] at h
  linear_combination h

end GKSharp
