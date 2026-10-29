/- GKSharp/Proofs/CurveK.lean - the two forms of K_f (5.7) and the case lambda = -1 of Theorem C1: R = 1,
B = 4 sin^2(theta/2), Y = 4 cos(theta/2) sin(eps theta/2), K_f = 2^p sin^eps(theta/2)/sin(eps theta/2), and
(ln K_f)' < 0 (sec5_sharp_inequality.tex l.99-100, 169-171).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.CurveK
import GKSharp.Proofs.CurveDict

namespace GKSharp

open ComplexConjugate

section Forms

variable {p lam θ : ℝ}

/-- (5.7), second form: `K_f = 2(1−λ)² sin θ r^{2−q} B^{q−1} / Y`, `r = R(θ)`, `B = |1 + λz_θ|²`,
`Y = 2rs₂ − (1 + r²)s₁`. -/
theorem curveKf_eq (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    curveKf p lam θ =
      2 * (1 - lam) ^ 2 * Real.sin θ * curveR p lam θ ^ (2 - p / 2) *
        (‖1 + (lam : ℂ) * curveZ p lam θ‖ ^ 2) ^ (p / 2 - 1) /
        (2 * curveR p lam θ * Real.sin (p / 2 * θ) - (1 + curveR p lam θ ^ 2) * Real.sin ((1 - p / 2) * θ)) := by
  set r := curveR p lam θ with hr
  obtain ⟨hA, hQ, hρ2, hw, h2τ, -, hYpos⟩ := dict_identities hp1 hp2 hl hl1 hθ0 hθ hr
  obtain ⟨-, -, hR0, -, -⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  rw [← hr] at hR0
  obtain ⟨hs1, -, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
  have hz : curveZ p lam θ = (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) := rfl
  unfold curveKf
  rw [hz]
  set z := (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) with hzdef
  set A := 1 + 2 * r * Real.cos θ + r ^ 2 with hAdef
  set s1 := Real.sin ((1 - p / 2) * θ) with hs1def
  set Y := 2 * r * Real.sin (p / 2 * θ) - (1 + r ^ 2) * s1 with hYdef
  set B := ‖1 + (lam : ℂ) * z‖ ^ 2 with hBdef
  have hApos : 0 < A := by rw [← hA]; exact pow_pos (norm_pos_iff.2 (polar_one_add_ne_zero hR0 hθ0 hθ)) 2
  have hτ0 : 0 < r * Real.sin θ / (A * s1) := div_pos (mul_pos hR0 hsθ) (mul_pos hApos hs1)
  -- |v| > 0 and τ = |w|/|v| is the explicit τ of (5.5)
  have hvpos : 0 < ‖curveV p lam θ‖ := by
    have hvi := (curveV_re_im p lam θ).2
    have : 0 < (curveV p lam θ).im := by rw [hvi]; exact mul_pos (by linarith) hs1
    exact norm_pos_iff.2 (fun h => by rw [h, Complex.zero_im] at this; exact lt_irrefl _ this)
  have hτ : ‖mobW lam z‖ / ‖curveV p lam θ‖ = r * Real.sin θ / (A * s1) := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0, mul_div_assoc, div_self hvpos.ne',
      mul_one]
  rw [hτ, h2τ, hQ]
  have hB0 : 0 ≤ B := by positivity
  have hρ : ‖mobW lam z‖ ^ (p - 2) = B ^ ((p - 2) / 2) / A ^ ((p - 2) / 2) := by
    rw [← sq_rpow_half (norm_nonneg _) (p - 2), hρ2, Real.div_rpow hB0 hApos.le]
  have hl' : 0 < 1 - lam := by linarith
  have hQs : ((1 - lam) ^ 2 * r / A) ^ (1 - p / 2) =
      (1 - lam) ^ (2 - p) * r ^ (1 - p / 2) / A ^ (1 - p / 2) := by
    rw [Real.div_rpow (by positivity) hApos.le, Real.mul_rpow (by positivity) hR0.le,
      show 1 - p / 2 = (2 - p) / 2 by ring, sq_rpow_half hl'.le]
  rw [hρ, hQs]
  have e1 : (1 - lam) ^ p * (1 - lam) ^ (2 - p) = (1 - lam) ^ 2 := by
    rw [← Real.rpow_add hl', show p + (2 - p) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e2 : A ^ ((p - 2) / 2) * A ^ (1 - p / 2) = 1 := by
    rw [← Real.rpow_add hApos, show (p - 2) / 2 + (1 - p / 2) = 0 by ring, Real.rpow_zero]
  have e3 : r ^ (1 - p / 2) * r = r ^ (2 - p / 2) := by
    rw [← Real.rpow_add_one hR0.ne', show 1 - p / 2 + 1 = 2 - p / 2 by ring]
  have e4 : B ^ ((p - 2) / 2) = B ^ (p / 2 - 1) := by rw [show (p - 2) / 2 = p / 2 - 1 by ring]
  have hAe : 0 < A ^ ((p - 2) / 2) := Real.rpow_pos_of_pos hApos _
  have hAf : 0 < A ^ (1 - p / 2) := Real.rpow_pos_of_pos hApos _
  have key : 2 * (1 - lam) ^ p * (B ^ ((p - 2) / 2) / A ^ ((p - 2) / 2)) * (r * Real.sin θ / (A * s1)) *
      ((1 - lam) ^ (2 - p) * r ^ (1 - p / 2) / A ^ (1 - p / 2)) / (Y / (A * s1)) =
      2 * ((1 - lam) ^ p * (1 - lam) ^ (2 - p)) * Real.sin θ * (r ^ (1 - p / 2) * r) * B ^ ((p - 2) / 2) /
        (A ^ ((p - 2) / 2) * A ^ (1 - p / 2)) / Y := by
    field_simp
  rw [key, e1, e2, e3, e4, div_one]

end Forms

section MinusOne

variable {p θ : ℝ}

theorem cot_lt_cot {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.pi) : Real.cot b < Real.cot a := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith)
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi (by linarith) hb
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, div_lt_div_iff₀ hsb hsa]
  have h : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [Real.sin_sub] at h
  linarith

/-- Proof of Theorem C1, sec5_sharp_inequality.tex l.169-171 (`λ = −1`): "R ≡ 1, B = 4 sin²(θ/2),
Y = 4 cos(θ/2) sin(εθ/2), and (5.7) gives K_f = 2^p sin^ε(θ/2)/sin(εθ/2)", `ε = p − 1`. -/
theorem curveKf_minus_one (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    curveR p (-1) θ = 1 ∧
    ‖1 + ((-1 : ℝ) : ℂ) * curveZ p (-1) θ‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 ∧
    2 * curveR p (-1) θ * Real.sin (p / 2 * θ) - (1 + curveR p (-1) θ ^ 2) * Real.sin ((1 - p / 2) * θ) =
      4 * Real.cos (θ / 2) * Real.sin ((p - 1) * θ / 2) ∧
    curveKf p (-1) θ = 2 ^ p * Real.sin (θ / 2) ^ (p - 1) / Real.sin ((p - 1) * θ / 2) := by
  obtain ⟨-, hR⟩ := curve_root_minus_one hp1 hp2 hθ0 hθ
  obtain ⟨hs1, -, hid⟩ := curve_sines hp1 hp2 hθ0 hθ
  have hsh : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hch : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hse : 0 < Real.sin ((p - 1) * θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith [Real.pi_pos])
  have hB : ‖1 + ((-1 : ℝ) : ℂ) * curveZ p (-1) θ‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    have hz : curveZ p (-1) θ = ((1 : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) := by
      unfold curveZ; rw [hR]
    obtain ⟨hzr, hzi⟩ := polar_re_im 1 θ
    rw [hz, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, hzr, hzi]
    have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have h1 := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at h1
      have h2 := Real.sin_sq_add_cos_sq (θ / 2)
      linarith
    have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      have h := Real.sin_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at h
      exact h
    rw [hc, hs]
    linear_combination 4 * Real.sin (θ / 2) ^ 2 * Real.sin_sq_add_cos_sq (θ / 2)
  have hY : 2 * curveR p (-1) θ * Real.sin (p / 2 * θ) - (1 + curveR p (-1) θ ^ 2) * Real.sin ((1 - p / 2) * θ) =
      4 * Real.cos (θ / 2) * Real.sin ((p - 1) * θ / 2) := by
    rw [hR]; linear_combination 2 * hid
  refine ⟨hR, hB, hY, ?_⟩
  rw [curveKf_eq hp1 hp2 le_rfl (by norm_num) hθ0 hθ, hY, hB, hR, Real.one_rpow]
  have hsθ : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [hsθ, Real.mul_rpow (by norm_num) (by positivity), show p / 2 - 1 = (p - 2) / 2 by ring,
    sq_rpow_half hsh.le (p - 2)]
  have h4 : (4 : ℝ) * (4 : ℝ) ^ ((p - 2) / 2) = 2 ^ p := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sq_rpow_half (by norm_num) (p - 2),
      show (2 : ℝ) ^ 2 = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_add (by norm_num)]
    congr 1; ring
  have h5 : Real.sin (θ / 2) * Real.sin (θ / 2) ^ (p - 2) = Real.sin (θ / 2) ^ (p - 1) := by
    rw [mul_comm, ← Real.rpow_add_one hsh.ne', show p - 2 + 1 = p - 1 by ring]
  rw [← h4, ← h5]
  have hch' := hch.ne'
  have hse' := hse.ne'
  field_simp
  ring

/-- `log K_f` at `λ = −1`, as an explicit function on `(0, π)`. -/
theorem log_curveKf_minus_one (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    Real.log (curveKf p (-1) θ) =
      p * Real.log 2 + (p - 1) * Real.log (Real.sin (θ / 2)) - Real.log (Real.sin ((p - 1) * θ / 2)) := by
  have hsh : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hse : 0 < Real.sin ((p - 1) * θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith [Real.pi_pos])
  rw [(curveKf_minus_one hp1 hp2 hθ0 hθ).2.2.2, Real.log_div (by positivity) hse.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num), Real.log_rpow hsh]

/-- Proof of Theorem C1, sec5_sharp_inequality.tex l.171 (`λ = −1`): "(ln K_f)′ = (ε/2)[cot(θ/2) − cot(εθ/2)] < 0";
so `K_f` is strictly decreasing on `(0, π)`. -/
theorem curveKf_minus_one_deriv (hp1 : 1 < p) (hp2 : p < 2) :
    (∀ θ, 0 < θ → θ < Real.pi →
      HasDerivAt (fun x => Real.log (curveKf p (-1) x))
        ((p - 1) / 2 * (Real.cot (θ / 2) - Real.cot ((p - 1) * θ / 2))) θ ∧
      (p - 1) / 2 * (Real.cot (θ / 2) - Real.cot ((p - 1) * θ / 2)) < 0) ∧
    StrictAntiOn (curveKf p (-1)) (Set.Ioo 0 Real.pi) := by
  have hderiv : ∀ θ, 0 < θ → θ < Real.pi →
      HasDerivAt (fun x => Real.log (curveKf p (-1) x))
        ((p - 1) / 2 * (Real.cot (θ / 2) - Real.cot ((p - 1) * θ / 2))) θ := by
    intro θ hθ0 hθ
    have hsh : Real.sin (θ / 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
    have hse : Real.sin ((p - 1) * θ / 2) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith [Real.pi_pos])).ne'
    have h1 := (((hasDerivAt_id' θ).div_const 2).sin).log hsh
    have h2 := ((((hasDerivAt_id' θ).const_mul (p - 1)).div_const 2).sin).log hse
    have h := ((h1.const_mul (p - 1)).const_add (p * Real.log 2)).sub h2
    have heq : (fun x => Real.log (curveKf p (-1) x)) =ᶠ[nhds θ]
        (fun x => p * Real.log 2 + (p - 1) * Real.log (Real.sin (x / 2)) - Real.log (Real.sin ((p - 1) * x / 2))) := by
      filter_upwards [Ioo_mem_nhds hθ0 hθ] with x hx
      exact log_curveKf_minus_one hp1 hp2 hx.1 hx.2
    refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
    ring
  have hneg : ∀ θ, 0 < θ → θ < Real.pi →
      (p - 1) / 2 * (Real.cot (θ / 2) - Real.cot ((p - 1) * θ / 2)) < 0 := by
    intro θ hθ0 hθ
    have hc := cot_lt_cot (a := (p - 1) * θ / 2) (b := θ / 2) (by nlinarith) (by nlinarith) (by linarith)
    have : 0 < (p - 1) / 2 := by linarith
    nlinarith
  refine ⟨fun θ h0 h1 => ⟨hderiv θ h0 h1, hneg θ h0 h1⟩, ?_⟩
  have hlog : StrictAntiOn (fun x => Real.log (curveKf p (-1) x)) (Set.Ioo 0 Real.pi) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 Real.pi)
    · exact fun x hx => (hderiv x hx.1 hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(hderiv x hx.1 hx.2).deriv]
      exact hneg x hx.1 hx.2
  intro x hx y hy hxy
  have hpos : ∀ t ∈ Set.Ioo 0 Real.pi, 0 < curveKf p (-1) t := by
    intro t ht
    rw [(curveKf_minus_one hp1 hp2 ht.1 ht.2).2.2.2]
    have hsh : 0 < Real.sin (t / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
    have hse : 0 < Real.sin ((p - 1) * t / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith [ht.1]) (by nlinarith [ht.2, Real.pi_pos])
    positivity
  exact (Real.log_lt_log_iff (hpos y hy) (hpos x hx)).1 (hlog hx hy hxy)

end MinusOne

end GKSharp
