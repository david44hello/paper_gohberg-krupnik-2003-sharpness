/-
GKSharp/Proofs/Q15Monotone.lean — paper 019 short v1.80, sec5d_monotone.tex l.13, 27, 28 (the Q15 routes of Lemma 5.4):
proofs of the rows q15_sec5d_substitutions, q15_sec5d_cleared and q15_sec5d_Pi_coefficients.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Route: (5.9) (row sec5d_eq_5_10) and the γ-form of R (row sec5d_gamma_spec) give the three substitutions; the literal
partial derivatives (mono_log_partials) and four product-to-sum identities give the cleared expressions; the
coefficient identity is polynomial algebra modulo sin² + cos² = 1.
-/
import GKSharp.Proofs.MonotoneGamma
import GKSharp.Proofs.MonotonePartials

namespace GKSharp.Proofs.Q15Monotone

open Set

/-- `sin(x + y) cos(x − y) = (sin 2x + sin 2y)/2`. -/
private lemma sin_add_mul_cos_sub (x y : ℝ) :
    Real.sin (x + y) * Real.cos (x - y) = (Real.sin (2 * x) + Real.sin (2 * y)) / 2 := by
  rw [Real.sin_add, Real.cos_sub, Real.sin_two_mul, Real.sin_two_mul]
  linear_combination (Real.sin x * Real.cos x) * Real.sin_sq_add_cos_sq y +
    (Real.sin y * Real.cos y) * Real.sin_sq_add_cos_sq x

/-- `sin(x − y) cos(x + y) = (sin 2x − sin 2y)/2`. -/
private lemma sin_sub_mul_cos_add (x y : ℝ) :
    Real.sin (x - y) * Real.cos (x + y) = (Real.sin (2 * x) - Real.sin (2 * y)) / 2 := by
  rw [Real.sin_sub, Real.cos_add, Real.sin_two_mul, Real.sin_two_mul]
  linear_combination (Real.sin x * Real.cos x) * Real.sin_sq_add_cos_sq y -
    (Real.sin y * Real.cos y) * Real.sin_sq_add_cos_sq x

/-- `sin(x − y) sin(x + y) = (cos 2y − cos 2x)/2`. -/
private lemma sin_sub_mul_sin_add (x y : ℝ) :
    Real.sin (x - y) * Real.sin (x + y) = (Real.cos (2 * y) - Real.cos (2 * x)) / 2 := by
  rw [Real.sin_sub, Real.sin_add, Real.cos_two_mul, Real.cos_two_mul]
  linear_combination Real.cos y ^ 2 * Real.sin_sq_add_cos_sq x - Real.cos x ^ 2 * Real.sin_sq_add_cos_sq y

/-- `sin²(x + y) − 2 sin(x − y) sin(x + y) cos 2y + sin²(x − y) = sin² 2y`. -/
private lemma sin_sq_combination (x y : ℝ) :
    Real.sin (x + y) ^ 2 - 2 * Real.sin (x - y) * Real.sin (x + y) * Real.cos (2 * y) + Real.sin (x - y) ^ 2 =
      Real.sin (2 * y) ^ 2 := by
  rw [Real.sin_add, Real.sin_sub, Real.cos_two_mul, Real.sin_two_mul]
  linear_combination (-4 * Real.cos y ^ 2 * (Real.cos y ^ 2 - 1)) * Real.sin_sq_add_cos_sq x +
    (4 * Real.cos y ^ 2 * (Real.cos x ^ 2 - 1)) * Real.sin_sq_add_cos_sq y

/-- The positive sines of Section 5.4: `0 < b < a < π/2`, `b < γ < π/2`. -/
private lemma sec5d_sines {a b g : ℝ} (hb0 : 0 < b) (hba : b < a) (ha : a < Real.pi / 2)
    (hg1 : b < g) (hg2 : g < Real.pi / 2) :
    0 < Real.sin (g - b) ∧ 0 < Real.sin (g + b) ∧ 0 < Real.sin (g + a) ∧ 0 < Real.sin (2 * a) ∧
      0 < Real.sin (2 * b) := by
  have hpi := Real.pi_pos
  refine ⟨Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)⟩

/-- `‖1 + λ r e^{−iθ}‖² = 1 + 2λr cos θ + (λr)²`. -/
private lemma norm_sq_one_add (lam r θ : ℝ) :
    ‖(1 : ℂ) + (lam : ℂ) * ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I))‖ ^ 2 =
      1 + 2 * (lam * r) * Real.cos θ + (lam * r) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.exp_re, Complex.exp_im]
  linear_combination (lam * r) ^ 2 * Real.sin_sq_add_cos_sq θ

/-- sec5d l.13 (`a = θ/2`, `b = εa`, `γ` of (5.9), `r = R(θ)`): `λr = −sin(γ − a)/sin(γ + a)`,
`s₂ − rs₁ = sin(γ + a) sin 2b/sin(γ + b)`, `|1 + λz_θ| = sin 2a/sin(γ + a)`, the right side positive. -/
theorem q15_sec5d_substitutions_proved {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    let a := θ / 2
    let b := (p - 1) * (θ / 2)
    let γ := curveGamma p lam θ
    let r := curveR p lam θ
    lam * r = -(Real.sin (γ - a) / Real.sin (γ + a)) ∧
    Real.sin (p / 2 * θ) - r * Real.sin ((1 - p / 2) * θ) =
      Real.sin (γ + a) * Real.sin (2 * b) / Real.sin (γ + b) ∧
    ‖1 + (lam : ℂ) * curveZ p lam θ‖ = Real.sin (2 * a) / Real.sin (γ + a) ∧
    0 < Real.sin (2 * a) / Real.sin (γ + a) := by
  dsimp only
  obtain ⟨hg1, hg2, hR, -⟩ := sec5d_gamma_spec_proved hp1 hp2 hl hl1 hθ0 hθ
  have hroot := (curve_root_unique hp1 hp2 hθ0 hθ hl hl1).2.2.2.2.2.2.2.1
  rw [hR] at hroot
  have hmu := (sec5d_eq_5_10_proved p lam θ (curveGamma p lam θ) ⟨hp1, hp2⟩ ⟨hl, hl1⟩ ⟨hθ0, hθ⟩
    ⟨hg1, hg2⟩).mp hroot
  have hn := norm_sq_one_add lam (curveR p lam θ) θ
  have hθa : θ = 2 * (θ / 2) := by ring
  have hZ : curveZ p lam θ = (curveR p lam θ : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) := rfl
  set a := θ / 2 with ha_def
  set b := (p - 1) * a with hb_def
  set γ := curveGamma p lam θ with hγ_def
  set r := curveR p lam θ with hr_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hb0 : 0 < b := by rw [hb_def]; exact mul_pos (by linarith) ha0
  have hba : b < a := by rw [hb_def]; nlinarith
  have ha : a < Real.pi / 2 := by rw [ha_def]; linarith
  obtain ⟨hMb, hPb, hPa, h2a, h2b⟩ := sec5d_sines hb0 hba ha hg1 hg2
  have hlam : lam = -(Real.sin (γ - a) * Real.sin (γ + b) / (Real.sin (γ + a) * Real.sin (γ - b))) := by
    linarith
  have hMb' := hMb.ne'
  have hPb' := hPb.ne'
  have hPa' := hPa.ne'
  have hlr : lam * r = -(Real.sin (γ - a) / Real.sin (γ + a)) := by
    rw [hR, hlam]
    field_simp
  have hpos : 0 < Real.sin (2 * a) / Real.sin (γ + a) := div_pos h2a hPa
  refine ⟨hlr, ?_, ?_, hpos⟩
  · rw [hR, show p / 2 * θ = a + b by rw [hb_def, ha_def]; ring,
      show (1 - p / 2) * θ = a - b by rw [hb_def, ha_def]; ring, Real.sin_two_mul b]
    field_simp
    simp only [Real.sin_add, Real.sin_sub]
    ring
  · have hsq : ‖1 + (lam : ℂ) * curveZ p lam θ‖ ^ 2 = (Real.sin (2 * a) / Real.sin (γ + a)) ^ 2 := by
      rw [hZ, hn, hlr, hθa, div_pow, eq_div_iff (pow_ne_zero 2 hPa')]
      calc (1 + 2 * -(Real.sin (γ - a) / Real.sin (γ + a)) * Real.cos (2 * a) +
              (-(Real.sin (γ - a) / Real.sin (γ + a))) ^ 2) * Real.sin (γ + a) ^ 2
          = Real.sin (γ + a) ^ 2 - 2 * Real.sin (γ - a) * Real.sin (γ + a) * Real.cos (2 * a) +
              Real.sin (γ - a) ^ 2 := by
            field_simp
            ring
        _ = Real.sin (2 * a) ^ 2 := sin_sq_combination γ a
    calc ‖1 + (lam : ℂ) * curveZ p lam θ‖ = Real.sqrt (‖1 + (lam : ℂ) * curveZ p lam θ‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt ((Real.sin (2 * a) / Real.sin (γ + a)) ^ 2) := by rw [hsq]
      _ = Real.sin (2 * a) / Real.sin (γ + a) := Real.sqrt_sq hpos.le

/-- The four cleared expressions from the four values `S·cot(γ ∓ a)`, `S·cot(γ ∓ b)`. -/
private lemma cleared_algebra {ε q U V sa sb s cma cpa cmb cpb ka kb N S : ℝ}
    (hq : 2 * q - 1 = ε) (hN : N = sa * V - sb * U) (hS : S = U * V)
    (h1 : S * cma = V * (s + sa) / 2) (h2 : S * cpa = V * (s - sa) / 2)
    (h3 : S * cmb = U * (s + sb) / 2) (h4 : S * cpb = U * (s - sb) / 2) :
    S * (cma + cpb - cpa - cmb) = N ∧
    S * (-cma + ε * cpb - cpa + ε * cmb) = (ε * U - V) * s ∧
    S * ((1 - q) * cmb + q * cpb - ε * cpa) = ((U - ε * V) * s + ε * N) / 2 ∧
    S * (ε * (q * cpb - (1 - q) * cmb - cpa + 2 * ka - 2 * kb)) =
      ε / 2 * ((ε * U - V) * s + N) + 2 * ε * U * V * (ka - kb) := by
  refine ⟨by linear_combination h1 + h4 - h2 - h3 - hN, by linear_combination -h1 + ε * h4 - h2 + ε * h3,
    by linear_combination (1 - q) * h3 + q * h4 - ε * h2 - ε / 2 * hN - U * sb / 2 * hq,
    by linear_combination ε * q * h4 - ε * (1 - q) * h3 - ε * h2 + 2 * ε * (ka - kb) * hS - ε / 2 * hN +
      ε * U * s / 2 * hq⟩

/-- `ES` from the cleared expressions, the mixed terms cancelling and `sin² 2γ = 1 − X²`. -/
private lemma es_algebra {ε U V N S s X ka kb La Lg Ma Mg E : ℝ} (hS : S = U * V) (hU : U ≠ 0) (hV : V ≠ 0)
    (hE : E = La * Mg - Lg * Ma) (cMg : S * Mg = N) (cMa : S * Ma = (ε * U - V) * s)
    (cLg : S * Lg = ((U - ε * V) * s + ε * N) / 2)
    (cLa : S * La = ε / 2 * ((ε * U - V) * s + N) + 2 * ε * U * V * (ka - kb)) (hs : s ^ 2 + X ^ 2 = 1) :
    E * S = (ε * N ^ 2 - (U - ε * V) * (ε * U - V) * (1 - X ^ 2)) / (2 * U * V) + 2 * ε * (ka - kb) * N := by
  have hS0 : S ≠ 0 := by rw [hS]; exact mul_ne_zero hU hV
  have h1 : E * S = ((S * La) * (S * Mg) - (S * Lg) * (S * Ma)) / S := by
    rw [hE, eq_div_iff hS0]
    ring
  rw [h1, cLa, cMg, cLg, cMa, hS, div_add' _ _ _ (mul_ne_zero (mul_ne_zero two_ne_zero hU) hV),
    div_eq_div_iff (mul_ne_zero hU hV) (mul_ne_zero (mul_ne_zero two_ne_zero hU) hV)]
  linear_combination (-(U * V) * ((U - ε * V) * (ε * U - V))) * hs

/-- sec5d l.27 (`ε = p − 1`, `q = p/2`, `b = εa`, `X = cos 2γ`, at any `γ ∈ (b, π/2)`, `γ ≠ a`, i.e. `λ ≠ 0`; `L_a`, `L_γ`,
`M_a`, `M_γ` the actual partial derivatives): `U = sin(γ−a) sin(γ+a) = (cos 2a − X)/2`,
`V = sin(γ−b) sin(γ+b) = (cos 2b − X)/2`, `N = sin 2a V − sin 2b U`, `S = UV`; `SM_γ = N`, `SM_a = (εU − V) sin 2γ`,
`SL_γ = ½[(U − εV) sin 2γ + εN]`, `SL_a = (ε/2)[(εU − V) sin 2γ + N] + 2εUV(cot 2a − cot 2b)`,
`S²E = (SL_a)(SM_γ) − (SL_γ)(SM_a)`, and
`ES = [εN² − (U − εV)(εU − V)(1 − X²)]/(2UV) + 2ε(cot 2a − cot 2b)N`. -/
theorem q15_sec5d_cleared_proved {p a g : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ha0 : 0 < a) (ha : a < Real.pi / 2)
    (hg : (p - 1) * a < g ∧ g < Real.pi / 2) (hga : g ≠ a) :
    let ε := p - 1
    let b := (p - 1) * a
    let X := Real.cos (2 * g)
    let U := Real.sin (g - a) * Real.sin (g + a)
    let V := Real.sin (g - b) * Real.sin (g + b)
    let N := Real.sin (2 * a) * V - Real.sin (2 * b) * U
    let S := U * V
    U = (Real.cos (2 * a) - X) / 2 ∧ V = (Real.cos (2 * b) - X) / 2 ∧ S = monoS p a g ∧
    S * deriv (monoLogM p a) g = N ∧
    S * deriv (fun x => monoLogM p x g) a = (ε * U - V) * Real.sin (2 * g) ∧
    S * deriv (monoLogL p a) g = ((U - ε * V) * Real.sin (2 * g) + ε * N) / 2 ∧
    S * deriv (fun x => monoLogL p x g) a =
      ε / 2 * ((ε * U - V) * Real.sin (2 * g) + N) + 2 * ε * U * V * (Real.cot (2 * a) - Real.cot (2 * b)) ∧
    S ^ 2 * monoE p a g = (S * deriv (fun x => monoLogL p x g) a) * (S * deriv (monoLogM p a) g) -
      (S * deriv (monoLogL p a) g) * (S * deriv (fun x => monoLogM p x g) a) ∧
    monoE p a g * S = (ε * N ^ 2 - (U - ε * V) * (ε * U - V) * (1 - X ^ 2)) / (2 * U * V) +
      2 * ε * (Real.cot (2 * a) - Real.cot (2 * b)) * N := by
  intro ε b X U V N S
  have hb0 : 0 < b := mul_pos (by linarith) ha0
  have hba : b < a := by
    show (p - 1) * a < a
    nlinarith
  obtain ⟨hMb, hPb, hPa, h2a, h2b⟩ := sec5d_sines hb0 hba ha hg.1 hg.2
  have hMa : Real.sin (g - a) ≠ 0 := by
    rcases lt_or_gt_of_ne hga with h | h
    · have : 0 < Real.sin (a - g) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [show g - a = -(a - g) by ring, Real.sin_neg]
      linarith
    · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hU0 : U ≠ 0 := mul_ne_zero hMa hPa.ne'
  have hV0 : V ≠ 0 := mul_ne_zero hMb.ne' hPb.ne'
  obtain ⟨d1, d2, d3, d4⟩ := mono_log_partials p a g hMa hPa.ne' hMb.ne' hPb.ne' h2a.ne' h2b.ne'
  -- the four values `S·cot`
  have c1 : S * Real.cot (g - a) = V * (Real.sin (2 * g) + Real.sin (2 * a)) / 2 := by
    calc S * Real.cot (g - a) = (Real.sin (g + a) * Real.cos (g - a)) * V := by
          show Real.sin (g - a) * Real.sin (g + a) * V * Real.cot (g - a) = _
          rw [Real.cot_eq_cos_div_sin, mul_div_assoc', div_eq_iff hMa]
          ring
      _ = _ := by rw [sin_add_mul_cos_sub]; ring
  have c2 : S * Real.cot (g + a) = V * (Real.sin (2 * g) - Real.sin (2 * a)) / 2 := by
    calc S * Real.cot (g + a) = (Real.sin (g - a) * Real.cos (g + a)) * V := by
          show Real.sin (g - a) * Real.sin (g + a) * V * Real.cot (g + a) = _
          rw [Real.cot_eq_cos_div_sin, mul_div_assoc', div_eq_iff hPa.ne']
          ring
      _ = _ := by rw [sin_sub_mul_cos_add]; ring
  have c3 : S * Real.cot (g - b) = U * (Real.sin (2 * g) + Real.sin (2 * b)) / 2 := by
    calc S * Real.cot (g - b) = (Real.sin (g + b) * Real.cos (g - b)) * U := by
          show U * (Real.sin (g - b) * Real.sin (g + b)) * Real.cot (g - b) = _
          rw [Real.cot_eq_cos_div_sin, mul_div_assoc', div_eq_iff hMb.ne']
          ring
      _ = _ := by rw [sin_add_mul_cos_sub]; ring
  have c4 : S * Real.cot (g + b) = U * (Real.sin (2 * g) - Real.sin (2 * b)) / 2 := by
    calc S * Real.cot (g + b) = (Real.sin (g - b) * Real.cos (g + b)) * U := by
          show U * (Real.sin (g - b) * Real.sin (g + b)) * Real.cot (g + b) = _
          rw [Real.cot_eq_cos_div_sin, mul_div_assoc', div_eq_iff hPb.ne']
          ring
      _ = _ := by rw [sin_sub_mul_cos_add]; ring
  obtain ⟨eMg, eMa, eLg, eLa⟩ := cleared_algebra (ε := ε) (q := p / 2) (ka := Real.cot (2 * a))
    (kb := Real.cot (2 * b)) (by show 2 * (p / 2) - 1 = p - 1; ring) rfl rfl c1 c2 c3 c4
  have dMg : deriv (monoLogM p a) g = Real.cot (g - a) + Real.cot (g + b) - Real.cot (g + a) - Real.cot (g - b) :=
    d4.deriv
  have dMa : deriv (fun x => monoLogM p x g) a =
      -Real.cot (g - a) + ε * Real.cot (g + b) - Real.cot (g + a) + ε * Real.cot (g - b) := d3.deriv
  have dLg : deriv (monoLogL p a) g =
      (1 - p / 2) * Real.cot (g - b) + p / 2 * Real.cot (g + b) - ε * Real.cot (g + a) := d2.deriv
  have dLa : deriv (fun x => monoLogL p x g) a =
      ε * (p / 2 * Real.cot (g + b) - (1 - p / 2) * Real.cot (g - b) - Real.cot (g + a) +
        2 * Real.cot (2 * a) - 2 * Real.cot (2 * b)) := by
    rw [d1.deriv]
    show _ = (p - 1) * _
    ring
  have hU : U = (Real.cos (2 * a) - X) / 2 := sin_sub_mul_sin_add g a
  have hV : V = (Real.cos (2 * b) - X) / 2 := sin_sub_mul_sin_add g b
  have hSm : S = monoS p a g := by
    show Real.sin (g - a) * Real.sin (g + a) * (Real.sin (g - (p - 1) * a) * Real.sin (g + (p - 1) * a)) =
      monoS p a g
    unfold monoS
    ring
  have hMg' : S * deriv (monoLogM p a) g = N := by rw [dMg]; exact eMg
  have hMa' : S * deriv (fun x => monoLogM p x g) a = (ε * U - V) * Real.sin (2 * g) := by rw [dMa]; exact eMa
  have hLg' : S * deriv (monoLogL p a) g = ((U - ε * V) * Real.sin (2 * g) + ε * N) / 2 := by rw [dLg]; exact eLg
  have hLa' : S * deriv (fun x => monoLogL p x g) a =
      ε / 2 * ((ε * U - V) * Real.sin (2 * g) + N) + 2 * ε * U * V * (Real.cot (2 * a) - Real.cot (2 * b)) := by
    rw [dLa]; exact eLa
  have hES := es_algebra (X := X) (E := monoE p a g) rfl hU0 hV0 rfl hMg' hMa' hLg' hLa'
    (Real.sin_sq_add_cos_sq (2 * g))
  have hS2E : S ^ 2 * monoE p a g = (S * deriv (fun x => monoLogL p x g) a) * (S * deriv (monoLogM p a) g) -
      (S * deriv (monoLogL p a) g) * (S * deriv (fun x => monoLogM p x g) a) := by
    unfold monoE
    ring
  exact ⟨hU, hV, hSm, hMg', hMa', hLg', hLa', hS2E, hES⟩

/-- The coefficient identity, with `Sa = sin 2a`, `Ca = cos 2a`, `Sb = sin 2b`, `Cb = cos 2b`, `k = cot 2a − cot 2b`. -/
private lemma pi_algebra {ε X Sa Ca Sb Cb k : ℝ} (hk : Sa * Sb * k = Ca * Sb - Cb * Sa)
    (ha : Sa ^ 2 + Ca ^ 2 = 1) (hb : Sb ^ 2 + Cb ^ 2 = 1) (hU : Ca - X ≠ 0) (hV : Cb - X ≠ 0) :
    2 * Sa * Sb * ((ε * (Sa * ((Cb - X) / 2) - Sb * ((Ca - X) / 2)) ^ 2 -
        ((Ca - X) / 2 - ε * ((Cb - X) / 2)) * (ε * ((Ca - X) / 2) - (Cb - X) / 2) * (1 - X ^ 2)) /
          (2 * ((Ca - X) / 2) * ((Cb - X) / 2)) +
        2 * ε * k * (Sa * ((Cb - X) / 2) - Sb * ((Ca - X) / 2))) =
      -(1 - ε) ^ 2 * Sa * Sb * X ^ 2 + 2 * ε * (Sa * Cb - Ca * Sb) * (Sa - Sb) * X +
        (1 + ε ^ 2) * Sa * Sb - 2 * ε * Sa * Sb * (Ca * Cb + Sa * Sb) - 2 * ε * (Sa * Cb - Ca * Sb) ^ 2 := by
  have hUV : (Ca - X) * (Cb - X) ≠ 0 := mul_ne_zero hU hV
  have e1 : 2 * Sa * Sb * ((ε * (Sa * ((Cb - X) / 2) - Sb * ((Ca - X) / 2)) ^ 2 -
        ((Ca - X) / 2 - ε * ((Cb - X) / 2)) * (ε * ((Ca - X) / 2) - (Cb - X) / 2) * (1 - X ^ 2)) /
          (2 * ((Ca - X) / 2) * ((Cb - X) / 2)) +
        2 * ε * k * (Sa * ((Cb - X) / 2) - Sb * ((Ca - X) / 2))) =
      (4 * Sa * Sb * (ε * (Sa * ((Cb - X) / 2) - Sb * ((Ca - X) / 2)) ^ 2 -
        ((Ca - X) / 2 - ε * ((Cb - X) / 2)) * (ε * ((Ca - X) / 2) - (Cb - X) / 2) * (1 - X ^ 2)) +
        4 * ε * (Sa * Sb * k) * (Sa * ((Cb - X) / 2) - Sb * ((Ca - X) / 2)) * ((Ca - X) * (Cb - X))) /
        ((Ca - X) * (Cb - X)) := by
    field_simp
    ring
  rw [e1, hk, div_eq_iff hUV]
  linear_combination (Sa * Sb * ε * (Cb - X) ^ 2) * ha + (Sa * Sb * ε * (Ca - X) ^ 2) * hb

/-- sec5d l.28 (`ε = p − 1`, `b = εa`): `sin 2a sin 2b (cot 2a − cot 2b) = −sin 2(a − b)`; with the affine forms of
`U, V` (for every `X` with `UV ≠ 0`), the coefficients of `X², X, 1` in `2 sin 2a sin 2b ES` are those of `Π(X)`. -/
theorem q15_sec5d_Pi_coefficients_proved {p a : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ha0 : 0 < a)
    (ha : a < Real.pi / 2) :
    let ε := p - 1
    let b := (p - 1) * a
    Real.sin (2 * a) * Real.sin (2 * b) * (Real.cot (2 * a) - Real.cot (2 * b)) = -Real.sin (2 * (a - b)) ∧
    ∀ X : ℝ, Real.cos (2 * a) - X ≠ 0 → Real.cos (2 * b) - X ≠ 0 →
      let U := (Real.cos (2 * a) - X) / 2
      let V := (Real.cos (2 * b) - X) / 2
      let N := Real.sin (2 * a) * V - Real.sin (2 * b) * U
      2 * Real.sin (2 * a) * Real.sin (2 * b) *
          ((ε * N ^ 2 - (U - ε * V) * (ε * U - V) * (1 - X ^ 2)) / (2 * U * V) +
            2 * ε * (Real.cot (2 * a) - Real.cot (2 * b)) * N) =
        monoPi ε (2 * a) X := by
  intro ε b
  have hb0 : 0 < b := mul_pos (by linarith) ha0
  have hba : b < a := by
    show (p - 1) * a < a
    nlinarith
  have h2a : 0 < Real.sin (2 * a) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h2b : 0 < Real.sin (2 * b) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h2a' := h2a.ne'
  have h2b' := h2b.ne'
  have hk : Real.sin (2 * a) * Real.sin (2 * b) * (Real.cot (2 * a) - Real.cot (2 * b)) =
      Real.cos (2 * a) * Real.sin (2 * b) - Real.cos (2 * b) * Real.sin (2 * a) := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
    field_simp
  refine ⟨?_, fun X hU hV => ?_⟩
  · rw [hk, show 2 * (a - b) = 2 * a - 2 * b by ring, Real.sin_sub]
    ring
  intro U V N
  · have hpi : monoPi ε (2 * a) X =
        -(1 - ε) ^ 2 * Real.sin (2 * a) * Real.sin (2 * b) * X ^ 2 +
          2 * ε * (Real.sin (2 * a) * Real.cos (2 * b) - Real.cos (2 * a) * Real.sin (2 * b)) *
            (Real.sin (2 * a) - Real.sin (2 * b)) * X +
          (1 + ε ^ 2) * Real.sin (2 * a) * Real.sin (2 * b) -
          2 * ε * Real.sin (2 * a) * Real.sin (2 * b) *
            (Real.cos (2 * a) * Real.cos (2 * b) + Real.sin (2 * a) * Real.sin (2 * b)) -
          2 * ε * (Real.sin (2 * a) * Real.cos (2 * b) - Real.cos (2 * a) * Real.sin (2 * b)) ^ 2 := by
      unfold monoPi
      rw [show ε * (2 * a) = 2 * b by show (p - 1) * (2 * a) = 2 * ((p - 1) * a); ring,
        show (1 - ε) * (2 * a) = 2 * a - 2 * b by show (1 - (p - 1)) * (2 * a) = 2 * a - 2 * ((p - 1) * a); ring,
        Real.sin_sub, Real.cos_sub]
    rw [hpi]
    exact pi_algebra hk (Real.sin_sq_add_cos_sq _) (Real.sin_sq_add_cos_sq _) hU hV

end GKSharp.Proofs.Q15Monotone
