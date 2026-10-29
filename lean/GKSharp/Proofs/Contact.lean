/- GKSharp/Proofs/Contact.lean - the contact point of Section 5: rho(theta0) = C, Lambda(theta0) = 0,
K_f(theta0) = K, and z_* = 1/zeta_* with |z_*| = 1/r_* (sec5_sharp_inequality.tex l.106-122).
20261028.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.CurveK
import GKSharp.Proofs.GKProps
import GKSharp.Defs.Potential

namespace GKSharp

open ComplexConjugate

theorem mobQ_re_im (lam : ℝ) (w : ℂ) :
    (mobQ lam w).re = -(w.re ^ 2 + w.im ^ 2 + lam) + (1 + lam) * w.re ∧ (mobQ lam w).im = (1 - lam) * w.im := by
  simp only [mobQ, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  constructor <;> ring

section Contact

variable {p lam : ℝ}

/-- Trigonometry at `θ₀ = π/p`: `sin δ₀ = c₀`, `cos δ₀ = s₀`, `sin(qθ₀) = 1`. -/
theorem theta0_trig (hp1 : 1 < p) :
    Real.sin ((1 - p / 2) * (Real.pi / p)) = -Real.cos (Real.pi / p) ∧
    Real.cos ((1 - p / 2) * (Real.pi / p)) = Real.sin (Real.pi / p) ∧
    Real.sin (p / 2 * (Real.pi / p)) = 1 := by
  have hp0 : p ≠ 0 := by linarith
  have h1 : (1 - p / 2) * (Real.pi / p) = Real.pi / p - Real.pi / 2 := by field_simp
  have h2 : p / 2 * (Real.pi / p) = Real.pi / 2 := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, Real.sin_sub_pi_div_two]
  · rw [h1, Real.cos_sub_pi_div_two]
  · rw [h2, Real.sin_pi_div_two]

theorem theta0_bounds (hp1 : 1 < p) (hp2 : p < 2) :
    0 < Real.pi / p ∧ Real.pi / p < Real.pi ∧ 0 < Real.sin (Real.pi / p) ∧ 0 < -Real.cos (Real.pi / p) := by
  have hp0 : 0 < p := by linarith
  have ha : Real.pi / 2 < Real.pi / p := by
    rw [div_lt_div_iff₀ (by norm_num) hp0]; nlinarith [Real.pi_pos]
  have hb : Real.pi / p < Real.pi := by
    rw [div_lt_iff₀ hp0]; nlinarith [Real.pi_pos]
  refine ⟨by positivity, hb, Real.sin_pos_of_pos_of_lt_pi (by positivity) hb, ?_⟩
  have : Real.cos (Real.pi / p) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt ha (by linarith [Real.pi_pos])
  linarith

/-- Algebraic core of the contact lemma: `(X + λ)s₀ = τV` with `X = τ²V`, `V = ((1+λ)s₀)² + ((1−λ)c₀)²`, forces
`X = GK_p(λ)²` (the other root `λ²/C²` is excluded by `X + λ > 0` and, for `λ > 0`, by `X > λ`). -/
theorem contact_X_eq (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) {s0 c0 X τ : ℝ}
    (hs0def : s0 = Real.sin (Real.pi / p)) (hc0def : c0 = -Real.cos (Real.pi / p)) (hτ : 0 < τ)
    (hX : X = τ ^ 2 * (((1 + lam) * s0) ^ 2 + ((1 - lam) * c0) ^ 2))
    (hE1 : (X + lam) * s0 = τ * (((1 + lam) * s0) ^ 2 + ((1 - lam) * c0) ^ 2))
    (hXl : 0 < lam → lam < X) : X = gk p lam ^ 2 := by
  obtain ⟨-, -, hs0, hc0⟩ := theta0_bounds hp1 hp2
  rw [← hs0def] at hs0
  rw [← hc0def] at hc0
  set V := ((1 + lam) * s0) ^ 2 + ((1 - lam) * c0) ^ 2 with hVdef
  have hVpos : 0 < V := by
    have : 0 < (1 - lam) * c0 := mul_pos (by linarith) hc0
    positivity
  have hsq : (X + lam) ^ 2 * s0 ^ 2 = X * V := by
    calc (X + lam) ^ 2 * s0 ^ 2 = ((X + lam) * s0) ^ 2 := by ring
      _ = (τ * V) ^ 2 := by rw [hE1]
      _ = (τ ^ 2 * V) * V := by ring
      _ = X * V := by rw [hX]
  set t := c0 / s0 with htdef
  have ht : s0 * t = c0 := by rw [htdef]; field_simp
  have hcot : Real.cot (Real.pi / p) = -t := by rw [Real.cot_eq_cos_div_sin, htdef, hc0def, hs0def]; ring
  have hM : gkMid p lam = 1 + lam ^ 2 + (1 - lam) ^ 2 * t ^ 2 := by
    unfold gkMid
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs,
      show (1 : ℂ) - (lam : ℂ) = ((1 - lam : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, hcot]
    ring
  have hroot : gkQuad p lam X = 0 := by
    unfold gkQuad
    rw [hM, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have key : s0 ^ 2 * (X ^ 2 - (1 + lam ^ 2 + (1 - lam) ^ 2 * t ^ 2) * X + lam ^ 2) = 0 := by
      linear_combination hsq + (-(1 - lam) ^ 2 * X * (s0 * t + c0)) * ht
    have hs2 : s0 ^ 2 ≠ 0 := by positivity
    exact (mul_eq_zero.1 key).resolve_left hs2
  have hfac := gkQuad_factor p (lam : ℂ) X
  rw [hroot, eq_comm, mul_eq_zero, sub_eq_zero, sub_eq_zero] at hfac
  have hprod : gkRootHi p lam * gkRootLo p lam = lam ^ 2 := by
    have h := gkQuad_factor p (lam : ℂ) 0
    unfold gkQuad at h
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    linarith
  have hC1 : 1 < gk p lam := by
    have h := gk_gt_max hp1 (by linarith : p ≠ 2) (ρ := (lam : ℂ))
      (by intro h; have := congrArg Complex.re h; simp at this; linarith)
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    exact lt_of_le_of_lt (le_max_left _ _) h
  have hhi : gkRootHi p lam = gk p lam ^ 2 := (gk_sq_eq p lam).symm
  have hXpos : 0 < X + lam := by
    by_contra hneg
    push_neg at hneg
    have h1 : (X + lam) * s0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hs0.le
    have h2 : 0 < τ * V := mul_pos hτ hVpos
    linarith
  rcases hfac with h | h
  · rwa [hhi] at h
  · exfalso
    have hC2 : 1 < gk p lam ^ 2 := by nlinarith
    have hlo : gkRootLo p lam = lam ^ 2 / gk p lam ^ 2 := by
      rw [hhi] at hprod; field_simp; linarith
    rw [hlo] at h
    rcases lt_or_ge lam 0 with hneg | hnn
    · have h3 : lam ^ 2 < -lam * gk p lam ^ 2 := by nlinarith
      have h4 : lam ^ 2 / gk p lam ^ 2 + lam < 0 := by
        have : lam ^ 2 / gk p lam ^ 2 < -lam := by rw [div_lt_iff₀ (by positivity)]; linarith
        linarith
      rw [← h] at h4; linarith
    · rcases hnn.lt_or_eq with hpos | hzero
      · have h4 : lam ^ 2 / gk p lam ^ 2 < lam := by
          rw [div_lt_iff₀ (by positivity)]; nlinarith
        have := hXl hpos
        rw [h] at this; linarith
      · subst hzero
        rw [h] at hXpos; simp at hXpos

/-- Data at the contact point: `τ = |w|/|v|`, `|Q| = (1−λ)²τc₀/s₀` (by (5.4)) and `τ(C² + λ)s₀ = C²`. -/
theorem contact_data (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    ∃ τ : ℝ, 0 < τ ∧
      ‖mobW lam (curveZ p lam (Real.pi / p))‖ / ‖curveV p lam (Real.pi / p)‖ = τ ∧
      ‖mobQ lam (mobW lam (curveZ p lam (Real.pi / p)))‖ =
        (1 - lam) ^ 2 * τ * -Real.cos (Real.pi / p) / Real.sin (Real.pi / p) ∧
      τ * ((gk p lam ^ 2 + lam) * Real.sin (Real.pi / p)) = gk p lam ^ 2 := by
  obtain ⟨hθ0, hθ, hs0, hc0⟩ := theta0_bounds hp1 hp2
  obtain ⟨hsd, hcd, hs2⟩ := theta0_trig hp1
  set θ := Real.pi / p with hθdef
  set s0 := Real.sin θ with hs0def
  set c0 := -Real.cos θ with hc0def
  set r := curveR p lam θ with hr
  obtain ⟨hA, hQn, hρ2, hw, -, -, -⟩ := dict_identities hp1 hp2 hl hl1 hθ0 hθ hr
  obtain ⟨-, -, hR0, hR1, hDR⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  rw [← hr] at hR0 hR1 hDR
  have hz : curveZ p lam θ = (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) := rfl
  rw [hz]
  set z := (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) with hzdef
  set w := mobW lam z with hwdef
  obtain ⟨hzr, hzi⟩ := polar_re_im r θ
  rw [← hzdef] at hzr hzi
  have hz1 : (1 : ℂ) + z ≠ 0 := polar_one_add_ne_zero hR0 hθ0 hθ
  have hzm1 : z ≠ -1 := by intro h; apply hz1; rw [h]; ring
  set A := 1 + 2 * r * Real.cos θ + r ^ 2 with hAdef
  have hApos : 0 < A := by rw [← hA]; exact pow_pos (norm_pos_iff.2 hz1) 2
  set τ := r * Real.sin θ / (A * Real.sin ((1 - p / 2) * θ)) with hτdef
  have hτpos : 0 < τ := by
    rw [hτdef, hsd]; exact div_pos (mul_pos hR0 hs0) (mul_pos hApos hc0)
  obtain ⟨hvr, hvi⟩ := curveV_re_im p lam θ
  rw [hcd] at hvr
  rw [hsd] at hvi
  -- coordinates of w = τ v
  have hwr : w.re = τ * ((1 + lam) * s0) := by rw [hw, Complex.re_ofReal_mul, hvr]
  have hwi : w.im = τ * ((1 - lam) * c0) := by rw [hw, Complex.im_ofReal_mul, hvi]
  -- Q(w) = ((1-λ)²/A) z̄ has argument θ: s₀ Re Q + c₀ Im Q = 0
  have hQ := mobQ_mobW lam hzm1
  rw [hA] at hQ
  obtain ⟨hQr, hQi⟩ := mobQ_re_im lam w
  have hE0 : s0 * (mobQ lam w).re + c0 * (mobQ lam w).im = 0 := by
    rw [hQ, Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.conj_re, Complex.conj_im, hzr, hzi]
    ring
  rw [hQr, hQi, hwr, hwi] at hE0
  set V := ((1 + lam) * s0) ^ 2 + ((1 - lam) * c0) ^ 2 with hVdef
  have hVpos : 0 < V := by
    have : 0 < (1 - lam) * c0 := mul_pos (by linarith) hc0
    positivity
  have hX : ‖w‖ ^ 2 = τ ^ 2 * V := by
    rw [Complex.sq_norm, Complex.normSq_apply, hwr, hwi]; ring
  set X := ‖w‖ ^ 2 with hXdef
  -- (E1): (X + λ) s₀ = τ V
  have hE1 : (X + lam) * s0 = τ * V := by
    rw [hX]; linear_combination (-1 : ℝ) * hE0
  have hXl : 0 < lam → lam < X := by
    intro hpos
    have hB : ‖1 + (lam : ℂ) * z‖ ^ 2 - lam * A = (1 - lam) * (1 - lam * r ^ 2) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, hzr, hzi]
      rw [hAdef]
      linear_combination (lam ^ 2 * r ^ 2) * Real.sin_sq_add_cos_sq θ
    show lam < X
    rw [hρ2, lt_div_iff₀ hApos]
    have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hR0.le hR1
    have hlr : lam * r ^ 2 ≤ lam := by
      have := mul_le_mul_of_nonneg_left hr2 hpos.le
      linarith
    have : 0 < (1 - lam) * (1 - lam * r ^ 2) := mul_pos (by linarith) (by linarith)
    linarith
  have hXC := contact_X_eq hp1 hp2 hl hl1 (s0 := s0) (c0 := c0) (X := X) (τ := τ) rfl rfl hτpos hX hE1 hXl
  have hvpos : 0 < ‖curveV p lam θ‖ := by
    have : 0 < (curveV p lam θ).im := by rw [hvi]; exact mul_pos (by linarith) hc0
    exact norm_pos_iff.2 (fun h => by rw [h, Complex.zero_im] at this; exact lt_irrefl _ this)
  refine ⟨τ, hτpos, ?_, ?_, ?_⟩
  · rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτpos, mul_div_assoc,
      div_self hvpos.ne', mul_one]
  · rw [hQn, hτdef, hsd]
    field_simp
    rfl
  · rw [← hXC]
    have h1 : τ * ((X + lam) * s0) = τ * (τ * V) := by rw [hE1]
    rw [h1, hX]; ring

/-- Lemma (the contact point), first assertion: `ρ(θ₀) = C`, `C = GK_p(λ)`, `θ₀ = π/p`. -/
theorem contact_rho (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    ‖mobW lam (curveZ p lam (Real.pi / p))‖ = gk p lam := by
  obtain ⟨hθ0, hθ, hs0, hc0⟩ := theta0_bounds hp1 hp2
  obtain ⟨hsd, hcd, hs2⟩ := theta0_trig hp1
  set θ := Real.pi / p with hθdef
  set s0 := Real.sin θ with hs0def
  set c0 := -Real.cos θ with hc0def
  set r := curveR p lam θ with hr
  obtain ⟨hA, hQn, hρ2, hw, -, -, -⟩ := dict_identities hp1 hp2 hl hl1 hθ0 hθ hr
  obtain ⟨-, -, hR0, hR1, hDR⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  rw [← hr] at hR0 hR1 hDR
  have hz : curveZ p lam θ = (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) := rfl
  rw [hz]
  set z := (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) with hzdef
  set w := mobW lam z with hwdef
  obtain ⟨hzr, hzi⟩ := polar_re_im r θ
  rw [← hzdef] at hzr hzi
  have hz1 : (1 : ℂ) + z ≠ 0 := polar_one_add_ne_zero hR0 hθ0 hθ
  have hzm1 : z ≠ -1 := by intro h; apply hz1; rw [h]; ring
  set A := 1 + 2 * r * Real.cos θ + r ^ 2 with hAdef
  have hApos : 0 < A := by rw [← hA]; exact pow_pos (norm_pos_iff.2 hz1) 2
  set τ := r * Real.sin θ / (A * Real.sin ((1 - p / 2) * θ)) with hτdef
  have hτpos : 0 < τ := by
    rw [hτdef, hsd]; exact div_pos (mul_pos hR0 hs0) (mul_pos hApos hc0)
  obtain ⟨hvr, hvi⟩ := curveV_re_im p lam θ
  rw [hcd] at hvr
  rw [hsd] at hvi
  -- coordinates of w = τ v
  have hwr : w.re = τ * ((1 + lam) * s0) := by rw [hw, Complex.re_ofReal_mul, hvr]
  have hwi : w.im = τ * ((1 - lam) * c0) := by rw [hw, Complex.im_ofReal_mul, hvi]
  -- Q(w) = ((1-λ)²/A) z̄ has argument θ: s₀ Re Q + c₀ Im Q = 0
  have hQ := mobQ_mobW lam hzm1
  rw [hA] at hQ
  obtain ⟨hQr, hQi⟩ := mobQ_re_im lam w
  have hE0 : s0 * (mobQ lam w).re + c0 * (mobQ lam w).im = 0 := by
    rw [hQ, Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.conj_re, Complex.conj_im, hzr, hzi]
    ring
  rw [hQr, hQi, hwr, hwi] at hE0
  set V := ((1 + lam) * s0) ^ 2 + ((1 - lam) * c0) ^ 2 with hVdef
  have hVpos : 0 < V := by
    have : 0 < (1 - lam) * c0 := mul_pos (by linarith) hc0
    positivity
  have hX : ‖w‖ ^ 2 = τ ^ 2 * V := by
    rw [Complex.sq_norm, Complex.normSq_apply, hwr, hwi]; ring
  set X := ‖w‖ ^ 2 with hXdef
  -- (E1): (X + λ) s₀ = τ V
  have hE1 : (X + lam) * s0 = τ * V := by
    rw [hX]; linear_combination (-1 : ℝ) * hE0
  have hXl : 0 < lam → lam < X := by
    intro hpos
    have hB : ‖1 + (lam : ℂ) * z‖ ^ 2 - lam * A = (1 - lam) * (1 - lam * r ^ 2) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, hzr, hzi]
      rw [hAdef]
      linear_combination (lam ^ 2 * r ^ 2) * Real.sin_sq_add_cos_sq θ
    show lam < X
    rw [hρ2, lt_div_iff₀ hApos]
    have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hR0.le hR1
    have hlr : lam * r ^ 2 ≤ lam := by
      have := mul_le_mul_of_nonneg_left hr2 hpos.le
      linarith
    have : 0 < (1 - lam) * (1 - lam * r ^ 2) := mul_pos (by linarith) (by linarith)
    linarith
  have hXC := contact_X_eq hp1 hp2 hl hl1 (s0 := s0) (c0 := c0) (X := X) (τ := τ) rfl rfl hτpos hX hE1 hXl
  exact (pow_left_inj₀ (norm_nonneg _) (gk_nonneg _ _) two_ne_zero).1 hXC

/-- `|1 + λz_*| = C|1 + z_*|` at the contact point. -/
theorem contact_norm_eq (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    ‖1 + (lam : ℂ) * curveZ p lam (Real.pi / p)‖ = gk p lam * ‖1 + curveZ p lam (Real.pi / p)‖ := by
  obtain ⟨hθ0, hθ, -, -⟩ := theta0_bounds hp1 hp2
  obtain ⟨-, -, hR0, -, -⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  have hz1 : (1 : ℂ) + curveZ p lam (Real.pi / p) ≠ 0 := polar_one_add_ne_zero hR0 hθ0 hθ
  have h := contact_rho hp1 hp2 hl hl1
  unfold mobW at h
  rw [norm_div, div_eq_iff (norm_ne_zero_iff.2 hz1)] at h
  exact h

/-- Lemma (the contact point): `Λ(θ₀) = 0`, i.e. `𝒟_C(z_*) = 0` (for every `K`, as `Re z_*^q = |z_*|^q cos(qθ₀) = 0`). -/
theorem contact_Lambda (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) (K : ℝ) :
    critD p (gk p lam) K lam (curveZ p lam (Real.pi / p)) = 0 := by
  obtain ⟨hθ0, hθ, -, -⟩ := theta0_bounds hp1 hp2
  obtain ⟨-, -, hR0, -, -⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  have hn := contact_norm_eq hp1 hp2 hl hl1
  have harg : Complex.arg (curveZ p lam (Real.pi / p)) = -(Real.pi / p) := by
    unfold curveZ
    rw [Complex.arg_real_mul _ hR0,
      show Complex.exp (-((Real.pi / p : ℝ) : ℂ) * Complex.I) =
        Complex.cos ((-(Real.pi / p) : ℝ) : ℂ) + Complex.sin ((-(Real.pi / p) : ℝ) : ℂ) * Complex.I by
        rw [← Complex.exp_mul_I]; push_cast; ring_nf,
      Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith [Real.pi_pos]⟩]
  have hp0 : p ≠ 0 := by linarith
  have hcos : Real.cos (p / 2 * Complex.arg (curveZ p lam (Real.pi / p))) = 0 := by
    rw [harg, show p / 2 * -(Real.pi / p) = -(Real.pi / 2) by field_simp, Real.cos_neg, Real.cos_pi_div_two]
  unfold critD reQPow
  rw [hn, Real.mul_rpow (gk_nonneg _ _) (norm_nonneg _), hcos]
  ring

/-- Lemma (the contact point): `z_* = z_{θ₀} = 1/ζ_*`, `ζ_* = r_* e^{iθ₀}`, so `|z_*| = 1/r_*`. -/
theorem contact_point (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    curveZ p lam (Real.pi / p) =
      1 / ((contactRadius p lam : ℂ) * Complex.exp (((Real.pi / p : ℝ) : ℂ) * Complex.I)) ∧
    ‖curveZ p lam (Real.pi / p)‖ = 1 / contactRadius p lam := by
  obtain ⟨hθ0, hθ, hs0, hc0⟩ := theta0_bounds hp1 hp2
  obtain ⟨hsd, hcd, hs2⟩ := theta0_trig hp1
  obtain ⟨-, -, hR0, hR1, hDR⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  have hn := contact_norm_eq hp1 hp2 hl hl1
  set θ := Real.pi / p with hθdef
  set C := gk p lam with hCdef
  set r := curveR p lam θ with hr
  set c0 := -Real.cos θ with hc0def
  have hz : curveZ p lam θ = (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) := rfl
  obtain ⟨hzr, hzi⟩ := polar_re_im r θ
  rw [← hz] at hzr hzi
  have hC1 : 1 < C := by
    have h := gk_gt_max hp1 (by linarith : p ≠ 2) (ρ := (lam : ℂ))
      (by intro h; have := congrArg Complex.re h; simp at this; linarith)
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    exact lt_of_le_of_lt (le_max_left _ _) h
  -- squared moduli in coordinates
  have hsq := congrArg (· ^ 2) hn
  simp only [mul_pow, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzr, hzi] at hsq
  have hQ1 : (C ^ 2 - lam ^ 2) * r ^ 2 - 2 * (C ^ 2 - lam) * c0 * r + (C ^ 2 - 1) = 0 := by
    rw [hc0def]; linear_combination (-1 : ℝ) * hsq + (-(C ^ 2 - lam ^ 2) * r ^ 2) * Real.sin_sq_add_cos_sq θ
  have hD0 : (1 + lam) * r - (1 + lam * r ^ 2) * c0 = 0 := by
    have h := hDR; unfold curveD at h; rw [hs2, hsd] at h; linarith
  have hlr : 0 < 1 - lam * r ^ 2 := by
    have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hR0.le hR1
    rcases le_or_gt lam 0 with h | h
    · nlinarith
    · have := mul_le_mul_of_nonneg_left hr2 h.le; linarith
  have hut : (C ^ 2 - lam ^ 2) * r ^ 2 = C ^ 2 - 1 := by
    have key : ((C ^ 2 - 1) - (C ^ 2 - lam ^ 2) * r ^ 2) * (1 - lam * r ^ 2) = 0 := by
      linear_combination (1 + lam * r ^ 2) * hQ1 - 2 * (C ^ 2 - lam) * r * hD0
    have := (mul_eq_zero.1 key).resolve_right hlr.ne'
    linarith
  have hR : r * ((C ^ 2 - lam) * c0) = C ^ 2 - 1 := by
    linear_combination (-(1 : ℝ) / 2) * hQ1 + (1 / 2 : ℝ) * hut
  have hC2 : 1 < C ^ 2 := one_lt_pow₀ hC1 two_ne_zero
  have hrad : contactRadius p lam = (C ^ 2 - lam) * c0 / (C ^ 2 - 1) := by
    unfold contactRadius contactKappa
    rw [← hCdef, abs_of_neg (by linarith : Real.cos θ < 0)]
    ring
  have hC21 : C ^ 2 - 1 ≠ 0 := by linarith
  have hrinv : r = 1 / contactRadius p lam := by
    rw [hrad, one_div_div, eq_div_iff (mul_ne_zero (by linarith) hc0.ne')]
    linarith
  refine ⟨?_, ?_⟩
  · rw [hz, hrinv]
    push_cast
    rw [show -(θ : ℂ) * Complex.I = -((θ : ℂ) * Complex.I) by ring, Complex.exp_neg]
    field_simp
  · rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0,
      show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I,
      mul_one, hrinv]

theorem sq_rpow_one_sub_half {x : ℝ} (hx : 0 ≤ x) (p : ℝ) : (x ^ 2) ^ (1 - p / 2) = x ^ (2 - p) := by
  rw [show 1 - p / 2 = (2 - p) / 2 by ring]; exact sq_rpow_half hx (2 - p)

/-- Lemma (the contact point): `K_f(θ₀) = K` (with the first form of eq:K; `K_f(θ₀)/K = (1−λ)C/(s₀(C² − λ)) = 1` by
eq:GKreal). -/
theorem contact_Kf (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    curveKf p lam (Real.pi / p) = kConst p lam := by
  obtain ⟨τ, hτpos, hτ, hQ, hτC⟩ := contact_data hp1 hp2 hl hl1
  obtain ⟨-, hcd, -⟩ := theta0_trig hp1
  obtain ⟨-, -, hs0, hc0⟩ := theta0_bounds hp1 hp2
  have hρ := contact_rho hp1 hp2 hl hl1
  have hGK := (gk_real_eq hp1 hl1).1
  have hC1 : 1 < gk p lam := by
    have h := gk_gt_max hp1 (by linarith : p ≠ 2) (ρ := (lam : ℂ))
      (by intro h; have := congrArg Complex.re h; simp at this; linarith)
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    exact lt_of_le_of_lt (le_max_left _ _) h
  unfold curveKf
  rw [hτ, hQ, hρ, hcd]
  unfold kConst
  set C := gk p lam with hCdef
  set s0 := Real.sin (Real.pi / p) with hs0def
  set c0 := -Real.cos (Real.pi / p) with hc0def
  have hC0 : 0 < C := by linarith
  have hC2 : 1 < C ^ 2 := one_lt_pow₀ hC1 two_ne_zero
  set a := C ^ 2 + lam with hadef
  have ha : 0 < a := by rw [hadef]; linarith
  have hl' : 0 < 1 - lam := by linarith
  have hτv : τ = C ^ 2 / (a * s0) := by
    rw [eq_div_iff (mul_pos ha hs0).ne']; linarith
  rw [hτv]
  have hQs : ((1 - lam) ^ 2 * (C ^ 2 / (a * s0)) * c0 / s0) ^ (1 - p / 2) =
      (1 - lam) ^ (2 - p) * (C ^ (2 - p) * c0 ^ (1 - p / 2) / (a ^ (1 - p / 2) * s0 ^ (2 - p))) := by
    rw [show (1 - lam) ^ 2 * (C ^ 2 / (a * s0)) * c0 / s0 = (1 - lam) ^ 2 * (C ^ 2 * c0 / (a * s0 ^ 2)) by
        field_simp,
      Real.mul_rpow (by positivity) (by positivity), Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) hc0.le, Real.mul_rpow ha.le (by positivity),
      sq_rpow_one_sub_half hl'.le, sq_rpow_one_sub_half hC0.le, sq_rpow_one_sub_half hs0.le]
  rw [hQs]
  have hden : 2 * (C ^ 2 / (a * s0)) * s0 - 1 = (C ^ 2 - lam) / a := by
    have ha' : a ≠ 0 := ha.ne'
    have hs0' : s0 ≠ 0 := hs0.ne'
    have h1 : 2 * (C ^ 2 / (a * s0)) * s0 = 2 * C ^ 2 / a := by field_simp
    rw [h1, div_sub_one ha']
    congr 1
    rw [hadef]; ring
  rw [hden]
  -- the exact inverse pairs of real powers
  have e1 : (1 - lam) ^ (2 - p) = (1 - lam) ^ 2 / (1 - lam) ^ p := by
    rw [eq_div_iff (Real.rpow_pos_of_pos hl' p).ne', ← Real.rpow_add hl',
      show 2 - p + p = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e2 : C ^ (2 - p) = 1 / C ^ (p - 2) := by
    rw [eq_div_iff (Real.rpow_pos_of_pos hC0 _).ne', ← Real.rpow_add hC0, show 2 - p + (p - 2) = 0 by ring,
      Real.rpow_zero]
  have e3 : a ^ (p / 2 - 1) = 1 / a ^ (1 - p / 2) := by
    rw [eq_div_iff (Real.rpow_pos_of_pos ha _).ne', ← Real.rpow_add ha, show p / 2 - 1 + (1 - p / 2) = 0 by ring,
      Real.rpow_zero]
  have e4 : s0 ^ (p - 2) = 1 / s0 ^ (2 - p) := by
    rw [eq_div_iff (Real.rpow_pos_of_pos hs0 _).ne', ← Real.rpow_add hs0, show p - 2 + (2 - p) = 0 by ring,
      Real.rpow_zero]
  rw [e1, e2, e3, e4]
  have hP : 0 < (1 - lam) ^ p := Real.rpow_pos_of_pos hl' p
  have hCp : 0 < C ^ (p - 2) := Real.rpow_pos_of_pos hC0 _
  have hap : 0 < a ^ (1 - p / 2) := Real.rpow_pos_of_pos ha _
  have hsp : 0 < s0 ^ (2 - p) := Real.rpow_pos_of_pos hs0 _
  have hCl : 0 < C ^ 2 - lam := by linarith
  -- K_f / K = (1 - λ) C / (s₀ (C² − λ)) = 1 by eq:GKreal
  have hratio : (1 - lam) * C = s0 * (C ^ 2 - lam) := hGK
  field_simp
  linear_combination hratio

end Contact

end GKSharp
