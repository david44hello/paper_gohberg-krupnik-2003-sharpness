/- GKSharp/Proofs/SharpA2.lean - Consequence (A2) of Section 5 (sec5_sharp_inequality.tex l.85-90): along the critical
curve, rho(theta) = |w(z_theta)| is continuous on (0, pi) with positive derivative, increases strictly, tends to
infinity at pi and to rho0 = (1 + lam r0)/(1 + r0) in [0, 1) at 0; also the complex limit w(theta) -> rho0 (Reduction,
l.148 and l.153).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.LemmaA
import GKSharp.Proofs.CurveDict

/-!
Route (R8). The text (l.84-86) gets injectivity from (A1) and `ρ' > 0` from the implicit function theorem. Here the
derivative is computed directly instead:

* `R' = -∂_θD/∂_rD`, by differentiating `D(θ, R(θ)) = 0` (`R` is analytic, `∂_rD > 0`);
* `ρ² = B/A` with `A = |1 + z_θ|²`, `B = |1 + λz_θ|²` (l.53), so `(ρ²)' = 2(1 - λ)E/(∂_rD · A²)`;
* modulo `D = 0` and Pythagoras, `(1 + λ)² s₂² E = (1 + λr²)² sin θ (s₁|v|² - (1 - q)(1 + λ)² c₂ sin θ)`, and the
  right side is positive by the Lemma A bracket (`lemmaA_bracket`); for `λ = -1`, `R ≡ 1` and `E = 4 s₁ sin θ`.

Strict monotonicity then follows from `strictMonoOn_of_deriv_pos`; the limits come from `curve_root_limits`.
-/

namespace GKSharp

open Filter Topology

namespace SharpA2

/-! ## Algebra -/

/-- The numerator identity: modulo `D(θ, r) = 0` (`hD`) and Pythagoras, `(1 + λ)² s₂² E` is `(1 + λr²)² sin θ` times
`s₁|v|² - (1 - q)(1 + λ)² c₂ sin θ` (`q = p/2`, `|v|² = (1 + λ)²c₁² + (1 - λ)²s₁²`). -/
theorem key_identity (l r p s1 s2 c1 c2 sn cs : ℝ) (hsn : sn = s2 * c1 + c2 * s1) (hcs : cs = c2 * c1 - s2 * s1)
    (hD : (1 + l) * r * s2 - (1 + l * r ^ 2) * s1 = 0) (P1 : s1 ^ 2 + c1 ^ 2 = 1) (P2 : s2 ^ 2 + c2 ^ 2 = 1) :
    (1 + l) ^ 2 * s2 ^ 2 *
        (r * sn * (1 - l * r ^ 2) * ((1 + l) * s2 - 2 * l * r * s1) +
          ((1 + l) * r * (c2 * (p / 2)) - (1 + l * r ^ 2) * (c1 * (1 - p / 2))) *
            ((1 + l * r ^ 2) * cs + (1 + l) * r)) =
      (1 + l * r ^ 2) ^ 2 * sn *
        (s1 * ((1 + l) ^ 2 * c1 ^ 2 + (1 - l) ^ 2 * s1 ^ 2) - (1 - p / 2) * (1 + l) ^ 2 * c2 * sn) := by
  subst hsn hcs
  linear_combination (-c1*l^3*(p / 2)*r^2*s2^3 + 2*c1*l^3*(p / 2)*r^2*s2 - c1*l^3*r^2*s2^3 - c1*l^3*r^2*s2 - 2*c1*l^2*(p / 2)*r^2*s2^3 + 4*c1*l^2*(p / 2)*r^2*s2 - c1*l^2*(p / 2)*s2^3 + 2*c1*l^2*(p / 2)*s2 - 4*c1*l^2*r^2*s1^2*s2 - 2*c1*l^2*r^2*s2^3 - 2*c1*l^2*r^2*s2 - 4*c1*l^2*r*s1*s2^2 + c1*l^2*s2^3 - c1*l^2*s2 - c1*l*(p / 2)*r^2*s2^3 + 2*c1*l*(p / 2)*r^2*s2 - 2*c1*l*(p / 2)*s2^3 + 4*c1*l*(p / 2)*s2 - c1*l*r^2*s2^3 - c1*l*r^2*s2 - 4*c1*l*r*s1*s2^2 - 4*c1*l*s1^2*s2 + 2*c1*l*s2^3 - 2*c1*l*s2 - c1*(p / 2)*s2^3 + 2*c1*(p / 2)*s2 + c1*s2^3 - c1*s2 - c2*l^3*(p / 2)*r^2*s1*s2^2 + c2*l^3*(p / 2)*r^2*s1 + c2*l^3*(p / 2)*r*s2 - c2*l^3*r^2*s1*s2^2 - 2*c2*l^2*(p / 2)*r^2*s1*s2^2 + 2*c2*l^2*(p / 2)*r^2*s1 + 3*c2*l^2*(p / 2)*r*s2 - c2*l^2*(p / 2)*s1*s2^2 + c2*l^2*(p / 2)*s1 - 4*c2*l^2*r^2*s1^3 - 2*c2*l^2*r^2*s1*s2^2 - 4*c2*l^2*r*s1^2*s2 + c2*l^2*s1*s2^2 - c2*l*(p / 2)*r^2*s1*s2^2 + c2*l*(p / 2)*r^2*s1 + 3*c2*l*(p / 2)*r*s2 - 2*c2*l*(p / 2)*s1*s2^2 + 2*c2*l*(p / 2)*s1 - c2*l*r^2*s1*s2^2 - 4*c2*l*r*s1^2*s2 - 4*c2*l*s1^3 + 2*c2*l*s1*s2^2 + c2*(p / 2)*r*s2 - c2*(p / 2)*s1*s2^2 + c2*(p / 2)*s1 + c2*s1*s2^2) * hD + (-s1*(l + 1)^2*(c1*s2 + c2*s1)*(l*r^2 + 1)^2) * P1 + (-(l + 1)^2*(l*r^2 + 1)*(2*c1*l*(p / 2)*r^2*s1*s2 - c1*l*(p / 2)*r*s2^2 - 2*c1*l*r^2*s1*s2 - c1*(p / 2)*r*s2^2 + 2*c1*(p / 2)*s1*s2 - 2*c1*s1*s2 + c2*l*(p / 2)*r^2*s1^2 - c2*l*r^2*s1^2 + c2*(p / 2)*s1^2 - c2*s1^2)) * P2

/-- Sign of the numerator for `λ > -1`, from `key_identity` and the (multiplied-out) Lemma A bracket `hbr`. -/
theorem E_pos_alg {l r p s1 s2 c1 c2 sn cs : ℝ} (hl : -1 < l) (hr0 : 0 < r) (hr1 : r ≤ 1) (hs2 : 0 < s2)
    (hsnp : 0 < sn) (hsn : sn = s2 * c1 + c2 * s1) (hcs : cs = c2 * c1 - s2 * s1)
    (hD : (1 + l) * r * s2 - (1 + l * r ^ 2) * s1 = 0) (P1 : s1 ^ 2 + c1 ^ 2 = 1) (P2 : s2 ^ 2 + c2 ^ 2 = 1)
    (hbr : 0 < s1 * ((1 + l) ^ 2 * c1 ^ 2 + (1 - l) ^ 2 * s1 ^ 2) - (1 - p / 2) * (1 + l) ^ 2 * c2 * sn) :
    0 < r * sn * (1 - l * r ^ 2) * ((1 + l) * s2 - 2 * l * r * s1) +
      ((1 + l) * r * (c2 * (p / 2)) - (1 + l * r ^ 2) * (c1 * (1 - p / 2))) * ((1 + l * r ^ 2) * cs + (1 + l) * r) := by
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1
  have hβ : 0 < 1 + l * r ^ 2 := by
    rcases le_or_gt 0 l with h | h
    · have := mul_nonneg h (sq_nonneg r)
      linarith
    · have := mul_le_mul_of_nonpos_left hr2 h.le
      linarith
  have hid := key_identity l r p s1 s2 c1 c2 sn cs hsn hcs hD P1 P2
  have hα : 0 < (1 + l) ^ 2 * s2 ^ 2 := mul_pos (pow_pos (by linarith) 2) (pow_pos hs2 2)
  have hrhs := mul_pos (mul_pos (pow_pos hβ 2) hsnp) hbr
  rw [← hid] at hrhs
  exact lt_of_mul_lt_mul_left (by rw [mul_zero]; exact hrhs) hα.le

/-- `∂_rD = (1 + λ)s₂ - 2λrs₁ > 0` for `0 < r ≤ 1`, `0 < s₁ < s₂`, `-1 ≤ λ < 1` (l.46; also at `λ = -1`). -/
theorem Dr_pos {lam r s1 s2 : ℝ} (hl : -1 ≤ lam) (hl1 : lam < 1) (hr0 : 0 < r) (hr1 : r ≤ 1) (hs1 : 0 < s1)
    (hs12 : s1 < s2) : 0 < (1 + lam) * s2 - 2 * lam * r * s1 := by
  have h1 : 0 ≤ (1 + lam) * (s2 - r * s1) :=
    mul_nonneg (by linarith) (by nlinarith [mul_le_mul_of_nonneg_right hr1 hs1.le])
  have h2 : 0 < (1 - lam) * r * s1 := mul_pos (mul_pos (by linarith) hr0) hs1
  have e : (1 + lam) * s2 - 2 * lam * r * s1 = (1 + lam) * (s2 - r * s1) + (1 - lam) * r * s1 := by ring
  rw [e]
  linarith

/-! ## The curve quantities -/

variable {p lam : ℝ}

/-- `A(θ) = |1 + z_θ|² = 1 + 2R cos θ + R²` (l.53). -/
noncomputable def curveA (p lam θ : ℝ) : ℝ := 1 + 2 * curveR p lam θ * Real.cos θ + curveR p lam θ ^ 2

/-- `B(θ) = |1 + λz_θ|² = 1 + 2λR cos θ + λ²R²` (l.53). -/
noncomputable def curveB (p lam θ : ℝ) : ℝ :=
  1 + 2 * lam * curveR p lam θ * Real.cos θ + lam ^ 2 * curveR p lam θ ^ 2

/-- The numerator `E = r sin θ (1 - λr²) ∂_rD + ∂_θD ((1 + λr²) cos θ + (1 + λ)r)` of `(ρ²)'`. -/
noncomputable def numE (p lam θ r : ℝ) : ℝ :=
  r * Real.sin θ * (1 - lam * r ^ 2) *
      ((1 + lam) * Real.sin (p / 2 * θ) - 2 * lam * r * Real.sin ((1 - p / 2) * θ)) +
    ((1 + lam) * r * (Real.cos (p / 2 * θ) * (p / 2)) -
        (1 + lam * r ^ 2) * (Real.cos ((1 - p / 2) * θ) * (1 - p / 2))) *
      ((1 + lam * r ^ 2) * Real.cos θ + (1 + lam) * r)

theorem curveA_pos {θ : ℝ} (hR : 0 < curveR p lam θ) (hθ0 : 0 < θ) (hθ : θ < Real.pi) : 0 < curveA p lam θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
  have e : curveA p lam θ = (1 + curveR p lam θ * Real.cos θ) ^ 2 + (curveR p lam θ * Real.sin θ) ^ 2 := by
    unfold curveA
    linear_combination (-(curveR p lam θ ^ 2)) * Real.sin_sq_add_cos_sq θ
  rw [e]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (mul_pos hR hs) 2)

theorem curveB_pos {θ : ℝ} (hR : 0 < curveR p lam θ) (hθ0 : 0 < θ) (hθ : θ < Real.pi) : 0 < curveB p lam θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
  have e : curveB p lam θ =
      (1 + lam * curveR p lam θ * Real.cos θ) ^ 2 + (lam * curveR p lam θ * Real.sin θ) ^ 2 := by
    unfold curveB
    linear_combination (-(lam ^ 2 * curveR p lam θ ^ 2)) * Real.sin_sq_add_cos_sq θ
  rw [e]
  rcases eq_or_ne lam 0 with h | h
  · subst h; norm_num
  · have hne : lam * curveR p lam θ * Real.sin θ ≠ 0 := mul_ne_zero (mul_ne_zero h hR.ne') hs.ne'
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hne).symm)

/-- `ρ(θ)² = B/A` on `(0, π)` (`dict_identities`, l.53). -/
theorem rho_sq (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ < Real.pi) : ‖mobW lam (curveZ p lam θ)‖ ^ 2 = curveB p lam θ / curveA p lam θ := by
  obtain ⟨-, -, hW, -⟩ := dict_identities hp1 hp2 hl hl1 hθ0 hθ rfl
  obtain ⟨hre, him⟩ := polar_re_im (curveR p lam θ) θ
  have hB : ‖1 + (lam : ℂ) * ((curveR p lam θ : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I))‖ ^ 2 =
      curveB p lam θ := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul, hre, him]
    unfold curveB
    linear_combination (lam * curveR p lam θ) ^ 2 * Real.sin_sq_add_cos_sq θ
  unfold curveZ
  rw [hW, hB]
  rfl

/-- `R' ∂_rD + ∂_θD = 0` on `(0, π)`: differentiate `D(θ, R(θ)) = 0` (`R` is analytic, `curve_root_analytic`). -/
theorem curveR_deriv_rel (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ < Real.pi) :
    HasDerivAt (curveR p lam) (deriv (curveR p lam) θ) θ ∧
    deriv (curveR p lam) θ *
        ((1 + lam) * Real.sin (p / 2 * θ) - 2 * lam * curveR p lam θ * Real.sin ((1 - p / 2) * θ)) +
      ((1 + lam) * curveR p lam θ * (Real.cos (p / 2 * θ) * (p / 2)) -
        (1 + lam * curveR p lam θ ^ 2) * (Real.cos ((1 - p / 2) * θ) * (1 - p / 2))) = 0 := by
  have hRd : HasDerivAt (curveR p lam) (deriv (curveR p lam) θ) θ :=
    (curve_root_analytic hp1 hp2 hl hl1 hθ0 hθ).differentiableAt.hasDerivAt
  refine ⟨hRd, ?_⟩
  have hs2 := ((hasDerivAt_id' θ).const_mul (p / 2)).sin
  have hs1 := ((hasDerivAt_id' θ).const_mul (1 - p / 2)).sin
  have h := ((hRd.const_mul (1 + lam)).mul hs2).sub ((((hRd.mul hRd).const_mul lam).const_add 1).mul hs1)
  have hg : HasDerivAt (fun x => curveD p lam x (curveR p lam x))
      (deriv (curveR p lam) θ *
          ((1 + lam) * Real.sin (p / 2 * θ) - 2 * lam * curveR p lam θ * Real.sin ((1 - p / 2) * θ)) +
        ((1 + lam) * curveR p lam θ * (Real.cos (p / 2 * θ) * (p / 2)) -
          (1 + lam * curveR p lam θ ^ 2) * (Real.cos ((1 - p / 2) * θ) * (1 - p / 2)))) θ := by
    convert h using 1
    · funext x; simp only [curveD, Pi.mul_apply, Pi.sub_apply]; ring
    · simp only [Pi.mul_apply]; ring
  have hev : (fun x => curveD p lam x (curveR p lam x)) =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
    filter_upwards [Ioo_mem_nhds hθ0 hθ] with x hx
    exact (curve_root_formula hp1 hp2 hx.1 hx.2 hl hl1).2.2.2.2
  exact hg.unique ((hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq hev)

/-- `(B/A)' = 2(1 - λ)(R sin θ (1 - λR²) - R' ((1 + λR²) cos θ + (1 + λ)R))/A²`. -/
theorem rhoSq_hasDerivAt {θ R' : ℝ} (hRd : HasDerivAt (curveR p lam) R' θ) (hA : curveA p lam θ ≠ 0) :
    HasDerivAt (fun x => curveB p lam x / curveA p lam x)
      (2 * (1 - lam) * (curveR p lam θ * Real.sin θ * (1 - lam * curveR p lam θ ^ 2) -
        R' * ((1 + lam * curveR p lam θ ^ 2) * Real.cos θ + (1 + lam) * curveR p lam θ)) / curveA p lam θ ^ 2) θ := by
  have hAd : HasDerivAt (curveA p lam)
      (2 * (R' * Real.cos θ - curveR p lam θ * Real.sin θ) + 2 * curveR p lam θ * R') θ := by
    have h := (((hRd.const_mul 2).mul (Real.hasDerivAt_cos θ)).const_add 1).add (hRd.mul hRd)
    convert h using 1
    · funext x; simp only [curveA, Pi.mul_apply, Pi.add_apply]; ring
    · ring
  have hBd : HasDerivAt (curveB p lam)
      (2 * lam * (R' * Real.cos θ - curveR p lam θ * Real.sin θ) + 2 * lam ^ 2 * curveR p lam θ * R') θ := by
    have h := (((hRd.const_mul (2 * lam)).mul (Real.hasDerivAt_cos θ)).const_add 1).add
      ((hRd.mul hRd).const_mul (lam ^ 2))
    convert h using 1
    · funext x; simp only [curveB, Pi.mul_apply, Pi.add_apply]; ring
    · ring
  convert hBd.fun_div hAd hA using 1
  rw [div_left_inj' (pow_ne_zero 2 hA)]
  simp only [curveA, curveB]
  ring

/-- `E > 0` on `(0, π)`: `E_pos_alg` with `lemmaA_bracket` for `λ > -1`; `E = 4 s₁ sin θ` for `λ = -1`. -/
theorem numE_pos (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ < Real.pi) : 0 < numE p lam θ (curveR p lam θ) := by
  obtain ⟨-, -, hR0, hR1, hDR⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  obtain ⟨hs1, hs12, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
  rcases hl.lt_or_eq with hl' | rfl
  · have hsin : Real.sin θ = Real.sin (p / 2 * θ) * Real.cos ((1 - p / 2) * θ) +
        Real.cos (p / 2 * θ) * Real.sin ((1 - p / 2) * θ) := by
      have h := Real.sin_add (p / 2 * θ) ((1 - p / 2) * θ)
      rwa [show p / 2 * θ + (1 - p / 2) * θ = θ by ring] at h
    have hcos : Real.cos θ = Real.cos (p / 2 * θ) * Real.cos ((1 - p / 2) * θ) -
        Real.sin (p / 2 * θ) * Real.sin ((1 - p / 2) * θ) := by
      have h := Real.cos_add (p / 2 * θ) ((1 - p / 2) * θ)
      rwa [show p / 2 * θ + (1 - p / 2) * θ = θ by ring] at h
    have hbr0 := lemmaA_bracket hp1 hp2 hl hl1 hθ0 hθ
    rw [norm_curveV_sq] at hbr0
    have hbr1 := mul_lt_mul_of_pos_right hbr0 hsθ
    rw [sub_mul, zero_mul, mul_assoc _ (Real.sin ((1 - p / 2) * θ) / Real.sin θ),
      div_mul_cancel₀ _ hsθ.ne'] at hbr1
    have hbr : 0 < Real.sin ((1 - p / 2) * θ) *
          ((1 + lam) ^ 2 * Real.cos ((1 - p / 2) * θ) ^ 2 + (1 - lam) ^ 2 * Real.sin ((1 - p / 2) * θ) ^ 2) -
        (1 - p / 2) * (1 + lam) ^ 2 * Real.cos (p / 2 * θ) * Real.sin θ := by
      linear_combination hbr1
    unfold numE
    exact E_pos_alg hl' hR0 hR1 (hs1.trans hs12) hsθ hsin hcos hDR (Real.sin_sq_add_cos_sq _)
      (Real.sin_sq_add_cos_sq _) hbr
  · have hR := (curve_root_minus_one hp1 hp2 hθ0 hθ).2
    rw [hR]
    have e : numE p (-1) θ 1 = 4 * Real.sin θ * Real.sin ((1 - p / 2) * θ) := by unfold numE; ring
    rw [e]
    exact mul_pos (mul_pos (by norm_num) hsθ) hs1

/-- `ρ` has a positive derivative at every `θ ∈ (0, π)`. -/
theorem rho_hasDerivAt (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ < Real.pi) : ∃ d, HasDerivAt (fun x => ‖mobW lam (curveZ p lam x)‖) d θ ∧ 0 < d := by
  obtain ⟨-, -, hR0, hR1, -⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  obtain ⟨hs1, hs12, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  have hA := curveA_pos hR0 hθ0 hθ
  have hB := curveB_pos hR0 hθ0 hθ
  obtain ⟨hRd, hrel⟩ := curveR_deriv_rel hp1 hp2 hl hl1 hθ0 hθ
  have hDr := Dr_pos hl hl1 hR0 hR1 hs1 hs12
  have hE := numE_pos hp1 hp2 hl hl1 hθ0 hθ
  have hXE : (curveR p lam θ * Real.sin θ * (1 - lam * curveR p lam θ ^ 2) -
        deriv (curveR p lam) θ * ((1 + lam * curveR p lam θ ^ 2) * Real.cos θ + (1 + lam) * curveR p lam θ)) *
      ((1 + lam) * Real.sin (p / 2 * θ) - 2 * lam * curveR p lam θ * Real.sin ((1 - p / 2) * θ)) =
      numE p lam θ (curveR p lam θ) := by
    unfold numE
    linear_combination (-((1 + lam * curveR p lam θ ^ 2) * Real.cos θ + (1 + lam) * curveR p lam θ)) * hrel
  have hX : 0 < curveR p lam θ * Real.sin θ * (1 - lam * curveR p lam θ ^ 2) -
      deriv (curveR p lam) θ * ((1 + lam * curveR p lam θ ^ 2) * Real.cos θ + (1 + lam) * curveR p lam θ) :=
    lt_of_mul_lt_mul_right (by rw [zero_mul, hXE]; exact hE) hDr.le
  have hBA : 0 < curveB p lam θ / curveA p lam θ := div_pos hB hA
  refine ⟨_, ((rhoSq_hasDerivAt hRd hA.ne').sqrt hBA.ne').congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [Ioo_mem_nhds hθ0 hθ] with x hx
    rw [← rho_sq hp1 hp2 hl hl1 hx.1 hx.2, Real.sqrt_sq (norm_nonneg _)]
  · exact div_pos (div_pos (mul_pos (mul_pos two_pos (by linarith)) hX) (pow_pos hA 2))
      (mul_pos two_pos (Real.sqrt_pos.2 hBA))

/-- `ρ → ∞` as `θ → π⁻`: `R → 1`, so `A → 0⁺` and `B → (1 - λ)² > 0` (l.85, "z_θ → -1"). -/
theorem rho_tendsto_pi (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    Tendsto (fun θ => ‖mobW lam (curveZ p lam θ)‖) (𝓝[<] Real.pi) atTop := by
  have hR := (curve_root_limits hp1 hp2 hl hl1).1
  have hcos : Tendsto Real.cos (𝓝[<] Real.pi) (𝓝 (-1)) := by
    have h := Real.continuous_cos.tendsto Real.pi
    rw [Real.cos_pi] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hmem : Set.Ioo 0 Real.pi ∈ 𝓝[<] Real.pi := Ioo_mem_nhdsLT Real.pi_pos
  have hA0 : Tendsto (curveA p lam) (𝓝[<] Real.pi) (𝓝 0) := by
    have h := (((hR.const_mul 2).mul hcos).const_add 1).add (hR.pow 2)
    rw [show (1 : ℝ) + 2 * 1 * -1 + 1 ^ 2 = 0 by norm_num] at h
    exact h
  have hA : Tendsto (curveA p lam) (𝓝[<] Real.pi) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hA0, Filter.eventually_of_mem hmem fun x hx =>
      curveA_pos (curve_root_formula hp1 hp2 hx.1 hx.2 hl hl1).2.2.1 hx.1 hx.2⟩
  have hB : Tendsto (curveB p lam) (𝓝[<] Real.pi) (𝓝 ((1 - lam) ^ 2)) := by
    have h := (((hR.const_mul (2 * lam)).mul hcos).const_add 1).add ((hR.pow 2).const_mul (lam ^ 2))
    rw [show (1 : ℝ) + 2 * lam * 1 * -1 + lam ^ 2 * 1 ^ 2 = (1 - lam) ^ 2 by ring] at h
    exact h
  have hBA := hB.pos_mul_atTop (pow_pos (by linarith) 2) (tendsto_inv_nhdsGT_zero.comp hA)
  refine (Real.tendsto_sqrt_atTop.comp hBA).congr' ?_
  filter_upwards [hmem] with x hx
  simp only [Function.comp]
  rw [← div_eq_mul_inv, ← rho_sq hp1 hp2 hl hl1 hx.1 hx.2, Real.sqrt_sq (norm_nonneg _)]

end SharpA2

/-- Reduction helper (Proposition Reduction, Steps 1-2), sec5_sharp_inequality.tex l.148, l.153: "w(θ) → ρ₀" as `θ → 0⁺`, as a
complex limit (`R → r₀` by `curve_root_limits`, `e^{-iθ} → 1`). -/
theorem curve_w_tendsto_rho0_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    Tendsto (fun θ => mobW lam (curveZ p lam θ)) (𝓝[>] 0)
      (𝓝 ((((1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) : ℝ)) : ℂ)) := by
  obtain ⟨-, hR, hr0, -⟩ := curve_root_limits hp1 hp2 hl hl1
  generalize curveRoot lam (1 - p / 2) (p / 2) = r0 at hR hr0 ⊢
  have hRc : Tendsto (fun θ => (curveR p lam θ : ℂ)) (𝓝[>] 0) (𝓝 (r0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto r0).comp hR
  have hE : Tendsto (fun θ : ℝ => Complex.exp (-(θ : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun θ : ℝ => Complex.exp (-(θ : ℂ) * Complex.I)) := by fun_prop
    have h := hc.tendsto 0
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun θ => curveZ p lam θ) (𝓝[>] 0) (𝓝 (r0 : ℂ)) := by
    have h := hRc.mul hE
    rw [mul_one] at h
    exact h
  have hden : (1 : ℂ) + r0 ≠ 0 := by
    have h : (0 : ℝ) < 1 + r0 := by linarith
    exact_mod_cast h.ne'
  have h := ((hz.const_mul (lam : ℂ)).const_add 1).div (hz.const_add 1) hden
  rw [show ((1 : ℂ) + (lam : ℂ) * (r0 : ℂ)) / (1 + (r0 : ℂ)) = (((1 + lam * r0) / (1 + r0) : ℝ) : ℂ) by
    push_cast; ring] at h
  exact h

/-- Consequence (A2), sec5_sharp_inequality.tex l.85-90: "ρ(θ) is continuous, injective, ρ → ∞ as θ → π;
so ρ increases strictly from ρ₀ := ρ(0⁺) = (1 + λr₀)/(1 + r₀) ∈ [0, 1) to ∞, and ρ′ > 0"; "If λ > 0,
ρ₀ ≥ (1+λ)/2 > √λ". (`rhoCurve p lam` is the abbreviation `fun θ => ‖mobW lam (curveZ p lam θ)‖`.) Route R8: the
derivative is computed directly (module docstring), not via (A1) and the implicit function theorem. -/
theorem sec5_A2_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    let r0 := curveRoot lam (1 - p / 2) (p / 2)
    let ρ0 := (1 + lam * r0) / (1 + r0)
    ContinuousOn (fun θ => ‖mobW lam (curveZ p lam θ)‖) (Set.Ioo 0 Real.pi) ∧
    StrictMonoOn (fun θ => ‖mobW lam (curveZ p lam θ)‖) (Set.Ioo 0 Real.pi) ∧
    Tendsto (fun θ => ‖mobW lam (curveZ p lam θ)‖) (𝓝[<] Real.pi) atTop ∧
    Tendsto (fun θ => ‖mobW lam (curveZ p lam θ)‖) (𝓝[>] 0) (𝓝 ρ0) ∧
    0 ≤ ρ0 ∧ ρ0 < 1 ∧
    (∀ θ ∈ Set.Ioo 0 Real.pi, 0 < deriv (fun θ => ‖mobW lam (curveZ p lam θ)‖) θ) ∧
    (0 < lam → (1 + lam) / 2 ≤ ρ0 ∧ Real.sqrt lam < (1 + lam) / 2) := by
  dsimp only
  obtain ⟨-, -, hr0, hr1⟩ := curve_root_limits hp1 hp2 hl hl1
  have hderiv := fun θ (hθ : θ ∈ Set.Ioo 0 Real.pi) => SharpA2.rho_hasDerivAt hp1 hp2 hl hl1 hθ.1 hθ.2
  have hcont : ContinuousOn (fun θ => ‖mobW lam (curveZ p lam θ)‖) (Set.Ioo 0 Real.pi) := fun θ hθ =>
    (hderiv θ hθ).choose_spec.1.continuousAt.continuousWithinAt
  have hpos : ∀ θ ∈ Set.Ioo 0 Real.pi, 0 < deriv (fun θ => ‖mobW lam (curveZ p lam θ)‖) θ := by
    intro θ hθ
    obtain ⟨d, hd, hd0⟩ := hderiv θ hθ
    rw [hd.deriv]
    exact hd0
  have hρ0 : 0 ≤ (1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) :=
    div_nonneg (by nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 + lam by linarith) hr0.le]) (by linarith)
  have hlim0 := (curve_w_tendsto_rho0_proved hp1 hp2 hl hl1).norm
  rw [Complex.norm_of_nonneg hρ0] at hlim0
  refine ⟨hcont, strictMonoOn_of_deriv_pos (convex_Ioo 0 Real.pi) hcont (by rw [interior_Ioo]; exact hpos),
    SharpA2.rho_tendsto_pi hp1 hp2 hl hl1, hlim0, hρ0, ?_, hpos, ?_⟩
  · generalize curveRoot lam (1 - p / 2) (p / 2) = r0 at hr0 hr1 ⊢
    rw [div_lt_one (by linarith)]
    nlinarith [mul_pos (show (0 : ℝ) < 1 - lam by linarith) hr0]
  · intro hl0
    generalize curveRoot lam (1 - p / 2) (p / 2) = r0 at hr0 hr1 ⊢
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - lam by linarith) (show (0 : ℝ) ≤ 1 - r0 by linarith)]
    · rw [Real.sqrt_lt' (by linarith)]
      nlinarith [pow_pos (show (0 : ℝ) < 1 - lam by linarith) 2]

end GKSharp
