/- GKSharp/Proofs/Sec4bContactDeriv.lean - slice (b): the contact derivative values and Γ_yy > 0 (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Row of PROPOSAL_CHECKS_THRESHOLDS.lean v1.00 as `<row>_proved` with the row's exact type.
- contact_derivative_values (B:45-50). With `R = e^y`, `P_a = R² + 2aR cos t + a² = ‖ζ + a‖²`: `χ_a = (log P_a)/2`
  everywhere, and on `y > 0` (both `P` positive) `L = log C - χ_λ + χ_1`. So `∂_y χ_a = (R² + aR cos t)/P_a`,
  `∂_t χ_a = -aR sin t/P_a`, `∂_y² χ_a = aR(R² cos t + 2aR + a² cos t)/P_a²`, `∂_t∂_y χ_a = aR sin t (R² - a²)/P_a²`.
  At the contact `R = r`, `cos θ = -cs`, `sin θ = sn`; with `cs = (1+λ)r/(r²+λ)`, `sn² = (r²-1)(r²-λ²)/(r²+λ)²`
  (contact_rational_identities): `P_1 = (r²-1)(r²-λ)/(r²+λ)`, `P_λ = (r²-λ²)(r²-λ)/(r²+λ)`, and the values are
  rational identities in `r, λ`. `Γ_yy > 0`: with `B₁ = 2cosh y + 2cos θ`, `B₂ = e^y + λ²e^{-y} + 2λ cos θ`, at the
  contact `B₂ = C²B₁` (contact square gap) and `B₂' = C²B₁'` (`C²(r² - 1) = r² - λ²`, contact radius), so the `(q-1)`
  terms cancel: `Γ_yy = q (C²)^{q-2} B₁^{q-2} C² B₁ (r(C² - 1) + (C² - λ²)/r) > 0`; the same identities give `Γ_y = 0`.
-/
import GKSharp.Proofs.ContactRay
import GKSharp.Proofs.Sec4bLocal

namespace GKSharp

open Set Filter GKSharp.Threshold
open scoped Topology

/-- `‖ζ(y, t) + a‖² = e^{2y} + 2a e^y cos t + a²`. -/
lemma sec4b_norm_zeta_add_sq (a y t : ℝ) :
    ‖zeta y t + (a : ℂ)‖ ^ 2 = Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos t + a ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [zeta, Complex.exp_re, Complex.exp_im]
  linear_combination Real.exp y * Real.exp y * Real.sin_sq_add_cos_sq t

/-- `χ_a = (log P_a)/2` (the log of a norm is half the log of its square). -/
lemma sec4b_chi_eq (a y t : ℝ) :
    chi a y t = Real.log (Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos t + a ^ 2) / 2 := by
  rw [← sec4b_norm_zeta_add_sq, Real.log_pow]
  unfold chi
  push_cast
  ring

/-- `P_a > 0` for `|a| ≤ 1 < e^y`. -/
lemma sec4b_P_pos {a y : ℝ} (ha : |a| ≤ 1) (hy : 0 < y) (t : ℝ) :
    0 < Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos t + a ^ 2 := by
  have he : 1 < Real.exp y := by linarith [Real.add_one_lt_exp hy.ne']
  have hac : |a * Real.cos t| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ha (Real.abs_cos_le_one t) (abs_nonneg _) zero_le_one).trans (by norm_num)
  have h1 : 0 < Real.exp y + a * Real.cos t := by linarith [neg_abs_le (a * Real.cos t)]
  have hid : Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos t + a ^ 2 =
      (Real.exp y + a * Real.cos t) ^ 2 + (a * Real.sin t) ^ 2 := by
    linear_combination (-a ^ 2) * Real.sin_sq_add_cos_sq t
  rw [hid]
  nlinarith [sq_nonneg (a * Real.sin t), mul_pos h1 h1]

/-- `ζ + a ≠ 0` for `|a| ≤ 1 < e^y`. -/
lemma sec4b_norm_ne {a y : ℝ} (ha : |a| ≤ 1) (hy : 0 < y) (t : ℝ) : ‖zeta y t + (a : ℂ)‖ ≠ 0 := by
  intro h
  have hsq := sec4b_norm_zeta_add_sq a y t
  rw [h] at hsq
  nlinarith [sec4b_P_pos ha hy t]

/-- On `y > 0`, `logGap = log C - χ_λ + χ_1`. -/
lemma sec4b_logGap_eq {p lam y : ℝ} (hlam : lam ∈ Ioo (-1 : ℝ) 1) (hy : 0 < y) (t : ℝ) :
    logGap p lam y t = Real.log (gk p lam) - chi lam y t + chi 1 y t := by
  have hl : |lam| ≤ 1 := abs_le.2 ⟨hlam.1.le, hlam.2.le⟩
  have h1 := sec4b_norm_ne hl hy t
  have h2 : ‖zeta y t + 1‖ ≠ 0 := by simpa using sec4b_norm_ne (a := 1) (by norm_num) hy t
  unfold logGap mobContact chi
  rw [norm_div, Real.log_div h1 h2]
  push_cast
  ring

lemma sec4b_hasDerivAt_P_y (a t y : ℝ) :
    HasDerivAt (fun x => Real.exp x * Real.exp x + 2 * a * Real.exp x * Real.cos t + a ^ 2)
      (2 * (Real.exp y * Real.exp y + a * Real.exp y * Real.cos t)) y := by
  have h := Real.hasDerivAt_exp y
  refine ((((h.mul h).add ((h.const_mul (2 * a)).mul_const (Real.cos t))).add_const (a ^ 2))).congr_deriv ?_
  ring

lemma sec4b_hasDerivAt_P_t (a y t : ℝ) :
    HasDerivAt (fun s => Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos s + a ^ 2)
      (-(2 * a * Real.exp y * Real.sin t)) t := by
  refine ((((Real.hasDerivAt_cos t).const_mul (2 * a * Real.exp y)).const_add
    (Real.exp y * Real.exp y)).add_const (a ^ 2)).congr_deriv ?_
  ring

/-- `∂_y χ_a = (R² + aR cos t)/P_a`. -/
lemma sec4b_hasDerivAt_chi_y {a y : ℝ} (t : ℝ)
    (hP : Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos t + a ^ 2 ≠ 0) :
    HasDerivAt (fun x => chi a x t)
      ((Real.exp y * Real.exp y + a * Real.exp y * Real.cos t) /
        (Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos t + a ^ 2)) y := by
  have hf : (fun x => chi a x t) = fun x =>
      Real.log (Real.exp x * Real.exp x + 2 * a * Real.exp x * Real.cos t + a ^ 2) / 2 :=
    funext fun x => sec4b_chi_eq a x t
  rw [hf]
  refine (((sec4b_hasDerivAt_P_y a t y).log hP).div_const 2).congr_deriv ?_
  ring

/-- `∂_t χ_a = -aR sin t/P_a`. -/
lemma sec4b_hasDerivAt_chi_t {a y t : ℝ}
    (hP : Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos t + a ^ 2 ≠ 0) :
    HasDerivAt (fun s => chi a y s)
      (-(a * Real.exp y * Real.sin t) /
        (Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos t + a ^ 2)) t := by
  have hf : (fun s => chi a y s) = fun s =>
      Real.log (Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos s + a ^ 2) / 2 :=
    funext fun s => sec4b_chi_eq a y s
  rw [hf]
  refine (((sec4b_hasDerivAt_P_t a y t).log hP).div_const 2).congr_deriv ?_
  ring

/-- `∂_y` of the `y`-slope `(R² + aR cos t)/P_a`. -/
lemma sec4b_hasDerivAt_slope_y {a y : ℝ} (t : ℝ)
    (hP : Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos t + a ^ 2 ≠ 0) :
    HasDerivAt (fun x => (Real.exp x * Real.exp x + a * Real.exp x * Real.cos t) /
        (Real.exp x * Real.exp x + 2 * a * Real.exp x * Real.cos t + a ^ 2))
      (a * Real.exp y * (Real.exp y * Real.exp y * Real.cos t + 2 * a * Real.exp y + a ^ 2 * Real.cos t) /
        (Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos t + a ^ 2) ^ 2) y := by
  have h := Real.hasDerivAt_exp y
  have hN : HasDerivAt (fun x => Real.exp x * Real.exp x + a * Real.exp x * Real.cos t)
      (2 * (Real.exp y * Real.exp y) + a * Real.exp y * Real.cos t) y :=
    ((h.mul h).add ((h.const_mul a).mul_const (Real.cos t))).congr_deriv (by ring)
  refine (hN.div (sec4b_hasDerivAt_P_y a t y) hP).congr_deriv ?_
  ring

/-- `∂_t` of the `y`-slope `(R² + aR cos t)/P_a`. -/
lemma sec4b_hasDerivAt_slope_t {a y t : ℝ}
    (hP : Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos t + a ^ 2 ≠ 0) :
    HasDerivAt (fun s => (Real.exp y * Real.exp y + a * Real.exp y * Real.cos s) /
        (Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos s + a ^ 2))
      (a * Real.exp y * Real.sin t * (Real.exp y * Real.exp y - a ^ 2) /
        (Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos t + a ^ 2) ^ 2) t := by
  have hN : HasDerivAt (fun s => Real.exp y * Real.exp y + a * Real.exp y * Real.cos s)
      (-(a * Real.exp y * Real.sin t)) t :=
    (((Real.hasDerivAt_cos t).const_mul (a * Real.exp y)).const_add (Real.exp y * Real.exp y)).congr_deriv
      (by ring)
  refine (hN.div (sec4b_hasDerivAt_P_t a y t) hP).congr_deriv ?_
  ring

/-- On `x > 0`: `∂_y L = -(R² + λR cos t)/P_λ + (R² + R cos t)/P_1`. -/
lemma sec4b_dy_logGap {p lam x : ℝ} (hlam : lam ∈ Ioo (-1 : ℝ) 1) (hx : 0 < x) (s : ℝ) :
    dy (logGap p lam) x s =
      0 - (Real.exp x * Real.exp x + lam * Real.exp x * Real.cos s) /
          (Real.exp x * Real.exp x + 2 * lam * Real.exp x * Real.cos s + lam ^ 2) +
        (Real.exp x * Real.exp x + 1 * Real.exp x * Real.cos s) /
          (Real.exp x * Real.exp x + 2 * 1 * Real.exp x * Real.cos s + 1 ^ 2) := by
  have hl : |lam| ≤ 1 := abs_le.2 ⟨hlam.1.le, hlam.2.le⟩
  have hev : (fun x' => logGap p lam x' s) =ᶠ[𝓝 x]
      fun x' => Real.log (gk p lam) - chi lam x' s + chi 1 x' s := by
    filter_upwards [Ioi_mem_nhds hx] with x' hx'
    exact sec4b_logGap_eq hlam hx' s
  have hd : HasDerivAt (fun x' => Real.log (gk p lam) - chi lam x' s + chi 1 x' s) _ x :=
    ((hasDerivAt_const x _).sub (sec4b_hasDerivAt_chi_y s (sec4b_P_pos hl hx s).ne')).add
      (sec4b_hasDerivAt_chi_y s (sec4b_P_pos (a := 1) (by norm_num) hx s).ne')
  show deriv (fun x' => logGap p lam x' s) x = _
  rw [hev.deriv_eq, hd.deriv]

/-- The contact data in closed form: `P_1`, `P_λ` at `(log r, θ)` and the bounds on `r`. -/
lemma sec4b_contact_P {p lam : ℝ} (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let r := rContact p lam
    r * r + 2 * lam * r * -cs p + lam ^ 2 = (r ^ 2 - lam ^ 2) * (r ^ 2 - lam) / (r ^ 2 + lam) ∧
    r * r + 2 * 1 * r * -cs p + 1 ^ 2 = (r ^ 2 - 1) * (r ^ 2 - lam) / (r ^ 2 + lam) := by
  dsimp only
  obtain ⟨hr1, -, -, -⟩ := contact_root_properties hp hp2 hlam
  obtain ⟨hcsr, -, -⟩ := contact_rational_identities_proved p lam hp hp2 hlam
  have hS : rContact p lam ^ 2 + lam ≠ 0 := by nlinarith [hlam.1]
  constructor
  · rw [hcsr]; field_simp; ring
  · rw [hcsr]; field_simp; ring

/-- B:45-50, row `contact_derivative_values`, the five `χ`/`logGap` values (part 1). -/
theorem sec4b_contact_chi_values (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let t := theta p
    let v := vContact p lam
    dt (logGap p lam) y t = -(1 - lam) / (sn p * v) ∧
    dyy (logGap p lam) y t = (1 - lam) * cs p / (sn p ^ 2 * v) ∧
    dty (logGap p lam) y t = (1 - lam) * sigmaContact p lam / (sn p * v ^ 2) ∧
    dy (chi lam) y t = (1 - lam / rContact p lam * cs p) / dOne p lam ∧
    dt (chi lam) y t = -(lam / rContact p lam * sn p) / dOne p lam ∧
    dy (logGap p lam) y t = 0 := by
  dsimp only
  obtain ⟨hr1, -, -, -⟩ := contact_root_properties hp hp2 hlam
  obtain ⟨hcsr, hsnr, -⟩ := contact_rational_identities_proved p lam hp hp2 hlam
  obtain ⟨hPlc, hP1c⟩ := sec4b_contact_P hp hp2 hlam
  have hsn := sec4a_sn_pos hp
  have hl : |lam| ≤ 1 := abs_le.2 ⟨hlam.1.le, hlam.2.le⟩
  have hθc : Real.cos (theta p) = -cs p := by unfold theta cs; ring
  have hθs : Real.sin (theta p) = sn p := rfl
  unfold yContact vContact sigmaContact dOne
  obtain ⟨r, hr⟩ : ∃ r, r = rContact p lam := ⟨_, rfl⟩
  rw [← hr]
  rw [← hr] at hr1 hcsr hsnr hPlc hP1c
  have hr0 : 0 < r := by linarith
  have hrne : r ≠ 0 := hr0.ne'
  have hy0 : 0 < Real.log r := Real.log_pos hr1
  have hey : Real.exp (Real.log r) = r := Real.exp_log hr0
  have hS : r ^ 2 + lam ≠ 0 := by nlinarith [hlam.1]
  have hA : r ^ 2 - lam ^ 2 ≠ 0 := by nlinarith [hlam.1, hlam.2]
  have hB : r ^ 2 - lam ≠ 0 := by nlinarith [hlam.2]
  have hC : r ^ 2 - 1 ≠ 0 := by nlinarith
  have hB' : r * r - lam ≠ 0 := by nlinarith [hlam.2]
  have h1l : 1 + lam ≠ 0 := by linarith [hlam.1]
  have hsne : sn p ≠ 0 := hsn.ne'
  have hv : r - lam / r ≠ 0 := by
    rw [sub_ne_zero]; intro h; field_simp at h; nlinarith [hlam.2]
  have hPl := sec4b_P_pos hl hy0 (theta p)
  have hP1 := sec4b_P_pos (a := 1) (by norm_num) hy0 (theta p)
  have hdyL := sec4b_dy_logGap (p := p) hlam hy0
  -- `1/sn = sn/sn²`
  have hinvsn : ∀ X Y : ℝ, X / (sn p * Y) = X * sn p / (sn p ^ 2 * Y) := fun X Y => by
    rw [pow_two, mul_assoc, mul_comm X (sn p), mul_div_mul_left X (sn p * Y) hsne]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `∂_t L`
    have hf : (fun s => logGap p lam (Real.log r) s) =
        fun s => Real.log (gk p lam) - chi lam (Real.log r) s + chi 1 (Real.log r) s :=
      funext fun s => sec4b_logGap_eq hlam hy0 s
    have hd : HasDerivAt (fun s => Real.log (gk p lam) - chi lam (Real.log r) s + chi 1 (Real.log r) s) _
        (theta p) :=
      ((hasDerivAt_const _ _).sub (sec4b_hasDerivAt_chi_t hPl.ne')).add (sec4b_hasDerivAt_chi_t hP1.ne')
    show deriv (fun s => logGap p lam (Real.log r) s) (theta p) = _
    rw [hf, hd.deriv, hey, hθc, hθs, hPlc, hP1c, hinvsn, hsnr]
    field_simp
    ring
  · -- `∂_y² L`
    have hev : (fun x => dy (logGap p lam) x (theta p)) =ᶠ[𝓝 (Real.log r)] fun x =>
        0 - (Real.exp x * Real.exp x + lam * Real.exp x * Real.cos (theta p)) /
            (Real.exp x * Real.exp x + 2 * lam * Real.exp x * Real.cos (theta p) + lam ^ 2) +
          (Real.exp x * Real.exp x + 1 * Real.exp x * Real.cos (theta p)) /
            (Real.exp x * Real.exp x + 2 * 1 * Real.exp x * Real.cos (theta p) + 1 ^ 2) := by
      filter_upwards [Ioi_mem_nhds hy0] with x hx
      exact sec4b_dy_logGap hlam hx (theta p)
    have hd : HasDerivAt (fun x =>
        0 - (Real.exp x * Real.exp x + lam * Real.exp x * Real.cos (theta p)) /
            (Real.exp x * Real.exp x + 2 * lam * Real.exp x * Real.cos (theta p) + lam ^ 2) +
          (Real.exp x * Real.exp x + 1 * Real.exp x * Real.cos (theta p)) /
            (Real.exp x * Real.exp x + 2 * 1 * Real.exp x * Real.cos (theta p) + 1 ^ 2)) _ (Real.log r) :=
      ((hasDerivAt_const _ _).sub (sec4b_hasDerivAt_slope_y (theta p) hPl.ne')).add
        (sec4b_hasDerivAt_slope_y (theta p) hP1.ne')
    show deriv (fun x => dy (logGap p lam) x (theta p)) (Real.log r) = _
    rw [hev.deriv_eq, hd.deriv, hey, hθc, hPlc, hP1c, hsnr, hcsr]
    field_simp
    ring
  · -- `∂_t ∂_y L`
    have hf : (fun s => dy (logGap p lam) (Real.log r) s) = fun s =>
        0 - (Real.exp (Real.log r) * Real.exp (Real.log r) + lam * Real.exp (Real.log r) * Real.cos s) /
            (Real.exp (Real.log r) * Real.exp (Real.log r) + 2 * lam * Real.exp (Real.log r) * Real.cos s +
              lam ^ 2) +
          (Real.exp (Real.log r) * Real.exp (Real.log r) + 1 * Real.exp (Real.log r) * Real.cos s) /
            (Real.exp (Real.log r) * Real.exp (Real.log r) + 2 * 1 * Real.exp (Real.log r) * Real.cos s +
              1 ^ 2) :=
      funext fun s => hdyL s
    have hd : HasDerivAt (fun s =>
        0 - (Real.exp (Real.log r) * Real.exp (Real.log r) + lam * Real.exp (Real.log r) * Real.cos s) /
            (Real.exp (Real.log r) * Real.exp (Real.log r) + 2 * lam * Real.exp (Real.log r) * Real.cos s +
              lam ^ 2) +
          (Real.exp (Real.log r) * Real.exp (Real.log r) + 1 * Real.exp (Real.log r) * Real.cos s) /
            (Real.exp (Real.log r) * Real.exp (Real.log r) + 2 * 1 * Real.exp (Real.log r) * Real.cos s +
              1 ^ 2)) _ (theta p) :=
      ((hasDerivAt_const _ _).sub (sec4b_hasDerivAt_slope_t hPl.ne')).add (sec4b_hasDerivAt_slope_t hP1.ne')
    show deriv (fun s => dy (logGap p lam) (Real.log r) s) (theta p) = _
    rw [hf, hd.deriv, hey, hθc, hθs, hPlc, hP1c, hinvsn, hsnr, hcsr]
    field_simp
    ring
  · -- `∂_y χ_λ`
    show deriv (fun x => chi lam x (theta p)) (Real.log r) = _
    rw [(sec4b_hasDerivAt_chi_y (theta p) hPl.ne').deriv, hey, hθc]
    rw [div_eq_div_iff (by rw [hey, hθc] at hPl; exact hPl.ne') (by
      intro h; field_simp at h; rw [hey, hθc] at hPl; nlinarith)]
    field_simp
    ring
  · -- `∂_t χ_λ`
    show deriv (fun s => chi lam (Real.log r) s) (theta p) = _
    rw [(sec4b_hasDerivAt_chi_t hPl.ne').deriv, hey, hθc, hθs]
    rw [div_eq_div_iff (by rw [hey, hθc] at hPl; exact hPl.ne') (by
      intro h; field_simp at h; rw [hey, hθc] at hPl; nlinarith)]
    field_simp
    ring
  · -- `∂_y L = 0` at the contact (support lemma)
    rw [hdyL, hey, hθc, hPlc, hP1c, hcsr]
    field_simp
    ring

/-- `Γ_GK(y, t) = C^p (2cosh y + 2cos t)^q - (e^y + λ² e^{-y} + 2λ cos t)^q` (real `λ`). -/
lemma sec4b_gammaGK_eq (p lam y t : ℝ) :
    gammaGK p lam y t = gk p lam ^ p * (2 * Real.cosh y + 2 * Real.cos t) ^ (p / 2) -
      (Real.exp y + lam ^ 2 * Real.exp (-y) + 2 * (lam * Real.cos t)) ^ (p / 2) := by
  have hn : ‖(lam : ℂ)‖ ^ 2 = lam ^ 2 := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hre : (star (lam : ℂ) * unitPoint t).re = lam * Real.cos t := by
    rw [Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul, unitPoint, Complex.exp_ofReal_mul_I_re]
  show GKSharp.gamma p (gk p lam) (lam : ℂ) y t = _
  unfold GKSharp.gamma
  rw [hn, hre]

/-- `0 < Γ_yy` and `Γ_y = 0` at the contact `(log r, θ)`. With `B₁ = 2cosh y + 2cos θ`, `B₂ = e^y + λ²e^{-y} + 2λ cos θ`:
`B₂ = C² B₁` (square gap) and `B₂' = C² B₁'` (`C²(r² - 1) = r² - λ²`), so with `X = (C²)^{q-2}`, `Y = B₁^{q-2}` the
`(q - 1)` terms cancel: `Γ_yy = q X Y C² B₁ (C²(r + 1/r) - (r + λ²/r))`, and `C²(r + 1/r) - (r + λ²/r) > 0`. -/
theorem sec4b_contact_gamma_values (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    0 < dyy (gammaGK p lam) (yContact p lam) (theta p) ∧
      dy (gammaGK p lam) (yContact p lam) (theta p) = 0 := by
  obtain ⟨hr1, -, -, -⟩ := contact_root_properties hp hp2 hlam
  obtain ⟨-, hrad⟩ := contact_gk_radius p lam hp hp2 hlam
  have hgap := contact_ray_squared_gap p lam (rContact p lam) hp hp2 hlam
  have hC1 : 1 < gk p lam := lt_of_le_of_lt (le_max_left _ _)
    (gk_gt_max hp (ne_of_lt hp2) (ρ := (lam : ℂ)) (by
      intro hh
      have hh' : lam = 1 := by exact_mod_cast hh
      linarith [hlam.2]))
  have hsn := sec4a_sn_pos hp
  have hpyth : sn p ^ 2 + cs p ^ 2 = 1 := by
    unfold sn cs; rw [neg_sq]; exact Real.sin_sq_add_cos_sq _
  have hcs1 : cs p < 1 := by nlinarith
  have hl : |lam| ≤ 1 := abs_le.2 ⟨hlam.1.le, hlam.2.le⟩
  have hθc : Real.cos (theta p) = -cs p := by unfold theta cs; ring
  unfold yContact
  obtain ⟨r, hr⟩ : ∃ r, r = rContact p lam := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = gk p lam := ⟨_, rfl⟩
  rw [← hr]
  rw [← hr] at hr1 hrad hgap
  rw [← hC] at hrad hgap hC1
  have hr0 : 0 < r := by linarith
  have hy0 : 0 < Real.log r := Real.log_pos hr1
  have hey : Real.exp (Real.log r) = r := Real.exp_log hr0
  have hC0 : 0 < C := by linarith
  have hC2 : 0 < C ^ 2 := by positivity
  have hinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
  -- `B₂ = C² B₁` and `B₂' = C² B₁'` at the contact
  have hkey : r + lam ^ 2 * r⁻¹ + 2 * (lam * -cs p) = C ^ 2 * (2 * ((r + r⁻¹) / 2) + 2 * -cs p) := by
    linear_combination (-r⁻¹) * hgap - (r - 2 * lam * cs p - C ^ 2 * r + 2 * C ^ 2 * cs p) * hinv
  have hrad' : C ^ 2 * (r ^ 2 - 1) = r ^ 2 - lam ^ 2 := by
    have hne : r ^ 2 - 1 ≠ 0 := by nlinarith
    rw [hrad]; field_simp
  have hkey2 : r - lam ^ 2 * r⁻¹ = C ^ 2 * (2 * ((r - r⁻¹) / 2)) := by
    linear_combination (-r⁻¹) * hrad' - r * (1 - C ^ 2) * hinv
  obtain ⟨b, hbdef⟩ : ∃ b, b = 2 * ((r + r⁻¹) / 2) + 2 * -cs p := ⟨_, rfl⟩
  have hsum2 : 2 ≤ r + r⁻¹ := by
    have he : (r - 1) ^ 2 * r⁻¹ = r + r⁻¹ - 2 := by linear_combination (r - 2) * hinv
    have := mul_nonneg (sq_nonneg (r - 1)) (inv_pos.2 hr0).le
    linarith
  have hb : 0 < b := by rw [hbdef]; linarith
  -- rpow bookkeeping
  have hCp : C ^ p = (C ^ 2) ^ (p / 2) := by
    rw [← Real.rpow_natCast C 2, ← Real.rpow_mul hC0.le]
    congr 1
    push_cast
    ring
  have hX1 : (C ^ 2) ^ (p / 2 - 1 - 1) * C ^ 2 = (C ^ 2) ^ (p / 2 - 1) := by
    rw [← Real.rpow_add_one hC2.ne']
    congr 1
    ring
  have hX2 : (C ^ 2) ^ (p / 2 - 1) * C ^ 2 = (C ^ 2) ^ (p / 2) := by
    rw [← Real.rpow_add_one hC2.ne']
    congr 1
    ring
  have hY1 : b ^ (p / 2 - 1 - 1) * b = b ^ (p / 2 - 1) := by
    rw [← Real.rpow_add_one hb.ne']
    congr 1
    ring
  -- `Γ` along `t = θ` and its first two `y`-derivatives
  have hGeq : (fun x => gammaGK p lam x (theta p)) = fun x =>
      C ^ p * (2 * Real.cosh x + 2 * Real.cos (theta p)) ^ (p / 2) -
        (Real.exp x + lam ^ 2 * Real.exp (-x) + 2 * (lam * Real.cos (theta p))) ^ (p / 2) := by
    funext x
    rw [sec4b_gammaGK_eq, ← hC]
  have hB1pos : ∀ x, 0 < 2 * Real.cosh x + 2 * Real.cos (theta p) := fun x => by
    rw [hθc]; linarith [Real.one_le_cosh x]
  have hB2pos : ∀ x, 0 < x → 0 < Real.exp x + lam ^ 2 * Real.exp (-x) + 2 * (lam * Real.cos (theta p)) := by
    intro x hx
    have hP := sec4b_P_pos hl hx (theta p)
    have hm : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hprod : (Real.exp x + lam ^ 2 * Real.exp (-x) + 2 * (lam * Real.cos (theta p))) * Real.exp x =
        Real.exp x * Real.exp x + 2 * lam * Real.exp x * Real.cos (theta p) + lam ^ 2 := by
      linear_combination lam ^ 2 * hm
    exact (pos_iff_pos_of_mul_pos (by rw [hprod]; exact hP)).2 (Real.exp_pos x)
  have hB1d : ∀ x, HasDerivAt (fun x => 2 * Real.cosh x + 2 * Real.cos (theta p)) (2 * Real.sinh x) x :=
    fun x => ((Real.hasDerivAt_cosh x).const_mul 2).add_const _
  have hB2d : ∀ x, HasDerivAt (fun x => Real.exp x + lam ^ 2 * Real.exp (-x) + 2 * (lam * Real.cos (theta p)))
      (Real.exp x - lam ^ 2 * Real.exp (-x)) x := fun x =>
    (((Real.hasDerivAt_exp x).add (((hasDerivAt_neg x).exp).const_mul (lam ^ 2))).add_const _).congr_deriv
      (by ring)
  have hB2d' : ∀ x, HasDerivAt (fun x => Real.exp x - lam ^ 2 * Real.exp (-x))
      (Real.exp x + lam ^ 2 * Real.exp (-x)) x := fun x =>
    ((Real.hasDerivAt_exp x).sub (((hasDerivAt_neg x).exp).const_mul (lam ^ 2))).congr_deriv (by ring)
  have hGd : ∀ x, 0 < x → HasDerivAt (fun x =>
      C ^ p * (2 * Real.cosh x + 2 * Real.cos (theta p)) ^ (p / 2) -
        (Real.exp x + lam ^ 2 * Real.exp (-x) + 2 * (lam * Real.cos (theta p))) ^ (p / 2))
      (C ^ p * (2 * Real.sinh x * (p / 2) * (2 * Real.cosh x + 2 * Real.cos (theta p)) ^ (p / 2 - 1)) -
        (Real.exp x - lam ^ 2 * Real.exp (-x)) * (p / 2) *
          (Real.exp x + lam ^ 2 * Real.exp (-x) + 2 * (lam * Real.cos (theta p))) ^ (p / 2 - 1)) x :=
    fun x hx => (((hB1d x).rpow_const (Or.inl (hB1pos x).ne')).const_mul (C ^ p)).sub
      ((hB2d x).rpow_const (Or.inl (hB2pos x hx).ne'))
  constructor
  · have hev : (fun x => dy (gammaGK p lam) x (theta p)) =ᶠ[𝓝 (Real.log r)] fun x =>
        C ^ p * (2 * Real.sinh x * (p / 2) * (2 * Real.cosh x + 2 * Real.cos (theta p)) ^ (p / 2 - 1)) -
          (Real.exp x - lam ^ 2 * Real.exp (-x)) * (p / 2) *
            (Real.exp x + lam ^ 2 * Real.exp (-x) + 2 * (lam * Real.cos (theta p))) ^ (p / 2 - 1) := by
      filter_upwards [Ioi_mem_nhds hy0] with x hx
      show deriv (fun x' => gammaGK p lam x' (theta p)) x = _
      rw [hGeq, (hGd x hx).deriv]
    have hG2 : HasDerivAt (fun x =>
        C ^ p * (2 * Real.sinh x * (p / 2) * (2 * Real.cosh x + 2 * Real.cos (theta p)) ^ (p / 2 - 1)) -
          (Real.exp x - lam ^ 2 * Real.exp (-x)) * (p / 2) *
            (Real.exp x + lam ^ 2 * Real.exp (-x) + 2 * (lam * Real.cos (theta p))) ^ (p / 2 - 1)) _
        (Real.log r) :=
      (((((Real.hasDerivAt_sinh _).const_mul 2).mul_const (p / 2)).mul
          ((hB1d _).rpow_const (Or.inl (hB1pos _).ne'))).const_mul (C ^ p)).sub
        (((hB2d' _).mul_const (p / 2)).mul ((hB2d _).rpow_const (Or.inl (hB2pos _ hy0).ne')))
    show 0 < deriv (fun x => dy (gammaGK p lam) x (theta p)) (Real.log r)
    rw [hev.deriv_eq, hG2.deriv, Real.cosh_eq, Real.sinh_eq, Real.exp_neg, hey, hθc, hkey, hkey2, ← hbdef,
      Real.mul_rpow hC2.le hb.le, Real.mul_rpow hC2.le hb.le, hCp, ← hX2, ← hX1, ← hY1]
    have hX : 0 < (C ^ 2) ^ (p / 2 - 1 - 1) := Real.rpow_pos_of_pos hC2 _
    have hY : 0 < b ^ (p / 2 - 1 - 1) := Real.rpow_pos_of_pos hb _
    have hlam2 : lam ^ 2 < 1 := by
      linarith only [mul_pos (sub_pos.2 hlam.2) (show 0 < 1 + lam by linarith only [hlam.1])]
    have hCsq : 1 < C ^ 2 := by nlinarith only [hC1]
    have hF : 0 < C ^ 2 * (r + r⁻¹) - (r + lam ^ 2 * r⁻¹) := by
      have h1 := mul_pos hr0 (show 0 < C ^ 2 - 1 by linarith only [hCsq])
      have h2 := mul_pos (inv_pos.2 hr0) (show 0 < C ^ 2 - lam ^ 2 by linarith only [hCsq, hlam2])
      linarith only [h1, h2]
    have key := mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (show (0 : ℝ) < p / 2 by linarith only [hp]) hX)
      hY) hC2) hb) hF
    convert key using 1
    ring
  · show deriv (fun x => gammaGK p lam x (theta p)) (Real.log r) = 0
    rw [hGeq, (hGd _ hy0).deriv, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, hey, hθc, hkey, hkey2, ← hbdef,
      Real.mul_rpow hC2.le hb.le, hCp, ← hX2]
    ring

/-- Support: `∂_y logGap = 0` at the contact. -/
theorem sec4b_contact_dy_logGap_zero (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    dy (logGap p lam) (yContact p lam) (theta p) = 0 :=
  (sec4b_contact_chi_values p lam hp hp2 hlam).2.2.2.2.2

/-- Support: `∂_y Γ_GK = 0` at the contact. -/
theorem sec4b_contact_dy_gammaGK_zero (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    dy (gammaGK p lam) (yContact p lam) (theta p) = 0 :=
  (sec4b_contact_gamma_values p lam hp hp2 hlam).2

/-- B:45-50, row `contact_derivative_values`. -/
theorem contact_derivative_values_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let t := theta p
    let v := vContact p lam
    dt (logGap p lam) y t = -(1 - lam) / (sn p * v) ∧
    dyy (logGap p lam) y t = (1 - lam) * cs p / (sn p ^ 2 * v) ∧
    dty (logGap p lam) y t = (1 - lam) * sigmaContact p lam / (sn p * v ^ 2) ∧
    dy (chi lam) y t = (1 - lam / rContact p lam * cs p) / dOne p lam ∧
    dt (chi lam) y t = -(lam / rContact p lam * sn p) / dOne p lam ∧
    0 < dyy (gammaGK p lam) y t := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := sec4b_contact_chi_values p lam hp hp2 hlam
  exact ⟨h1, h2, h3, h4, h5, (sec4b_contact_gamma_values p lam hp hp2 hlam).1⟩

end GKSharp
