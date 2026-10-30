/- GKSharp/Proofs/RadialMinusOne.lean - the radial computation at λ = −1 (sec4a_criterion.tex l.28, short v1.80):
"At λ = −1, r_* = 1, v = 2 and that radial computation gives ∂_y²Γ_C(0, θ₀) = pPc₀/s₀² > 0, where P = (2 + 2c₀)^q."
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactEndpoint

namespace GKSharp
open Threshold ContactCalc Set Filter
open scoped Topology ContDiff

/-- `r_*(−1) = 1` and `v(−1) = r_* + 1/r_* = 2`. -/
theorem contact_minus_one_radius (p : ℝ) : rContact p (-1) = 1 ∧ vContact p (-1) = 2 := by
  have hr : rContact p (-1) = 1 := by
    unfold rContact sigmaContact
    rw [show (1 + (-1 : ℝ)) / cs p = 0 by simp, show (0 : ℝ) ^ 2 - 4 * (-1) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  refine ⟨hr, ?_⟩
  unfold vContact
  rw [hr]
  norm_num

/-- sec4a_criterion.tex l.28: at `λ = −1`, `∂_y²Γ_C(0, θ₀) = p(2 + 2c₀)^q c₀/s₀² > 0`. -/
theorem radial_minus_one_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    dyy (gammaGK p (-1)) 0 (theta p) = p * (2 + 2 * cs p) ^ (p / 2) * cs p / sn p ^ 2 ∧
      0 < p * (2 + 2 * cs p) ^ (p / 2) * cs p / sn p ^ 2 := by
  let C := gk p (-1 : ℝ)
  let a := 2 * Real.cos (theta p)
  let A : ℝ → ℝ := fun y => 2 * Real.cosh y + a
  let B : ℝ → ℝ := fun y => 2 * Real.cosh y - a
  have hp0 : 0 < p := by linarith
  have hq : 0 < p / 2 := by linarith
  have ht0 : 0 < theta p := div_pos Real.pi_pos hp0
  have htpi : theta p < Real.pi := div_lt_self Real.pi_pos hp
  have hc0 : Real.cos (theta p) < 0 := cos_theta_negative hp hp2
  have hc1 : -1 < Real.cos (theta p) := by
    simpa only [Real.cos_pi] using Real.strictAntiOn_cos
      ⟨ht0.le, htpi.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ htpi
  have hA (y : ℝ) : 0 < A y := by dsimp [A, a]; linarith [Real.one_le_cosh y]
  have hB (y : ℝ) : 0 < B y := by dsimp [B, a]; linarith [Real.one_le_cosh y]
  have hCp : C ^ p = (C ^ 2) ^ (p / 2) := by
    rw [← Real.rpow_natCast C 2, ← Real.rpow_mul (by
      have := lt_of_le_of_lt (le_max_left _ _)
        (gk_gt_max hp (ne_of_lt hp2) (ρ := ((-1 : ℝ) : ℂ)) (by norm_num))
      linarith : 0 ≤ C)]
    congr 1
    ring
  have hslice (y : ℝ) : gammaGK p (-1) y (theta p) = C ^ p * A y ^ (p / 2) - B y ^ (p / 2) := by
    rw [sec4b_gammaGK_eq]
    dsimp [C, A, B, a]
    norm_num only [neg_one_sq, one_mul, neg_one_mul]
    congr 1
    congr 1
    rw [Real.cosh_eq]
    ring
  have hzero : gammaGK p (-1) 0 (theta p) = 0 := sec4a_gamma_endpoint hp hp2 rfl
  have hbase : C ^ 2 * A 0 = B 0 := by
    have hz := hzero
    rw [hslice, hCp, ← Real.mul_rpow (sq_nonneg C) (hA 0).le] at hz
    exact (Real.rpow_left_inj (mul_nonneg (sq_nonneg C) (hA 0).le) (hB 0).le hq.ne').mp
      (sub_eq_zero.mp hz)
  have hAd (y : ℝ) : HasDerivAt A (2 * Real.sinh y) y :=
    ((Real.hasDerivAt_cosh y).const_mul 2).add_const a
  have hBd (y : ℝ) : HasDerivAt B (2 * Real.sinh y) y :=
    ((Real.hasDerivAt_cosh y).const_mul 2).sub_const a
  let D : ℝ → ℝ := fun y => C ^ p * (2 * Real.sinh y * (p / 2) * A y ^ (p / 2 - 1)) -
    2 * Real.sinh y * (p / 2) * B y ^ (p / 2 - 1)
  have hD (y : ℝ) : HasDerivAt (fun y => gammaGK p (-1) y (theta p)) (D y) y := by
    have hh := (((hAd y).rpow_const (p := p / 2) (Or.inl (hA y).ne')).const_mul (C ^ p)).sub
      ((hBd y).rpow_const (p := p / 2) (Or.inl (hB y).ne'))
    exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall hslice)
  have hdy (y : ℝ) : dy (gammaGK p (-1)) y (theta p) = D y := (hD y).deriv
  have hD2 : HasDerivAt D (p * (C ^ p * A 0 ^ (p / 2 - 1) - B 0 ^ (p / 2 - 1))) 0 := by
    have hh := (((((Real.hasDerivAt_sinh 0).const_mul 2).mul_const (p / 2)).mul
      ((hAd 0).rpow_const (p := p / 2 - 1) (Or.inl (hA 0).ne'))).const_mul (C ^ p)).sub
      ((((Real.hasDerivAt_sinh 0).const_mul 2).mul_const (p / 2)).mul
        ((hBd 0).rpow_const (p := p / 2 - 1) (Or.inl (hB 0).ne')))
    convert hh using 1
    simp only [Real.cosh_zero, Real.sinh_zero, mul_zero, zero_mul, add_zero]
    ring
  have hpower : C ^ p * A 0 ^ (p / 2 - 1) = C ^ 2 * B 0 ^ (p / 2 - 1) := by
    rw [← hbase, Real.mul_rpow (sq_nonneg C) (hA 0).le, hCp]
    have hh : (C ^ 2) ^ (p / 2 - 1) * C ^ 2 = (C ^ 2) ^ (p / 2) := by
      rw [← Real.rpow_add_one (by
        have := lt_of_le_of_lt (le_max_left _ _)
          (gk_gt_max hp (ne_of_lt hp2) (ρ := ((-1 : ℝ) : ℂ)) (by norm_num))
        positivity : C ^ 2 ≠ 0)]
      congr 1
      ring
    rw [← hh]
    ring
  have hdyy : dyy (gammaGK p (-1)) 0 (theta p) = p * (C ^ 2 - 1) * B 0 ^ (p / 2 - 1) := by
    change deriv (fun y => dy (gammaGK p (-1)) y (theta p)) 0 = _
    rw [show (fun y => dy (gammaGK p (-1)) y (theta p)) = D from funext hdy, hD2.deriv, hpower]
    ring
  -- the closed form: `A 0 = 2 − 2c₀`, `B 0 = 2 + 2c₀`, `s₀² = 1 − c₀²`
  have hcs : cs p = -Real.cos (theta p) := rfl
  have hsn : sn p ^ 2 = 1 - cs p ^ 2 := by
    rw [hcs, neg_sq]
    unfold sn theta
    linarith [Real.sin_sq_add_cos_sq (Real.pi / p)]
  have hA0 : A 0 = 2 - 2 * cs p := by dsimp [A, a]; rw [Real.cosh_zero, hcs]; ring
  have hB0 : B 0 = 2 + 2 * cs p := by dsimp [B, a]; rw [Real.cosh_zero, hcs]; ring
  have hcpos : 0 < cs p := by rw [hcs]; linarith
  have hclt : cs p < 1 := by rw [hcs]; linarith
  have hC2 : C ^ 2 - 1 = 4 * cs p / (2 - 2 * cs p) := by
    have h2 : (0 : ℝ) < 2 - 2 * cs p := by linarith
    rw [hA0, hB0] at hbase
    field_simp
    linarith
  have hBpow : (2 + 2 * cs p) ^ (p / 2) = (2 + 2 * cs p) ^ (p / 2 - 1) * (2 + 2 * cs p) := by
    rw [← Real.rpow_add_one (by linarith : (2 + 2 * cs p) ≠ 0)]
    congr 1
    ring
  have hval : dyy (gammaGK p (-1)) 0 (theta p) = p * (2 + 2 * cs p) ^ (p / 2) * cs p / sn p ^ 2 := by
    rw [hdyy, hC2, hB0, hBpow, hsn]
    have h1 : (0 : ℝ) < 1 - cs p := by linarith
    have h2 : (0 : ℝ) < 1 + cs p := by linarith
    have h3 : (1 - cs p ^ 2) ≠ 0 := by nlinarith
    have h4 : (2 - 2 * cs p) ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨hval, ?_⟩
  have hsn0 : 0 < sn p ^ 2 := by rw [hsn]; nlinarith
  have hP : 0 < (2 + 2 * cs p) ^ (p / 2) := Real.rpow_pos_of_pos (by linarith) _
  positivity

end GKSharp
