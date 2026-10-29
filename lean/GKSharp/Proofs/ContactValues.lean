/-
GKSharp/Proofs/ContactValues.lean — paper 019 (sec4b_failure.tex l. 39, 45-46): rows `sec4_contact_G_factor` and
`sec4_contact_complex_values`, with the exact types of the statement draft (b1.30).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Route (G factor): `G = C^p‖ζ+1‖^p - ‖ζ+λ‖^p`, `P = ‖ζ+λ‖^p`, `e^{pL} = C^p‖ζ+1‖^p/‖ζ+λ‖^p` when both bases are nonzero.
-/
import GKSharp.Defs.ThresholdAnalysis
import GKSharp.Proofs.ContactScalar
import GKSharp.Proofs.GKRoot

namespace GKSharp

open Set Threshold

/-- sec4b l.39, row `sec4_contact_G_factor`: `G = P (e^{pL} - 1)` where both logarithm bases are nonzero. -/
theorem sec4_contact_G_factor_proved (p lam y t : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1)
    (hz : zeta y t + (lam : ℂ) ≠ 0) (hz1 : zeta y t + 1 ≠ 0) :
    bigG p (gk p lam) lam (zeta y t) =
      weightP p lam y t * (Real.exp (p * logGap p lam y t) - 1) := by
  have hC : 0 < gk p lam :=
    lt_of_le_of_lt (zero_le_one.trans (le_max_left _ _)) (gk_gt_max hp (ne_of_lt hp2) (ρ := (lam : ℂ))
      (fun hh => by
        have : lam = 1 := by exact_mod_cast hh
        linarith [hlam.2]))
  have hl := norm_pos_iff.2 hz
  have h1 := norm_pos_iff.2 hz1
  simp only [bigG, GKSharp.obstacleG, weightP, chi, logGap, mobContact, norm_div]
  rw [Real.log_div hl.ne' h1.ne', add_comm (1 : ℂ) (zeta y t), add_comm ((lam : ℝ) : ℂ) (zeta y t),
    Real.rpow_def_of_pos h1, Real.rpow_def_of_pos hl, Real.rpow_def_of_pos hC]
  have e : p * (Real.log (gk p lam) - (Real.log ‖zeta y t + (lam : ℂ)‖ - Real.log ‖zeta y t + 1‖)) =
      Real.log (gk p lam) * p + Real.log ‖zeta y t + 1‖ * p - Real.log ‖zeta y t + (lam : ℂ)‖ * p := by ring
  rw [e, Real.exp_sub, Real.exp_add, mul_comm p (Real.log ‖zeta y t + (lam : ℂ)‖)]
  field_simp

/-- sec4b l.45–46, row `sec4_contact_complex_values`: the four printed complex identities at the contact. -/
theorem sec4_contact_complex_values_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let zz : ℂ := (rContact p lam : ℂ) * Complex.exp (Complex.I * (theta p : ℂ))
    let uu : ℂ := (yContact p lam : ℂ) + Complex.I * (theta p : ℂ)
    let vv : ℂ := ((sn p * vContact p lam : ℝ) : ℂ)
    (zz + (lam : ℂ)) * (zz + 1) / zz = Complex.I * vv ∧
    (1 - (lam : ℂ)) * zz / ((zz + (lam : ℂ)) * (zz + 1)) =
      -Complex.I * (((1 - lam) / (sn p * vContact p lam) : ℝ) : ℂ) ∧
    deriv (fun u : ℂ => (1 - (lam : ℂ)) * Complex.exp u /
      ((Complex.exp u + (lam : ℂ)) * (Complex.exp u + 1))) uu =
      (1 - (lam : ℂ)) * (zz - (lam : ℂ) / zz) / vv ^ 2 ∧
    zz - (lam : ℂ) / zz = -((cs p * vContact p lam : ℝ) : ℂ) +
      Complex.I * ((sn p * sigmaContact p lam : ℝ) : ℂ) := by
  dsimp only
  obtain ⟨hr1, -, hv0, hsum⟩ := contact_root_properties hp hp2 hlam
  have hp0 : 0 < p := by linarith
  have hsn : 0 < sn p :=
    Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hp0) (div_lt_self Real.pi_pos hp)
  have hcs0 : 0 < cs p := by
    have hthalf : Real.pi / 2 < Real.pi / p := by
      rw [lt_div_iff₀ hp0]
      nlinarith [Real.pi_pos]
    have htpi : Real.pi / p < Real.pi := div_lt_self Real.pi_pos hp
    unfold cs
    exact neg_pos.mpr (Real.cos_neg_of_pi_div_two_lt_of_lt hthalf (by linarith))
  have htrig : sn p ^ 2 + cs p ^ 2 = 1 := by
    simp only [sn, cs, neg_sq]
    exact Real.sin_sq_add_cos_sq _
  have hsig : sigmaContact p lam * cs p = 1 + lam := by
    unfold sigmaContact
    field_simp
  obtain ⟨r, hr⟩ : ∃ x, x = rContact p lam := ⟨_, rfl⟩
  have hr0 : r ≠ 0 := by rw [hr]; linarith
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0
  have hσC : ((sigmaContact p lam : ℝ) : ℂ) = (r : ℂ) + (lam : ℂ) / (r : ℂ) := by
    rw [← hsum, hr]
    push_cast
    ring
  have hvC : ((vContact p lam : ℝ) : ℂ) = (r : ℂ) - (lam : ℂ) / (r : ℂ) := by
    rw [hr]
    unfold vContact
    push_cast
    ring
  have hsigC : ((sigmaContact p lam : ℝ) : ℂ) * ((cs p : ℝ) : ℂ) = 1 + (lam : ℂ) := by
    rw [← Complex.ofReal_mul, hsig]
    push_cast
    ring
  have htrigC : ((sn p : ℝ) : ℂ) ^ 2 + ((cs p : ℝ) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, htrig, Complex.ofReal_one]
  have hE : Complex.exp (Complex.I * (theta p : ℂ)) = -((cs p : ℝ) : ℂ) + ((sn p : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp [theta, cs, sn]
  obtain ⟨z, hz⟩ : ∃ w : ℂ, w = (rContact p lam : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)) := ⟨_, rfl⟩
  rw [← hz]
  have hz' : z = (r : ℂ) * (-((cs p : ℝ) : ℂ) + ((sn p : ℝ) : ℂ) * Complex.I) := by rw [hz, hE, hr]
  have hz0 : z ≠ 0 := by rw [hz, ← hr]; exact mul_ne_zero hrC (Complex.exp_ne_zero _)
  have hzinv : z⁻¹ = (r : ℂ)⁻¹ * (-((cs p : ℝ) : ℂ) - ((sn p : ℝ) : ℂ) * Complex.I) := by
    apply inv_eq_of_mul_eq_one_right
    rw [hz', show (r : ℂ) * (-((cs p : ℝ) : ℂ) + ((sn p : ℝ) : ℂ) * Complex.I) *
        ((r : ℂ)⁻¹ * (-((cs p : ℝ) : ℂ) - ((sn p : ℝ) : ℂ) * Complex.I)) =
        ((r : ℂ) * (r : ℂ)⁻¹) * ((-((cs p : ℝ) : ℂ) + ((sn p : ℝ) : ℂ) * Complex.I) *
          (-((cs p : ℝ) : ℂ) - ((sn p : ℝ) : ℂ) * Complex.I)) by ring, mul_inv_cancel₀ hrC, one_mul]
    linear_combination htrigC - ((sn p : ℝ) : ℂ) ^ 2 * Complex.I_sq
  -- `z + λ/z = -(1+λ) + i sn v` and `z - λ/z = -cs v + i sn σ`
  have hk1 : z + (lam : ℂ) * z⁻¹ = -(1 + (lam : ℂ)) +
      Complex.I * (((sn p : ℝ) : ℂ) * ((vContact p lam : ℝ) : ℂ)) := by
    rw [hzinv, hz']
    linear_combination ((cs p : ℝ) : ℂ) * hσC - hsigC - ((sn p : ℝ) : ℂ) * Complex.I * hvC
  have hk2 : z - (lam : ℂ) / z = -((cs p * vContact p lam : ℝ) : ℂ) +
      Complex.I * ((sn p * sigmaContact p lam : ℝ) : ℂ) := by
    rw [div_eq_mul_inv, hzinv, hz']
    push_cast
    linear_combination ((cs p : ℝ) : ℂ) * hvC - ((sn p : ℝ) : ℂ) * Complex.I * hσC
  have h1 : (z + (lam : ℂ)) * (z + 1) / z = Complex.I * ((sn p * vContact p lam : ℝ) : ℂ) := by
    rw [show (z + (lam : ℂ)) * (z + 1) / z = z + (lam : ℂ) * z⁻¹ + (1 + (lam : ℂ)) by field_simp; ring, hk1]
    push_cast
    ring
  have hvv0 : ((sn p * vContact p lam : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (mul_pos hsn hv0).ne'
  have hD : (z + (lam : ℂ)) * (z + 1) = Complex.I * ((sn p * vContact p lam : ℝ) : ℂ) * z := by
    rw [← h1]
    field_simp
  have hDne : (z + (lam : ℂ)) * (z + 1) ≠ 0 := by
    rw [hD]
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero hvv0) hz0
  refine ⟨h1, ?_, ?_, hk2⟩
  · have hval : (1 - (lam : ℂ)) * z / ((z + (lam : ℂ)) * (z + 1)) =
        (1 - (lam : ℂ)) / (Complex.I * ((sn p * vContact p lam : ℝ) : ℂ)) := by
      rw [← h1, div_div_eq_mul_div]
    rw [hval, Complex.ofReal_div, div_eq_iff (mul_ne_zero Complex.I_ne_zero hvv0)]
    rw [show -Complex.I * (((1 - lam : ℝ) : ℂ) / ((sn p * vContact p lam : ℝ) : ℂ)) *
        (Complex.I * ((sn p * vContact p lam : ℝ) : ℂ)) =
        -(Complex.I * Complex.I) * ((((1 - lam : ℝ) : ℂ) / ((sn p * vContact p lam : ℝ) : ℂ)) *
          ((sn p * vContact p lam : ℝ) : ℂ)) by ring, div_mul_cancel₀ _ hvv0, Complex.I_mul_I]
    push_cast
    ring
  · have hexpuu : Complex.exp ((yContact p lam : ℂ) + Complex.I * (theta p : ℂ)) = z := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, yContact, Real.exp_log (by rw [← hr]; linarith), hz]
    have hnum := (Complex.hasDerivAt_exp ((yContact p lam : ℂ) + Complex.I * (theta p : ℂ))).const_mul
      (1 - (lam : ℂ))
    have hden := ((Complex.hasDerivAt_exp ((yContact p lam : ℂ) + Complex.I * (theta p : ℂ))).add_const
      (lam : ℂ)).mul ((Complex.hasDerivAt_exp ((yContact p lam : ℂ) + Complex.I * (theta p : ℂ))).add_const 1)
    have hf := hnum.div hden (by simp only [Pi.mul_apply]; rw [hexpuu]; exact hDne)
    have hD2 : ((z + (lam : ℂ)) * (z + 1)) ^ 2 = -(((sn p * vContact p lam : ℝ) : ℂ) ^ 2 * z ^ 2) := by
      rw [hD]
      linear_combination (((sn p * vContact p lam : ℝ) : ℂ) ^ 2 * z ^ 2) * Complex.I_sq
    have hfd : deriv (fun u : ℂ => (1 - (lam : ℂ)) * Complex.exp u /
        ((Complex.exp u + (lam : ℂ)) * (Complex.exp u + 1)))
        ((yContact p lam : ℂ) + Complex.I * (theta p : ℂ)) = _ := hf.deriv
    rw [hfd]
    simp only [Pi.mul_apply]
    rw [hexpuu, hD2]
    field_simp
    ring

end GKSharp

