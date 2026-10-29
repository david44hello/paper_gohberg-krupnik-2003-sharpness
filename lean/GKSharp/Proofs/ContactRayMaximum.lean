/- GKSharp/Proofs/ContactRayMaximum.lean — the actual Möbius ray maximum.
Frozen source: short_v0.40/sec4b_failure.tex:28–32.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactRay

namespace GKSharp
open Threshold Set

private theorem ray_shift_norm_sq (xx tt aa : ℝ) :
    ‖(xx : ℂ) * Complex.exp (Complex.I * (tt : ℂ)) + (aa : ℂ)‖ ^ 2 =
      xx ^ 2 + 2 * xx * aa * Real.cos tt + aa ^ 2 := by
  have hre : (Complex.exp (Complex.I * (tt : ℂ))).re = Real.cos tt := by
    simpa [mul_comm] using Complex.exp_ofReal_mul_I_re tt
  have him : (Complex.exp (Complex.I * (tt : ℂ))).im = Real.sin tt := by
    simpa [mul_comm] using Complex.exp_ofReal_mul_I_im tt
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    hre, him, zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  linear_combination xx ^ 2 * Real.sin_sq_add_cos_sq tt

/-- B:28–32. The actual matrix GK is the maximum of the Möbius modulus
on the contact ray, and the actual chosen radius is its unique maximizer. -/
theorem contact_ray_max_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    (∀ (r : ℝ), 0 < r →
      ‖mobContact lam ((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)))‖ ≤ gk p lam) ∧
    (∀ (r : ℝ), 0 < r →
      (‖mobContact lam ((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)))‖ = gk p lam ↔
        r = rContact p lam)) := by
  have hp0 : 0 < p := by linarith
  have hs : 0 < sn p := by
    apply Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hp0)
    rw [div_lt_iff₀ hp0]
    nlinarith [Real.pi_pos]
  have htrig : sn p ^ 2 + cs p ^ 2 = 1 := by simp [sn, cs]
  have hC1 : 1 < gk p lam := by
    exact lt_of_le_of_lt (le_max_left _ _)
      (gk_gt_max hp (ne_of_lt hp2) (ρ := (lam : ℂ)) (by
        intro hh
        have hh' : lam = 1 := by exact_mod_cast hh
        linarith [hlam.2]))
  have hC0 : 0 ≤ gk p lam := by linarith
  have hCden : 0 < gk p lam ^ 2 - 1 := by nlinarith only [hC1, sq_nonneg (gk p lam - 1)]
  have hpoint (xx : ℝ) :
      ‖mobContact lam ((xx : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)))‖ ≤ gk p lam ∧
      (‖mobContact lam ((xx : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)))‖ = gk p lam ↔
        xx = rContact p lam) := by
    let zz : ℂ := (xx : ℂ) * Complex.exp (Complex.I * (theta p : ℂ))
    have hnum : ‖zz + (lam : ℂ)‖ ^ 2 = xx ^ 2 - 2 * lam * cs p * xx + lam ^ 2 := by
      change ‖(xx : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)) + (lam : ℂ)‖ ^ 2 = _
      rw [ray_shift_norm_sq]
      unfold cs theta
      ring
    have hden : ‖zz + 1‖ ^ 2 = xx ^ 2 - 2 * cs p * xx + 1 := by
      have hh := ray_shift_norm_sq xx (theta p) 1
      norm_num at hh
      change ‖(xx : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)) + 1‖ ^ 2 = _
      rw [hh]
      unfold cs theta
      ring
    have hD : 0 < ‖zz + 1‖ ^ 2 := by
      rw [hden]
      nlinarith only [sq_nonneg (xx - cs p), sq_pos_of_pos hs, htrig]
    have hb : 0 < ‖zz + 1‖ := by
      nlinarith only [hD, norm_nonneg (zz + 1)]
    have hg := contact_ray_squared_gap p lam xx hp hp2 hlam
    rw [← hden, ← hnum] at hg
    have hsq : ‖zz + (lam : ℂ)‖ ^ 2 ≤ (gk p lam * ‖zz + 1‖) ^ 2 := by
      nlinarith only [hg, mul_nonneg hCden.le (sq_nonneg (xx - rContact p lam))]
    have hle : ‖zz + (lam : ℂ)‖ ≤ gk p lam * ‖zz + 1‖ :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC0 hb.le)).mp hsq
    change ‖mobContact lam zz‖ ≤ gk p lam ∧ (_ ↔ _)
    refine ⟨?_, ?_⟩
    · simp only [mobContact, norm_div]
      exact (div_le_iff₀ hb).mpr hle
    · constructor
      · intro hh
        have hh' : ‖zz + (lam : ℂ)‖ / ‖zz + 1‖ = gk p lam := by
          simpa only [mobContact, norm_div] using hh
        have hnorm : ‖zz + (lam : ℂ)‖ = gk p lam * ‖zz + 1‖ :=
          (div_eq_iff hb.ne').mp hh'
        have hzero : (gk p lam ^ 2 - 1) * (xx - rContact p lam) ^ 2 = 0 := by
          nlinarith only [hg, congrArg (fun x : ℝ => x ^ 2) hnorm]
        have hh0 : (xx - rContact p lam) ^ 2 = 0 :=
          (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hCden)
        exact sub_eq_zero.mp (sq_eq_zero_iff.mp hh0)
      · intro hh
        have hzero : (xx - rContact p lam) ^ 2 = 0 := by rw [hh]; ring
        rw [hzero, mul_zero] at hg
        have heq : ‖zz + (lam : ℂ)‖ ^ 2 = (gk p lam * ‖zz + 1‖) ^ 2 := by
          nlinarith only [hg]
        have hnorm : ‖zz + (lam : ℂ)‖ = gk p lam * ‖zz + 1‖ :=
          (pow_left_inj₀ (norm_nonneg _) (mul_nonneg hC0 hb.le) two_ne_zero).mp heq
        simp only [mobContact, norm_div]
        exact (div_eq_iff hb.ne').mpr hnorm
  exact ⟨fun xx _ => (hpoint xx).1, fun xx _ => (hpoint xx).2⟩

end GKSharp

#print axioms GKSharp.contact_ray_max_proved
