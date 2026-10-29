/- GKSharp/Proofs/ContactDtGamma.lean - the angular derivative of Γ at the contact equals -qK (short v0.70 sec4).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Γ(y, t) = C^p B₁(t)^q - B₂(t)^q, `B₁ = 2cosh y + 2cos t`, `B₂ = e^y + λ²e^{-y} + 2λ cos t`, `q = p/2`, so
`∂ₜΓ = -p sin t (C^p B₁^{q-1} - λ B₂^{q-1})`. At the contact (`t = θ = π/p`, `sin θ = s`, `cos θ = -c`) `B₂ = C² B₁`,
so `C^p B₁^{q-1} = C² B₂^{q-1}` and `∂ₜΓ = -p s (C² - λ) B₂^{q-1} = -p (1 - λ) C B₂^{q-1}` (eq:GKreal
`s(C² - λ) = (1 - λ)C`, shared row quadratic_identities). And `K = 2(1 - λ)C s^{p-2} c^{1-q} (C² + λ)^{q-1}
= 2(1 - λ) C (s² c⁻¹ (C² + λ))^{q-1}` with `s² c⁻¹ (C² + λ) = B₂`. So `∂ₜΓ = -qK`.
- λ ∈ (-1, 1): `y = log r`, `r = rContact`; `B₁ = r + 1/r - 2c`, `B₂ = r + λ²/r - 2λc`; `B₂ = C²B₁` by the contact
  square gap; `s² c⁻¹ (C² + λ) = B₂` from `c = (1+λ)r/(r²+λ)`, `s² = (r²-1)(r²-λ²)/(r²+λ)²`, `C² = (r²-λ²)/(r²-1)`.
- λ = -1: `y = 0`, `a = π/(2p)`, `C = tan a` (shared gk_minus_one): `B₁ = 4cos²a`, `B₂ = 4sin²a = C²B₁`,
  `C² - 1 = c/cos²a`, so `s² c⁻¹ (C² - 1) = s²/cos²a = 4sin²a`.
-/
import GKSharp.Proofs.ContactRay
import GKSharp.Proofs.GKMinusOne
import GKSharp.Proofs.Sec4aBasic

namespace GKSharp

open Set GKSharp.Threshold

lemma sec4t_gamma_real (p C lam y x : ℝ) :
    GKSharp.gamma p C (lam : ℂ) y x =
      C ^ p * (2 * Real.cosh y + 2 * Real.cos x) ^ (p / 2) -
        (Real.exp y + lam ^ 2 * Real.exp (-y) + 2 * (lam * Real.cos x)) ^ (p / 2) := by
  have hn : ‖(lam : ℂ)‖ ^ 2 = lam ^ 2 := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hre : (star (lam : ℂ) * unitPoint x).re = lam * Real.cos x := by
    rw [Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul, unitPoint, Complex.exp_ofReal_mul_I_re]
  unfold GKSharp.gamma
  rw [hn, hre]

/-- The common computation: `∂ₜΓ(y, θ) = -q · 2(1 - λ)C s^{p-2} c^{1-q} (C² + λ)^{q-1}` from the contact relations. -/
lemma sec4t_dt_core {p C lam y b1 b2 : ℝ} (hp : 1 < p) (hC : 0 < C) (hCl : 0 < C ^ 2 + lam) (hc : 0 < cs p)
    (hs : 0 < sn p) (hB1 : 2 * Real.cosh y + 2 * Real.cos (theta p) = b1)
    (hB2 : Real.exp y + lam ^ 2 * Real.exp (-y) + 2 * (lam * Real.cos (theta p)) = b2)
    (hb1 : 0 < b1) (hb2 : b2 = C ^ 2 * b1) (hbase : sn p ^ 2 * (cs p)⁻¹ * (C ^ 2 + lam) = b2)
    (hgk : sn p * (C ^ 2 - lam) = (1 - lam) * C) :
    deriv (fun x => GKSharp.gamma p C (lam : ℂ) y x) (theta p) =
      -(p / 2) * (2 * (1 - lam) * C * Real.sin (Real.pi / p) ^ (p - 2) * (-Real.cos (Real.pi / p)) ^ (1 - p / 2) *
        (C ^ 2 + lam) ^ (p / 2 - 1)) := by
  have hb2pos : 0 < b2 := by rw [hb2]; exact mul_pos (pow_pos hC 2) hb1
  have hfun : (fun x => GKSharp.gamma p C (lam : ℂ) y x) = fun x =>
      C ^ p * (2 * Real.cosh y + 2 * Real.cos x) ^ (p / 2) -
        (Real.exp y + lam ^ 2 * Real.exp (-y) + 2 * (lam * Real.cos x)) ^ (p / 2) :=
    funext (sec4t_gamma_real p C lam y)
  have hg1 : HasDerivAt (fun x => 2 * Real.cosh y + 2 * Real.cos x) (2 * -Real.sin (theta p)) (theta p) :=
    ((Real.hasDerivAt_cos _).const_mul 2).const_add _
  have hg2 : HasDerivAt (fun x => Real.exp y + lam ^ 2 * Real.exp (-y) + 2 * (lam * Real.cos x))
      (2 * (lam * -Real.sin (theta p))) (theta p) :=
    (((Real.hasDerivAt_cos _).const_mul lam).const_mul 2).const_add _
  have hd : HasDerivAt (fun x => C ^ p * (2 * Real.cosh y + 2 * Real.cos x) ^ (p / 2) -
      (Real.exp y + lam ^ 2 * Real.exp (-y) + 2 * (lam * Real.cos x)) ^ (p / 2)) _ (theta p) :=
    ((hg1.rpow_const (p := p / 2) (Or.inl (by rw [hB1]; exact hb1.ne'))).const_mul (C ^ p)).sub
      (hg2.rpow_const (p := p / 2) (Or.inl (by rw [hB2]; exact hb2pos.ne')))
  rw [hfun, hd.deriv, hB1, hB2]
  have hsθ : Real.sin (theta p) = sn p := rfl
  rw [hsθ]
  show _ = -(p / 2) * (2 * (1 - lam) * C * sn p ^ (p - 2) * cs p ^ (1 - p / 2) * (C ^ 2 + lam) ^ (p / 2 - 1))
  have hs2 : sn p ^ (p - 2) = (sn p ^ 2) ^ (p / 2 - 1) := by
    rw [← Real.rpow_natCast (sn p) 2, ← Real.rpow_mul hs.le]
    congr 1
    push_cast
    ring
  have hc1 : cs p ^ (1 - p / 2) = ((cs p)⁻¹) ^ (p / 2 - 1) := by
    rw [Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
    congr 1
    ring
  have hK : sn p ^ (p - 2) * cs p ^ (1 - p / 2) * (C ^ 2 + lam) ^ (p / 2 - 1) = b2 ^ (p / 2 - 1) := by
    rw [hs2, hc1, ← Real.mul_rpow (sq_nonneg _) (inv_nonneg.2 hc.le),
      ← Real.mul_rpow (mul_nonneg (sq_nonneg _) (inv_nonneg.2 hc.le)) hCl.le, hbase]
  have hCp : C ^ p = (C ^ 2) ^ (p / 2 - 1) * C ^ 2 := by
    rw [← Real.rpow_natCast C 2, ← Real.rpow_mul hC.le, ← Real.rpow_add hC]
    congr 1
    push_cast
    ring
  have hi : C ^ p * b1 ^ (p / 2 - 1) = C ^ 2 * b2 ^ (p / 2 - 1) := by
    rw [hCp, hb2, Real.mul_rpow (sq_nonneg C) hb1.le]
    ring
  linear_combination (-p * sn p) * hi + (-p * b2 ^ (p / 2 - 1)) * hgk + (p * (1 - lam) * C) * hK

lemma sec4t_cs_pos {p : ℝ} (hp : 1 < p) (hp2 : p < 2) : 0 < cs p := by
  have hpi := Real.pi_pos
  have h1 : Real.pi / 2 < Real.pi / p := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have h2 : Real.pi / p < Real.pi + Real.pi / 2 := by
    have := div_le_self hpi.le (show (1 : ℝ) ≤ p by linarith)
    linarith
  unfold cs
  linarith [Real.cos_neg_of_pi_div_two_lt_of_lt h1 h2]

/-- Row `contact_dt_gamma` (λ ∈ (-1, 1)). -/
theorem contact_dt_gamma (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1) :
    GKSharp.Threshold.dt (GKSharp.Threshold.gammaGK p lam)
      (GKSharp.Threshold.yContact p lam) (GKSharp.Threshold.theta p) =
      -GKSharp.Threshold.q p * GKSharp.kConst p lam := by
  obtain ⟨hr1, -, -, -⟩ := contact_root_properties hp hp2 hlam
  obtain ⟨-, hC2⟩ := contact_gk_radius p lam hp hp2 hlam
  obtain ⟨hcsr, hsn2, -⟩ := contact_rational_identities_proved p lam hp hp2 hlam
  have hgap := contact_ray_squared_gap p lam (rContact p lam) hp hp2 hlam
  have hq2 := (quadratic_identities_proved p lam hp hp2 ⟨hlam.1.le, hlam.2⟩).2
  obtain ⟨r, hr⟩ : ∃ r, r = rContact p lam := ⟨_, rfl⟩
  rw [← hr] at hr1 hC2 hcsr hsn2 hgap
  have hs := sec4a_sn_pos hp
  have hc := sec4t_cs_pos hp hp2
  have hc1 : cs p ≤ 1 := by unfold cs; linarith [Real.neg_one_le_cos (Real.pi / p)]
  have hC1 : 1 < gk p lam := lt_of_le_of_lt (le_max_left _ _)
    (gk_gt_max hp (ne_of_lt hp2) (ρ := (lam : ℂ)) (by
      intro hh
      have hh' : lam = 1 := by exact_mod_cast hh
      linarith [hlam.2]))
  have hr0 : 0 < r := by linarith
  have hinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
  have hcosθ : Real.cos (theta p) = -cs p := by unfold cs theta; ring
  have hB1 : 2 * Real.cosh (yContact p lam) + 2 * Real.cos (theta p) = r + r⁻¹ - 2 * cs p := by
    unfold yContact
    rw [← hr, Real.cosh_eq, Real.exp_neg, Real.exp_log hr0, hcosθ]
    ring
  have hB2 : Real.exp (yContact p lam) + lam ^ 2 * Real.exp (-yContact p lam) + 2 * (lam * Real.cos (theta p)) =
      r + lam ^ 2 * r⁻¹ - 2 * lam * cs p := by
    unfold yContact
    rw [← hr, Real.exp_neg, Real.exp_log hr0, hcosθ]
    ring
  have he : (r - 1) ^ 2 * r⁻¹ = r + r⁻¹ - 2 := by linear_combination (r - 2) * hinv
  have hb1 : 0 < r + r⁻¹ - 2 * cs p := by
    have := mul_pos (pow_pos (sub_pos.2 hr1) 2) (inv_pos.2 hr0)
    linarith
  have hb2 : r + lam ^ 2 * r⁻¹ - 2 * lam * cs p = gk p lam ^ 2 * (r + r⁻¹ - 2 * cs p) := by
    linear_combination (-r⁻¹) * hgap - (r - 2 * lam * cs p - gk p lam ^ 2 * r + 2 * gk p lam ^ 2 * cs p) * hinv
  have hrl : 0 < r ^ 2 + lam := by nlinarith [hlam.1]
  have hr21 : r ^ 2 - 1 ≠ 0 := by nlinarith
  have hl1 : 1 + lam ≠ 0 := by linarith [hlam.1]
  have hbase : sn p ^ 2 * (cs p)⁻¹ * (gk p lam ^ 2 + lam) = r + lam ^ 2 * r⁻¹ - 2 * lam * cs p := by
    rw [hsn2, hC2, hcsr]
    field_simp
    ring
  have hgk : sn p * (gk p lam ^ 2 - lam) = (1 - lam) * gk p lam := by
    rw [hq2]
    field_simp
  have hCl : 0 < gk p lam ^ 2 + lam := by nlinarith [hlam.1]
  show deriv (fun x => GKSharp.gamma p (gk p lam) (lam : ℂ) (yContact p lam) x) (theta p) = _
  rw [sec4t_dt_core hp (by linarith) hCl hc hs hB1 hB2 hb1 hb2 hbase hgk]
  unfold q kConst
  ring

/-- Row `endpoint_dt_gamma` (λ = -1, contact at `y = 0`). -/
theorem endpoint_dt_gamma (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    GKSharp.Threshold.dt (GKSharp.Threshold.gammaGK p (-1))
      0 (GKSharp.Threshold.theta p) =
      -GKSharp.Threshold.q p * GKSharp.kConst p (-1) := by
  have hp0 : 0 < p := by linarith
  have hpi := Real.pi_pos
  set a := Real.pi / (2 * p) with ha
  have ha0 : 0 < a := by positivity
  have ha2 : a < Real.pi / 2 := by
    rw [ha, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hcosa : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, ha2⟩
  have hca0 : Real.cos a ≠ 0 := hcosa.ne'
  have h2a : Real.pi / p = 2 * a := by rw [ha]; field_simp
  have hCt : gk p ((-1 : ℝ) : ℂ) = Real.tan a := by
    rw [Complex.ofReal_neg, Complex.ofReal_one]
    exact gk_minus_one hp hp2
  have hC1 : 1 < gk p ((-1 : ℝ) : ℂ) := lt_of_le_of_lt (le_max_left _ _)
    (gk_gt_max hp (ne_of_lt hp2) (ρ := ((-1 : ℝ) : ℂ)) (by
      intro hh
      have hh' : (-1 : ℝ) = 1 := by exact_mod_cast hh
      norm_num at hh'))
  have hs := sec4a_sn_pos hp
  have hc := sec4t_cs_pos hp hp2
  have hcs0 : cs p ≠ 0 := hc.ne'
  have hcos2 : Real.cos (theta p) = 2 * Real.cos a ^ 2 - 1 := by
    show Real.cos (Real.pi / p) = _
    rw [h2a, Real.cos_two_mul]
  have hsn : sn p = 2 * Real.sin a * Real.cos a := by unfold sn; rw [h2a, Real.sin_two_mul]
  have hcs : cs p = 1 - 2 * Real.cos a ^ 2 := by unfold cs; rw [h2a, Real.cos_two_mul]; ring
  have hB1 : 2 * Real.cosh 0 + 2 * Real.cos (theta p) = 4 * Real.cos a ^ 2 := by
    rw [Real.cosh_zero, hcos2]
    ring
  have hB2 : Real.exp 0 + (-1 : ℝ) ^ 2 * Real.exp (-0) + 2 * (-1 * Real.cos (theta p)) = 4 * Real.sin a ^ 2 := by
    rw [neg_zero, Real.exp_zero, hcos2]
    linear_combination (-4 : ℝ) * Real.sin_sq_add_cos_sq a
  have hb1 : 0 < 4 * Real.cos a ^ 2 := by positivity
  have hb2 : 4 * Real.sin a ^ 2 = gk p ((-1 : ℝ) : ℂ) ^ 2 * (4 * Real.cos a ^ 2) := by
    rw [hCt, Real.tan_eq_sin_div_cos, div_pow]
    field_simp
  have hC21 : gk p ((-1 : ℝ) : ℂ) ^ 2 + -1 = cs p / Real.cos a ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hca0), hCt, Real.tan_eq_sin_div_cos, div_pow, add_mul,
      div_mul_cancel₀ _ (pow_ne_zero 2 hca0), hcs]
    linear_combination Real.sin_sq_add_cos_sq a
  have hbase : sn p ^ 2 * (cs p)⁻¹ * (gk p ((-1 : ℝ) : ℂ) ^ 2 + -1) = 4 * Real.sin a ^ 2 := by
    rw [hC21, hsn]
    field_simp
    ring
  have hq2 := (quadratic_identities_proved p (-1) hp hp2 ⟨le_rfl, by norm_num⟩).2
  have hgk : sn p * (gk p ((-1 : ℝ) : ℂ) ^ 2 - -1) = (1 - -1) * gk p ((-1 : ℝ) : ℂ) := by
    rw [hq2]
    field_simp
  have hCl : 0 < gk p ((-1 : ℝ) : ℂ) ^ 2 + -1 := by nlinarith
  show deriv (fun x => GKSharp.gamma p (gk p ((-1 : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) 0 x) (theta p) = _
  rw [sec4t_dt_core hp (by linarith) hCl hc hs hB1 hB2 hb1 hb2 hbase hgk]
  unfold q kConst
  ring

end GKSharp
