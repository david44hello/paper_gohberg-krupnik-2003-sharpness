/- GKSharp/Proofs/Sec4aArch.lean - slice (b): obstacle contact value and the arch sinusoid (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v1.30, each as `<row>_proved` with the row's exact type.
- arch_sinusoid (A:26-27). (i) Contact: at `r = rContact > 1`, `e^y = r`, `cos t = cos(π/p) = -cs` the two bases of `Γ` are
  `r + 1/r - 2cs` and `r + λ²/r - 2λ cs`; the contact square gap (shared lemma contact_ray_squared_gap at `x = r`)
  gives `C² · base₁ = base₂`, so `Γ(log r, t) = (C² base₁)^q - base₂^q = 0` and the obstacle (an infimum; `0` if
  unbounded below) is `≤ 0` at `t = ±θ`. At the endpoint `λ = -1` the contact is `y = 0`: with `a = π/(2p)`,
  `C = GK_p(-1) = tan a` (shared row gk_minus_one) and `cos t = cos 2a`, `base₁ = 2 + 2cos 2a = 4cos²a`,
  `base₂ = 2 - 2cos 2a = 4sin²a = C² base₁`, so `Γ(0, t) = 0`. (ii) HKV Prop. 3.4 on the arch, elementary: with `F = f(·/q)` (trig convex),
  the 3-point inequalities at `(-π/2, 0, π/4)` and `(0, π/4, π/2)` add up to `0 ≤ (F(-π/2) + F(π/2)) sin(π/4)`, and
  `F(±π/2) = f(±θ) ≤ 0`, so both vanish. Then on `(0, π/2)`, `(0, x, π/2)` gives `F x ≤ F 0 cos x` and `(-π/2, 0, x)`
  gives `F 0 cos x ≤ F x`; symmetrically on `(-π/2, 0)`. So `f t = F(qt) = f(0) cos(qt)` on `[-θ, θ]`.
-/
import GKSharp.Proofs.ContactRay
import GKSharp.Proofs.GKMinusOne

namespace GKSharp

open Set GKSharp.Threshold

/-- The cleared 3-point inequality of trigonometric convexity. -/
lemma sec4a_trig_three {F : ℝ → ℝ} (hF : TrigConvexOn F univ) {x t y : ℝ} (hxt : x < t) (hty : t < y)
    (hyx : y - x < Real.pi) : F t * Real.sin (y - x) ≤ F x * Real.sin (y - t) + F y * Real.sin (t - x) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < y - x) hyx
  have := hF x (mem_univ _) y (mem_univ _) t (mem_univ _) hxt hty hyx
  rwa [le_div_iff₀ hs] at this

/-- HKV Prop. 3.4 on an arch of length `π`: if `F(±π/2) ≤ 0`, both vanish and `F = F(0) cos` on `[-π/2, π/2]`. -/
lemma sec4a_trig_arch {F : ℝ → ℝ} (hF : TrigConvexOn F univ) (hl : F (-(Real.pi / 2)) ≤ 0)
    (hr : F (Real.pi / 2) ≤ 0) :
    F (-(Real.pi / 2)) = 0 ∧ F (Real.pi / 2) = 0 ∧
      ∀ x ∈ Icc (-(Real.pi / 2)) (Real.pi / 2), F x = F 0 * Real.cos x := by
  have hpi := Real.pi_pos
  have ha := sec4a_trig_three hF (x := -(Real.pi / 2)) (t := 0) (y := Real.pi / 4)
    (by linarith) (by linarith) (by linarith)
  have hb := sec4a_trig_three hF (x := 0) (t := Real.pi / 4) (y := Real.pi / 2)
    (by linarith) (by linarith) (by linarith)
  simp only [sub_zero, sub_neg_eq_add, zero_add, Real.sin_add_pi_div_two, Real.sin_pi_div_two, mul_one] at ha
  simp only [sub_zero, Real.sin_pi_div_two_sub, Real.sin_pi_div_two, mul_one] at hb
  have hs4 : 0 < Real.sin (Real.pi / 4) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsum : 0 ≤ (F (-(Real.pi / 2)) + F (Real.pi / 2)) * Real.sin (Real.pi / 4) := by linarith
  have hpos : 0 ≤ F (-(Real.pi / 2)) + F (Real.pi / 2) := by nlinarith
  have hl0 : F (-(Real.pi / 2)) = 0 := by linarith
  have hr0 : F (Real.pi / 2) = 0 := by linarith
  refine ⟨hl0, hr0, fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  rcases lt_trichotomy x 0 with hneg | rfl | hpos'
  · rcases hx1.lt_or_eq with hx1 | rfl
    · have hu := sec4a_trig_three hF (x := -(Real.pi / 2)) (t := x) (y := 0) hx1 hneg (by linarith)
      have hd := sec4a_trig_three hF (x := x) (t := 0) (y := Real.pi / 2) hneg (by linarith) (by linarith)
      simp only [zero_sub, sub_neg_eq_add, zero_add, Real.sin_add_pi_div_two, Real.sin_pi_div_two, mul_one,
        hl0, zero_mul] at hu
      simp only [sub_zero, Real.sin_pi_div_two_sub, Real.sin_pi_div_two, mul_one, hr0, zero_mul,
        add_zero] at hd
      exact le_antisymm (by linarith) (by linarith)
    · rw [hl0, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  · rw [Real.cos_zero, mul_one]
  · rcases hx2.lt_or_eq with hx2 | rfl
    · have hu := sec4a_trig_three hF (x := 0) (t := x) (y := Real.pi / 2) hpos' hx2 (by linarith)
      have hd := sec4a_trig_three hF (x := -(Real.pi / 2)) (t := 0) (y := x) (by linarith) hpos' (by linarith)
      simp only [sub_zero, Real.sin_pi_div_two_sub, Real.sin_pi_div_two, mul_one, hr0, zero_mul,
        add_zero] at hu
      simp only [sub_zero, sub_neg_eq_add, zero_add, Real.sin_add_pi_div_two, Real.sin_pi_div_two, mul_one,
        hl0, zero_mul] at hd
      exact le_antisymm (by linarith) (by linarith)
    · rw [hr0, Real.cos_pi_div_two, mul_zero]

/-- At the contact radius the obstacle integrand vanishes: `Γ(log r, t) = 0` when `cos t = cos(π/p)`. -/
lemma sec4a_gamma_contact {p lam t : ℝ} (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ioo (-1 : ℝ) 1)
    (ht : Real.cos t = Real.cos (Real.pi / p)) :
    GKSharp.gamma p (gk p lam) (lam : ℂ) (Real.log (rContact p lam)) t = 0 := by
  obtain ⟨hr1, -, -, -⟩ := contact_root_properties hp hp2 hlam
  have hgap := contact_ray_squared_gap p lam (rContact p lam) hp hp2 hlam
  have hC1 : 1 < gk p lam := lt_of_le_of_lt (le_max_left _ _)
    (gk_gt_max hp (ne_of_lt hp2) (ρ := (lam : ℂ)) (by
      intro hh
      have hh' : lam = 1 := by exact_mod_cast hh
      linarith [hlam.2]))
  have hn : ‖(lam : ℂ)‖ ^ 2 = lam ^ 2 := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hre : (star (lam : ℂ) * unitPoint t).re = lam * Real.cos t := by
    rw [Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul, unitPoint, Complex.exp_ofReal_mul_I_re]
  have hcs : Real.cos t = -cs p := by rw [ht]; unfold cs; ring
  have hcs1 : cs p ≤ 1 := by unfold cs; linarith [Real.neg_one_le_cos (Real.pi / p)]
  unfold GKSharp.gamma
  rw [hn, hre, hcs]
  obtain ⟨C, hC⟩ : ∃ C, C = gk p lam := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = rContact p lam := ⟨_, rfl⟩
  rw [← hC, ← hr]
  rw [← hC, ← hr] at hgap
  rw [← hr] at hr1
  rw [← hC] at hC1
  have hr0 : 0 < r := by linarith
  have hC0 : 0 < C := by linarith
  have hinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
  rw [Real.exp_neg, Real.exp_log hr0, Real.cosh_eq, Real.exp_neg, Real.exp_log hr0]
  -- `C² base₁ = base₂` from the square gap at `x = r`
  have hkey : r + lam ^ 2 * r⁻¹ + 2 * (lam * -cs p) = C ^ 2 * (2 * ((r + r⁻¹) / 2) + 2 * -cs p) := by
    linear_combination (-r⁻¹) * hgap - (r - 2 * lam * cs p - C ^ 2 * r + 2 * C ^ 2 * cs p) * hinv
  have he : (r - 1) ^ 2 * r⁻¹ = r + r⁻¹ - 2 := by linear_combination (r - 2) * hinv
  have hsum2 : 2 ≤ r + r⁻¹ := by
    have := mul_nonneg (sq_nonneg (r - 1)) (inv_pos.2 hr0).le
    linarith
  have hb1 : 0 ≤ 2 * ((r + r⁻¹) / 2) + 2 * -cs p := by linarith
  rw [hkey, Real.mul_rpow (sq_nonneg C) hb1, ← Real.rpow_natCast C 2, ← Real.rpow_mul hC0.le,
    show ((2 : ℕ) : ℝ) * (p / 2) = p by push_cast; ring, sub_self]

/-- `obstacle p λ t ≤ 0` when `cos t = cos(π/p)`, in particular at `t = ±θ`. -/
lemma sec4a_obstacle_contact_nonpos {p lam t : ℝ} (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ioo (-1 : ℝ) 1)
    (ht : Real.cos t = Real.cos (Real.pi / p)) : Threshold.obstacle p lam t ≤ 0 := by
  show sInf (Set.range fun y : ℝ => GKSharp.gamma p (gk p lam) (lam : ℂ) y t) ≤ 0
  by_cases hb : BddBelow (Set.range fun y : ℝ => GKSharp.gamma p (gk p lam) (lam : ℂ) y t)
  · exact (csInf_le hb ⟨Real.log (rContact p lam), rfl⟩).trans (sec4a_gamma_contact hp hp2 hlam ht).le
  · exact (Real.sInf_of_not_bddBelow hb).le

/-- The endpoint `λ = -1`: the obstacle integrand vanishes at `y = 0` when `cos t = cos(π/p)`. -/
lemma sec4a_gamma_endpoint {p t : ℝ} (hp : 1 < p) (hp2 : p < 2) (ht : Real.cos t = Real.cos (Real.pi / p)) :
    GKSharp.gamma p (gk p ((-1 : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) 0 t = 0 := by
  have hp0 : 0 < p := by linarith
  have hpi := Real.pi_pos
  set a := Real.pi / (2 * p) with ha
  have ha0 : 0 < a := by positivity
  have ha2 : a < Real.pi / 2 := by
    rw [ha, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hcos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, ha2⟩
  have h2a : Real.pi / p = 2 * a := by rw [ha]; field_simp
  have hgk : gk p ((-1 : ℝ) : ℂ) = Real.tan a := by
    rw [Complex.ofReal_neg, Complex.ofReal_one]
    exact gk_minus_one hp hp2
  have hn : ‖((-1 : ℝ) : ℂ)‖ ^ 2 = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    norm_num
  have hre : (star ((-1 : ℝ) : ℂ) * unitPoint t).re = -Real.cos t := by
    rw [Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul, unitPoint, Complex.exp_ofReal_mul_I_re]
    ring
  have hcos2 : Real.cos t = 2 * Real.cos a ^ 2 - 1 := by rw [ht, h2a, Real.cos_two_mul]
  unfold GKSharp.gamma
  rw [hn, hre, hgk, Real.cosh_zero, neg_zero, Real.exp_zero]
  obtain ⟨C, hC⟩ : ∃ C, C = Real.tan a := ⟨_, rfl⟩
  rw [← hC]
  have hC0 : 0 ≤ C := hC ▸ (Real.tan_pos_of_pos_of_lt_pi_div_two ha0 ha2).le
  have hCsq : C ^ 2 * (2 * 1 + 2 * Real.cos t) = 4 * Real.sin a ^ 2 := by
    rw [hC, Real.tan_eq_sin_div_cos, hcos2, div_pow]
    field_simp
    ring
  -- `base₂ = C² · base₁`
  have hkey : 1 + 1 * 1 + 2 * -Real.cos t = C ^ 2 * (2 * 1 + 2 * Real.cos t) := by
    rw [hCsq, hcos2]
    linear_combination (-4 : ℝ) * Real.sin_sq_add_cos_sq a
  have hb1 : 0 ≤ 2 * 1 + 2 * Real.cos t := by linarith [Real.neg_one_le_cos t]
  rw [hkey, Real.mul_rpow (sq_nonneg C) hb1, ← Real.rpow_natCast C 2, ← Real.rpow_mul hC0,
    show ((2 : ℕ) : ℝ) * (p / 2) = p by push_cast; ring, sub_self]

/-- `obstacle p λ t ≤ 0` for `λ ∈ [-1, 1)` when `cos t = cos(π/p)`. -/
lemma sec4a_obstacle_contact_nonpos_Ico {p lam t : ℝ} (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ico (-1 : ℝ) 1)
    (ht : Real.cos t = Real.cos (Real.pi / p)) : Threshold.obstacle p lam t ≤ 0 := by
  rcases eq_or_lt_of_le hlam.1 with h | h
  · subst h
    show sInf (Set.range fun y : ℝ => GKSharp.gamma p (gk p ((-1 : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) y t) ≤ 0
    by_cases hb : BddBelow (Set.range fun y : ℝ => GKSharp.gamma p (gk p ((-1 : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) y t)
    · exact (csInf_le hb ⟨0, rfl⟩).trans (sec4a_gamma_endpoint hp hp2 ht).le
    · exact (Real.sInf_of_not_bddBelow hb).le
  · exact sec4a_obstacle_contact_nonpos hp hp2 ⟨h, hlam.2⟩ ht

/-- A:26-27, row `arch_sinusoid`. -/
theorem arch_sinusoid_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) (f : ℝ → ℝ)
    (_hf : Continuous f) (hq : QTrigConvex (q p) f)
    (hminor : ∀ t : ℝ, f t ≤ Threshold.obstacle p lam t) :
    f (-theta p) = 0 ∧ f (theta p) = 0 ∧
    ∃ aa : ℝ, ∀ t ∈ Icc (-theta p) (theta p), f t = aa * Real.cos (q p * t) := by
  have hp0 : p ≠ 0 := (show (0 : ℝ) < p by linarith).ne'
  have hq0 : 0 < q p := by unfold q; linarith
  have hθ : Real.pi / 2 / q p = theta p := by unfold q theta; field_simp
  have hnθ : -(Real.pi / 2) / q p = -theta p := by rw [neg_div, hθ]
  have hl : f (-theta p) ≤ 0 :=
    (hminor _).trans (sec4a_obstacle_contact_nonpos_Ico hp hp2 hlam (by rw [Real.cos_neg]; rfl))
  have hr : f (theta p) ≤ 0 := (hminor _).trans (sec4a_obstacle_contact_nonpos_Ico hp hp2 hlam rfl)
  obtain ⟨h1, h2, h3⟩ := sec4a_trig_arch (F := fun x => f (x / q p)) hq
    (by show f (-(Real.pi / 2) / q p) ≤ 0; rw [hnθ]; exact hl)
    (by show f (Real.pi / 2 / q p) ≤ 0; rw [hθ]; exact hr)
  have e1 : f (-theta p) = 0 := by rw [← hnθ]; exact h1
  have e2 : f (theta p) = 0 := by rw [← hθ]; exact h2
  refine ⟨e1, e2, f 0, fun t ht => ?_⟩
  have hqθ : q p * theta p = Real.pi / 2 := by unfold q theta; field_simp
  have hx : q p * t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    obtain ⟨ht1, ht2⟩ := ht
    have h1' := mul_le_mul_of_nonneg_left ht1 hq0.le
    have h2' := mul_le_mul_of_nonneg_left ht2 hq0.le
    constructor <;> linarith
  have := h3 (q p * t) hx
  simp only [mul_div_cancel_left₀ t hq0.ne', zero_div] at this
  exact this

end GKSharp
