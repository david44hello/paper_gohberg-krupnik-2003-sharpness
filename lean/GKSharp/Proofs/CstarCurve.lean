/- Theorem C* (sec5e_cstar.tex l.17-20, short v0.70), the critical-curve half of "If": the positive-axis test
h ≥ 0 gives D_C ≥ 0 on the positive z-axis, hence Φ(ρ₀) ≥ 0 and Λ(0⁺) = Φ(ρ₀)/(1-λ)^p ≥ 0 (sec5e_Lambda_zero); with the
shape {K_f < K} = (0, θ_a) ∪ (θ₀, π), every value Φ(w(θ)) is ≥ 0 (cstar_curve_nonneg). No cited input.
Copyright (C) Dave Goel 2026--now.

  (1) Positive axis (obstacleG_pos_axis, critD_pos_axis_nonneg): K ≤ m_C(0) = inf_y Γ_C(y, 0) and Γ_C(log s, 0) =
      s^{-q} G(s) (gamma_radial) give K s^q ≤ G(s) = C^p|1+s|^p - |λ+s|^p for s > 0; with s = 1/r,
      D_C(r) = r^p (G(1/r) - K r^{-q}) ≥ 0 for every r > 0.
  (2) ρ₀ = w(r₀) with r₀ = curveRoot > 0 real (the text: "ρ₀ real, i.e. a value of D_C/|1+z|^p on the positive axis"),
      and D_C(r₀) = |1+r₀|^p/(1-λ)^p Φ(w(r₀)) (critD_eq_mobPhi), so Φ(ρ₀) ≥ 0. Λ(θ) → Φ(ρ₀)/(1-λ)^p: Φ is continuous and
      w(θ) → ρ₀ (the curve_w_tendsto_rho0_proved).
  (3) f(θ) = Φ(w(θ)), f′ = F(K - K_f), F > 0 ((5.8) with (A2), the sec5_A2_proved), f(θ₀) = 0 (lemma_contact).
      θ ∈ (0, θ_a): f′ > 0 on (0, θ], so f(θ) ≥ lim_{0⁺} f = Φ(ρ₀) ≥ 0. θ ∈ [θ_a, θ₀]: K_f ≥ K on (θ, θ₀), f′ ≤ 0,
      f(θ) ≥ f(θ₀) = 0. θ ∈ (θ₀, π): f′ > 0 on (θ₀, θ), f(θ) > f(θ₀) = 0. -/
import GKSharp.Proofs.ReductionStep1
import GKSharp.Proofs.SharpA2
import GKSharp.Proofs.ObstacleMinimum
import GKSharp.Proofs.Gamma
import GKSharp.Proofs.GKRoot

open Filter Topology Set

namespace GKSharp

namespace CstarCurve

/-- (1) The positive-axis test: `K ≤ m_C(0)` gives `K s^q ≤ G(s)` for every real `s > 0`. -/
theorem obstacleG_pos_axis {p C KK lam : ℝ} (hp : 0 < p) (hC : max 1 ‖(lam : ℂ)‖ < C)
    (hh : KK ≤ obstacle p C (lam : ℂ) 0) {s : ℝ} (hs : 0 < s) :
    KK * s ^ (p / 2) ≤ obstacleG p C (lam : ℂ) (s : ℂ) := by
  have hle := hh.trans (csInf_le (obstacle_bddBelow hp (lam : ℂ) hC 0) (mem_range_self (Real.log s)))
  have hu : unitPoint 0 = 1 := by simp [unitPoint]
  rw [gamma_radial, Real.exp_log hs, hu, mul_one] at hle
  have hcancel : s ^ (p / 2) * s ^ (-(p / 2)) = 1 := by
    rw [← Real.rpow_add hs, add_neg_cancel, Real.rpow_zero]
  have hmul := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hs.le (p / 2))
  rw [← mul_assoc, hcancel, one_mul] at hmul
  linarith

/-- `D_C(r) = r^p (G(1/r) - K r^{-q})` for real `r > 0`. -/
theorem critD_pos_axis_eq {p C KK lam r : ℝ} (hr : 0 < r) :
    critD p C KK lam (r : ℂ) = r ^ p * (obstacleG p C (lam : ℂ) ((r⁻¹ : ℝ) : ℂ) - KK * r⁻¹ ^ (p / 2)) := by
  have hr' : 0 < r⁻¹ := inv_pos.mpr hr
  have e1 : ‖1 + (r : ℂ)‖ = 1 + r := by
    rw [show (1 : ℂ) + r = ((1 + r : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have e2 : ‖1 + (lam : ℂ) * r‖ = |1 + lam * r| := by
    rw [show (1 : ℂ) + lam * r = ((1 + lam * r : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  have e3 : ‖1 + ((r⁻¹ : ℝ) : ℂ)‖ = 1 + r⁻¹ := by
    rw [show (1 : ℂ) + ((r⁻¹ : ℝ) : ℂ) = ((1 + r⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have e4 : ‖(lam : ℂ) + ((r⁻¹ : ℝ) : ℂ)‖ = |lam + r⁻¹| := by
    rw [show (lam : ℂ) + ((r⁻¹ : ℝ) : ℂ) = ((lam + r⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
  have e5 : reQPow (r : ℂ) (p / 2) = r ^ (p / 2) := by
    rw [reQPow, Complex.norm_real, Real.norm_of_nonneg hr.le, Complex.arg_ofReal_of_nonneg hr.le, mul_zero,
      Real.cos_zero, mul_one]
  have f1 : r ^ p * (1 + r⁻¹) ^ p = (1 + r) ^ p := by
    rw [← Real.mul_rpow hr.le (by linarith), mul_add, mul_one, mul_inv_cancel₀ hr.ne', add_comm]
  have f2 : r ^ p * |lam + r⁻¹| ^ p = |1 + lam * r| ^ p := by
    rw [← Real.mul_rpow hr.le (abs_nonneg _), ← abs_of_pos hr, ← abs_mul, abs_of_pos hr, mul_add,
      mul_inv_cancel₀ hr.ne', mul_comm r lam, add_comm]
  have f3 : r ^ p * r⁻¹ ^ (p / 2) = r ^ (p / 2) := by
    rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, ← Real.rpow_add hr, show p + -(p / 2) = p / 2 by ring]
  unfold critD obstacleG
  rw [e1, e2, e3, e4, e5]
  linear_combination (C ^ p) * f1.symm - f2.symm - KK * f3.symm

/-- (1) `h ≥ 0` (`K ≤ m_C(0)`) gives `D_C ≥ 0` on the positive axis. -/
theorem critD_pos_axis_nonneg {p C KK lam : ℝ} (hp : 0 < p) (hC : max 1 ‖(lam : ℂ)‖ < C)
    (hh : KK ≤ obstacle p C (lam : ℂ) 0) {r : ℝ} (hr : 0 < r) : 0 ≤ critD p C KK lam (r : ℂ) := by
  rw [critD_pos_axis_eq hr]
  exact mul_nonneg (Real.rpow_nonneg hr.le p) (sub_nonneg.mpr (obstacleG_pos_axis hp hC hh (inv_pos.mpr hr)))

/-- `max 1 |λ| < GK_p(λ)` (`1 < p < 2`, `λ < 1`). -/
theorem gk_gt_max_real {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl1 : lam < 1) :
    max 1 ‖(lam : ℂ)‖ < gk p lam :=
  gk_gt_max hp1 (ne_of_lt hp2) (fun h => by
    have : lam = 1 := by exact_mod_cast h
    linarith)

/-- (2) `h ≥ 0` gives `Φ(ρ₀) ≥ 0`, `ρ₀ = w(r₀) = (1 + λr₀)/(1 + r₀)`. -/
theorem mobPhi_rho0_nonneg {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hh : kConst p lam ≤ obstacle p (gk p lam) (lam : ℂ) 0) :
    0 ≤ mobPhi p (gk p lam) (kConst p lam) lam
      ((((1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) : ℝ)) : ℂ) := by
  set r0 := curveRoot lam (1 - p / 2) (p / 2) with hr0def
  have hr0 : 0 < r0 := curveRoot_pos hl hl1 (by linarith) (by linarith)
  have hz : (r0 : ℂ) ≠ -1 := fun h => by
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.one_re] at this
    linarith
  have hw : mobW lam (r0 : ℂ) = (((1 + lam * r0) / (1 + r0) : ℝ) : ℂ) := by
    unfold mobW; push_cast; ring
  have hD := critD_pos_axis_nonneg (KK := kConst p lam) (by linarith) (gk_gt_max_real hp1 hp2 hl1) hh hr0
  rw [critD_eq_mobPhi p _ _ hl1 hz, hw] at hD
  have hpos : 0 < ‖1 + (r0 : ℂ)‖ ^ p / (1 - lam) ^ p :=
    div_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 (one_add_ne_zero hz)) p)
      (Real.rpow_pos_of_pos (by linarith) p)
  exact le_of_mul_le_mul_left (by rwa [mul_zero]) hpos

/-- **sec5e_cstar.tex l.19-20** (contract row sec5e_Lambda_zero): `Λ(0⁺) = Φ(ρ₀)/(1-λ)^p`, and `h ≥ 0` gives `Φ(ρ₀) ≥ 0`. -/
theorem sec5e_Lambda_zero_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1) :
    let r0 := curveRoot lam (1 - p / 2) (p / 2)
    let ρ0 := (1 + lam * r0) / (1 + r0)
    Tendsto (fun θ => mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam θ)) / (1 - lam) ^ p)
      (𝓝[>] 0) (𝓝 (mobPhi p (gk p lam) (kConst p lam) lam (ρ0 : ℂ) / (1 - lam) ^ p)) ∧
    (kConst p lam ≤ obstacle p (gk p lam) lam 0 → 0 ≤ mobPhi p (gk p lam) (kConst p lam) lam (ρ0 : ℂ)) := by
  intro r0 ρ0
  refine ⟨?_, mobPhi_rho0_nonneg hp1 hp2 (by linarith) hl1⟩
  exact ((((ReductionStep1.mobPhi_continuous (p := p) (by linarith) (gk p lam) (kConst p lam) lam).tendsto _).comp
    (curve_w_tendsto_rho0_proved hp1 hp2 (by linarith) hl1))).div_const _

/-- (3) Along the critical curve: `f′ = F (K - K_f)` with `F > 0` (by (5.8) and (A2)). -/
theorem curve_Phi_hasDerivAt {p lam θ : ℝ} (C K : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ : θ ∈ Ioo 0 Real.pi) :
    ∃ F : ℝ, 0 < F ∧ HasDerivAt (fun x => mobPhi p C K lam (mobW lam (curveZ p lam x))) (F * (K - curveKf p lam θ)) θ := by
  have hA2 := (sec5_A2_proved hp1 hp2 hl hl1).2.2.2.2.2.2.1 θ hθ
  obtain ⟨hd, hF, -, -⟩ := Sec5Eq58.eq_5_8_of_rho_deriv_pos (C := C) (K := K) hp1 hp2 hl hl1 hθ.1 hθ.2 hA2
  exact ⟨_, hF, hd⟩

/-- (3) `f(θ₀) = Φ(w(θ₀)) = 0` (lemma_contact + sec5_Lambda). -/
theorem curve_Phi_contact {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam (Real.pi / p))) = 0 := by
  obtain ⟨hθ0, hθπ, -, -⟩ := theta0_bounds hp1 hp2
  have h1 := (Proofs.Sec5Lambda.sec5_Lambda_proved (C := gk p lam) (K := kConst p lam) hp1 hp2 hl hl1 hθ0 hθπ).2
  rw [contact_Lambda hp1 hp2 hl hl1 (kConst p lam), zero_div] at h1
  exact (div_eq_zero_iff.mp h1).resolve_right (Real.rpow_pos_of_pos (by linarith) p).ne'

/-- **sec5e_cstar.tex l.17-19** (contract helper cstar_curve_nonneg): with `{K_f < K} = (0, θ_a) ∪ (θ₀, π)` and
`Φ(ρ₀) ≥ 0`, every critical-curve value `Φ(w(θ))` is `≥ 0`. -/
theorem cstar_curve_nonneg_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hset : ∃ θa ∈ Set.Ico 0 (Real.pi / p),
      {θ ∈ Set.Ioo 0 Real.pi | curveKf p lam θ < kConst p lam} = Set.Ioo 0 θa ∪ Set.Ioo (Real.pi / p) Real.pi)
    (h0 : 0 ≤ mobPhi p (gk p lam) (kConst p lam) lam
      ((((1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) : ℝ)) : ℂ)) :
    ∀ θ ∈ Set.Ioo 0 Real.pi, 0 ≤ mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam θ)) := by
  have hl : -1 ≤ lam := by linarith
  obtain ⟨θa, hθa, hS⟩ := hset
  set f : ℝ → ℝ := fun θ => mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam θ)) with hfdef
  obtain ⟨hθ0, hθπ, -, -⟩ := theta0_bounds hp1 hp2
  have hD : ∀ x ∈ Ioo 0 Real.pi, ∃ F : ℝ, 0 < F ∧ HasDerivAt f (F * (kConst p lam - curveKf p lam x)) x :=
    fun x hx => curve_Phi_hasDerivAt (gk p lam) (kConst p lam) hp1 hp2 hl hl1 hx
  have hcont : ∀ x ∈ Ioo 0 Real.pi, ContinuousAt f x := fun x hx => by
    obtain ⟨F, -, hd⟩ := hD x hx
    exact hd.continuousAt
  have hdiff : ∀ x ∈ Ioo 0 Real.pi, DifferentiableAt ℝ f x := fun x hx => by
    obtain ⟨F, -, hd⟩ := hD x hx
    exact hd.differentiableAt
  have hf0 : f (Real.pi / p) = 0 := curve_Phi_contact hp1 hp2 hl hl1
  -- membership in {K_f < K}
  have hmem : ∀ x ∈ Ioo 0 Real.pi, (curveKf p lam x < kConst p lam ↔ x ∈ Ioo 0 θa ∪ Ioo (Real.pi / p) Real.pi) :=
    fun x hx => by
      rw [← hS]
      exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  -- the sign of f′ from the sign of K - K_f
  have hsign_pos : ∀ x ∈ Ioo 0 Real.pi, curveKf p lam x < kConst p lam → 0 < deriv f x := fun x hx hlt => by
    obtain ⟨F, hF, hd⟩ := hD x hx
    rw [hd.deriv]
    exact mul_pos hF (by linarith)
  have hsign_nonpos : ∀ x ∈ Ioo 0 Real.pi, kConst p lam ≤ curveKf p lam x → deriv f x ≤ 0 := fun x hx hle => by
    obtain ⟨F, hF, hd⟩ := hD x hx
    rw [hd.deriv]
    exact mul_nonpos_of_nonneg_of_nonpos hF.le (by linarith)
  intro θ hθ
  show 0 ≤ f θ
  rcases lt_or_ge θ θa with hlt | hge
  · -- θ ∈ (0, θ_a): f increasing on (0, θ], f(θ) ≥ Φ(ρ₀) ≥ 0
    have hsub : Ioc 0 θ ⊆ Ioo 0 Real.pi := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    have hmono : MonotoneOn f (Ioc 0 θ) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 θ) (fun x hx => (hcont x (hsub hx)).continuousWithinAt)
        (fun x hx => ?_) (fun x hx => ?_)
      · rw [interior_Ioc] at hx
        exact (hdiff x (hsub (Ioo_subset_Ioc_self hx))).differentiableWithinAt
      · rw [interior_Ioc] at hx
        have hx' := hsub (Ioo_subset_Ioc_self hx)
        exact (hsign_pos x hx' ((hmem x hx').2 (Or.inl ⟨hx.1, hx.2.trans hlt⟩))).le
    have hlimf := ((ReductionStep1.mobPhi_continuous (p := p) (by linarith) (gk p lam) (kConst p lam) lam).tendsto
      _).comp (curve_w_tendsto_rho0_proved hp1 hp2 hl hl1)
    have hev : ∀ᶠ x in 𝓝[>] 0, f x ≤ f θ := by
      filter_upwards [Ioo_mem_nhdsGT hθ.1] with x hx
      exact hmono ⟨hx.1, hx.2.le⟩ ⟨hθ.1, le_rfl⟩ hx.2.le
    exact h0.trans (le_of_tendsto hlimf hev)
  · rcases le_or_gt θ (Real.pi / p) with hle | hgt
    · -- θ ∈ [θ_a, θ₀]: K_f ≥ K on (θ, θ₀), f decreasing on [θ, θ₀], f(θ) ≥ f(θ₀) = 0
      have hsub : Icc θ (Real.pi / p) ⊆ Ioo 0 Real.pi := fun x hx => ⟨hθ.1.trans_le hx.1, hx.2.trans_lt hθπ⟩
      have hanti : AntitoneOn f (Icc θ (Real.pi / p)) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) (fun x hx => (hcont x (hsub hx)).continuousWithinAt)
          (fun x hx => ?_) (fun x hx => ?_)
        · rw [interior_Icc] at hx
          exact (hdiff x (hsub (Ioo_subset_Icc_self hx))).differentiableWithinAt
        · rw [interior_Icc] at hx
          have hx' := hsub (Ioo_subset_Icc_self hx)
          refine hsign_nonpos x hx' (not_lt.mp fun hK => ?_)
          rcases (hmem x hx').1 hK with h1 | h1
          · exact absurd (hge.trans_lt hx.1) (not_lt.mpr h1.2.le)
          · exact absurd hx.2 (not_lt.mpr h1.1.le)
      have := hanti ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
      rw [hf0] at this
      exact this
    · -- θ ∈ (θ₀, π): f increasing on [θ₀, θ], f(θ) ≥ f(θ₀) = 0
      have hsub : Icc (Real.pi / p) θ ⊆ Ioo 0 Real.pi := fun x hx => ⟨hθ0.trans_le hx.1, hx.2.trans_lt hθ.2⟩
      have hmono : MonotoneOn f (Icc (Real.pi / p) θ) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (fun x hx => (hcont x (hsub hx)).continuousWithinAt)
          (fun x hx => ?_) (fun x hx => ?_)
        · rw [interior_Icc] at hx
          exact (hdiff x (hsub (Ioo_subset_Icc_self hx))).differentiableWithinAt
        · rw [interior_Icc] at hx
          have hx' := hsub (Ioo_subset_Icc_self hx)
          exact (hsign_pos x hx' ((hmem x hx').2 (Or.inr ⟨hx.1, hx'.2⟩))).le
      have := hmono ⟨le_rfl, hgt.le⟩ ⟨hgt.le, le_rfl⟩ hgt.le
      rw [hf0] at this
      exact this

end CstarCurve

end GKSharp
