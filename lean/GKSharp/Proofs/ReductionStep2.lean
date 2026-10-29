/- GKSharp/Proofs/ReductionStep2.lean - Reduction Step 2: Φ ≥ Φ(ρ₀) on the real segment I (short v0.70 sec5 l.147-155).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Notation: `q = p/2`, `C = GK_p(λ)`, `K = kConst`, `r₀ = R(0⁺)`, `ρ₀ = (1 + λr₀)/(1 + r₀)`, `ρ₁ = (1 + λ)/2`,
`Q(x) = (x - λ)(1 - x)`, `m(x) = (2x - 1 - λ) x^{1-p} Q(x)^{q-1}`.
- On `[ρ, ρ₀] ⊆ I`, `Φ(x) = (1 - λ)^p (C^p - x^p) - K Q(x)^q` (`Q ≥ 0`, so `Re Q^q = Q^q`), with
  `Φ'(x) = -(1 - λ)^p p x^{p-1} - K q Q^{q-1}(1 + λ - 2x)`. For `2x ≤ 1 + λ` both terms are `≤ 0`. For `2x > 1 + λ`,
  `Φ'(x) ≤ 0` iff `K m(x) ≤ 2(1 - λ)^p`; `m` increases on `(ρ₁, 1)` (`(2x - 1 - λ)x^{1-p} = 2x^{2-p} - (1 + λ)x^{1-p}`
  and `Q` decreases there), so it suffices that `K m(ρ₀) ≤ 2(1 - λ)^p`.
- ROUTE DIFFERENCE R9 (logged by the lead): `K m(ρ₀) ≤ 2(1 - λ)^p` from the curve, not from the gradient (5.8): as
  `θ → 0⁺`, `w(θ) → ρ₀` (premise `hw`), `|v| → 1 + λ`, `|Q(w)| → Q(ρ₀)`, `cos δ → 1`, so `K_f(θ) → L` with
  `L m(ρ₀) = 2(1 - λ)^p`; and `K_f(θ) > K_f(θ₀) = K` on `(0, θ₀)` (`hdec`, shared contact_Kf). So `K ≤ L`.
  (At `λ = -1`, `r₀ = 1`, `ρ₀ = 0 = ρ₁`, so the second case does not occur.)
-/
import GKSharp.Proofs.Contact

namespace GKSharp

open Set Filter
open scoped Topology

lemma sec5r_root_pos {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) :
    0 < curveRoot lam (1 - p / 2) (p / 2) := by
  unfold curveRoot
  apply div_pos (by linarith)
  have hs := Real.sqrt_nonneg ((1 + lam) ^ 2 * (p / 2) ^ 2 - 4 * lam * (1 - p / 2) ^ 2)
  rcases hl.lt_or_eq with hlt | heq
  · have : 0 < (1 + lam) * (p / 2) := mul_pos (by linarith) (by linarith)
    linarith
  · rw [← heq, show (1 + (-1 : ℝ)) ^ 2 * (p / 2) ^ 2 - 4 * -1 * (1 - p / 2) ^ 2 = (2 * (1 - p / 2)) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
    nlinarith

lemma sec5r_root_neg_one {p : ℝ} (hp2 : p < 2) : curveRoot (-1) (1 - p / 2) (p / 2) = 1 := by
  unfold curveRoot
  rw [show (1 + (-1 : ℝ)) ^ 2 * (p / 2) ^ 2 - 4 * -1 * (1 - p / 2) ^ 2 = (2 * (1 - p / 2)) ^ 2 by ring,
    Real.sqrt_sq (by linarith), div_eq_one_iff_eq (by nlinarith)]
  ring

lemma sec5r_kConst_nonneg {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    0 ≤ kConst p lam := by
  have hpi := Real.pi_pos
  have hC : 1 < gk p lam := lt_of_le_of_lt (le_max_left _ _)
    (gk_gt_max hp1 (ne_of_lt hp2) (ρ := (lam : ℂ)) (by
      intro hh
      have hh' : lam = 1 := by exact_mod_cast hh
      linarith))
  have hsin : 0 ≤ Real.sin (Real.pi / p) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (div_le_self hpi.le (by linarith))
  have hcos : 0 ≤ -Real.cos (Real.pi / p) := by
    have h2 : Real.pi / 2 ≤ Real.pi / p := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    have h3 : Real.pi / p ≤ Real.pi + Real.pi / 2 := by
      have := div_le_self hpi.le (show (1 : ℝ) ≤ p by linarith)
      linarith
    linarith [Real.cos_nonpos_of_pi_div_two_le_of_le h2 h3]
  unfold kConst
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
    (Real.rpow_nonneg hsin _)) (Real.rpow_nonneg hcos _)) (Real.rpow_nonneg (by nlinarith) _)

/-- `Φ` on the real axis where `Q ≥ 0`. -/
lemma sec5r_mobPhi_real {p C K lam x : ℝ} (hx : 0 ≤ x) (hQ : 0 ≤ (x - lam) * (1 - x)) :
    mobPhi p C K lam (x : ℂ) = (1 - lam) ^ p * (C ^ p - x ^ p) - K * ((x - lam) * (1 - x)) ^ (p / 2) := by
  have h2 : ((x : ℂ) - lam) * (1 - starRingEnd ℂ (x : ℂ)) = (((x - lam) * (1 - x) : ℝ) : ℂ) := by
    rw [Complex.conj_ofReal]
    push_cast
    ring
  unfold mobPhi reQPow mobQ
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, h2, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hQ, Complex.arg_ofReal_of_nonneg hQ, mul_zero, Real.cos_zero, mul_one]

lemma sec5r_phi_deriv {p C K lam x : ℝ} (hx : 0 < x) (hQ : 0 < (x - lam) * (1 - x)) :
    HasDerivAt (fun y : ℝ => (1 - lam) ^ p * (C ^ p - y ^ p) - K * ((y - lam) * (1 - y)) ^ (p / 2))
      ((1 - lam) ^ p * -(p * x ^ (p - 1)) - K * ((1 + lam - 2 * x) * (p / 2) * ((x - lam) * (1 - x)) ^ (p / 2 - 1)))
      x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ p) (p * x ^ (p - 1)) x := Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have hq : HasDerivAt (fun y : ℝ => (y - lam) * (1 - y)) (1 + lam - 2 * x) x := by
    have := ((hasDerivAt_id' x).sub_const lam).mul ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x))
    convert this using 1
    simp only [Pi.sub_apply]
    ring
  have h2 := hq.rpow_const (p := p / 2) (Or.inl hQ.ne')
  exact ((h1.const_sub (C ^ p)).const_mul ((1 - lam) ^ p)).sub (h2.const_mul K)

/-- `m(x) = (2x - 1 - λ) x^{1-p} Q(x)^{q-1}` increases on `(ρ₁, 1)`. -/
lemma sec5r_m_mono {p lam x y : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hx : (1 + lam) / 2 < x)
    (hxy : x ≤ y) (hy : y < 1) :
    (2 * x - 1 - lam) * x ^ (1 - p) * ((x - lam) * (1 - x)) ^ (p / 2 - 1) ≤
      (2 * y - 1 - lam) * y ^ (1 - p) * ((y - lam) * (1 - y)) ^ (p / 2 - 1) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hg : ∀ z : ℝ, 0 < z → (2 * z - 1 - lam) * z ^ (1 - p) = 2 * z ^ (2 - p) - (1 + lam) * z ^ (1 - p) := by
    intro z hz
    rw [show (2 : ℝ) - p = 1 + (1 - p) by ring, Real.rpow_add hz, Real.rpow_one]
    ring
  have hgle : (2 * x - 1 - lam) * x ^ (1 - p) ≤ (2 * y - 1 - lam) * y ^ (1 - p) := by
    rw [hg x hx0, hg y hy0]
    have h1 := Real.rpow_le_rpow hx0.le hxy (show (0 : ℝ) ≤ 2 - p by linarith)
    have h2 := Real.rpow_le_rpow_of_nonpos hx0 hxy (show 1 - p ≤ (0 : ℝ) by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 1 + lam by linarith)]
  have hQy : 0 < (y - lam) * (1 - y) := mul_pos (by linarith) (by linarith)
  have hQle : (y - lam) * (1 - y) ≤ (x - lam) * (1 - x) := by nlinarith
  have hpow := Real.rpow_le_rpow_of_nonpos hQy hQle (show p / 2 - 1 ≤ (0 : ℝ) by linarith)
  have hgy : 0 ≤ (2 * y - 1 - lam) * y ^ (1 - p) := mul_nonneg (by linarith) (Real.rpow_nonneg hy0.le _)
  exact mul_le_mul hgle hpow (Real.rpow_nonneg (by nlinarith) _) hgy

/-- The curve limit: `K_f(θ) → L` as `θ → 0⁺` (for `-1 < λ`, `ρ₀ > 0`, `2ρ₀ > 1 + λ`, `Q(ρ₀) > 0`). -/
lemma sec5r_Kf_tendsto {p lam ρ₀ : ℝ} (hl : -1 < lam) (hρ₀ : 0 < ρ₀) (h1 : 1 + lam < 2 * ρ₀)
    (hQ₀ : 0 < (ρ₀ - lam) * (1 - ρ₀)) (hp2 : p < 2)
    (hw : Tendsto (fun θ => mobW lam (curveZ p lam θ)) (𝓝[>] 0) (𝓝 ((ρ₀ : ℝ) : ℂ))) :
    Tendsto (curveKf p lam) (𝓝[>] 0)
      (𝓝 (2 * (1 - lam) ^ p * ρ₀ ^ (p - 2) * (ρ₀ / (1 + lam)) * ((ρ₀ - lam) * (1 - ρ₀)) ^ (1 - p / 2) /
        (2 * (ρ₀ / (1 + lam)) * 1 - 1))) := by
  have h1l : 0 < 1 + lam := by linarith
  have hwn : Tendsto (fun θ => ‖mobW lam (curveZ p lam θ)‖) (𝓝[>] 0) (𝓝 ρ₀) := by
    have := hw.norm
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ₀] at this
  have hvn : Tendsto (fun θ => ‖curveV p lam θ‖) (𝓝[>] 0) (𝓝 (1 + lam)) := by
    have hvc : Continuous (curveV p lam) := by unfold curveV; fun_prop
    have hv0 : curveV p lam 0 = ((1 + lam : ℝ) : ℂ) := by
      unfold curveV
      push_cast
      simp
    have := ((hvc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).norm
    rwa [hv0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1l] at this
  have hQn : Tendsto (fun θ => ‖mobQ lam (mobW lam (curveZ p lam θ))‖) (𝓝[>] 0)
      (𝓝 ((ρ₀ - lam) * (1 - ρ₀))) := by
    have hmq : Continuous (fun w : ℂ => mobQ lam w) := by
      unfold mobQ
      exact (continuous_id.sub continuous_const).mul (continuous_const.sub Complex.continuous_conj)
    have hQv : mobQ lam ((ρ₀ : ℝ) : ℂ) = (((ρ₀ - lam) * (1 - ρ₀) : ℝ) : ℂ) := by
      unfold mobQ
      rw [Complex.conj_ofReal]
      push_cast
      ring
    have := ((hmq.tendsto _).comp hw).norm
    rwa [hQv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ₀] at this
  have hcos : Tendsto (fun θ : ℝ => Real.cos ((1 - p / 2) * θ)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun θ : ℝ => Real.cos ((1 - p / 2) * θ)) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hr1 := hwn.rpow_const (p := p - 2) (Or.inl hρ₀.ne')
  have hr2 := hwn.div hvn h1l.ne'
  have hr3 := hQn.rpow_const (p := 1 - p / 2) (Or.inr (by linarith))
  have hnum := ((hr1.const_mul (2 * (1 - lam) ^ p)).mul hr2).mul hr3
  have hden := ((hr2.const_mul 2).mul hcos).sub_const 1
  have hden0 : 2 * (ρ₀ / (1 + lam)) * 1 - 1 ≠ 0 := by
    have : 1 < ρ₀ / (1 + lam) * 2 := by rw [div_mul_eq_mul_div, lt_div_iff₀ h1l]; linarith
    linarith
  unfold curveKf
  exact hnum.div hden hden0

/-- Reduction Step 2 (sec5_sharp_inequality.tex l.147-155): `Φ(ρ₀) ≤ Φ(ρ)` on the real segment `I`. -/
theorem reduction_step2 {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hdec : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi))
    (hw : Tendsto (fun θ => mobW lam (curveZ p lam θ)) (𝓝[>] 0)
      (𝓝 ((((1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) : ℝ)) : ℂ))) :
    ∀ ρ : ℝ, 0 ≤ ρ → (0 < lam → Real.sqrt lam ≤ ρ) →
      ρ ≤ (1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) →
      mobPhi p (gk p lam) (kConst p lam) lam
          ((((1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) : ℝ)) : ℂ) ≤
        mobPhi p (gk p lam) (kConst p lam) lam (ρ : ℂ) := by
  intro ρ hρ0 hρl hρρ₀
  have hp0 : 0 < p := by linarith
  have hpi := Real.pi_pos
  have hr0 := sec5r_root_pos hp1 hp2 hl
  have hK0 := sec5r_kConst_nonneg hp1 hp2 hl hl1
  have hKf := contact_Kf hp1 hp2 hl hl1
  obtain ⟨r₀, hr₀⟩ : ∃ r, r = curveRoot lam (1 - p / 2) (p / 2) := ⟨_, rfl⟩
  rw [← hr₀] at hρρ₀ hw hr0 ⊢
  obtain ⟨ρ₀, hρ₀⟩ : ∃ x, x = (1 + lam * r₀) / (1 + r₀) := ⟨_, rfl⟩
  rw [← hρ₀] at hρρ₀ hw ⊢
  obtain ⟨K, hK⟩ : ∃ K, K = kConst p lam := ⟨_, rfl⟩
  rw [← hK] at hK0 hKf ⊢
  have hρ₀1 : ρ₀ < 1 := by
    rw [hρ₀, div_lt_one (by linarith)]
    nlinarith
  have hρ₀l : lam < ρ₀ := by
    rw [hρ₀, lt_div_iff₀ (by linarith)]
    nlinarith
  have hQ₀ : 0 < (ρ₀ - lam) * (1 - ρ₀) := mul_pos (by linarith) (by linarith)
  have hρ₀0 : 0 ≤ ρ₀ := hρ0.trans hρρ₀
  have hsq : 0 < lam → lam ≤ Real.sqrt lam := by
    intro hl0
    have hs1 : Real.sqrt lam ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hl1.le
    nlinarith [Real.sq_sqrt hl0.le, Real.sqrt_nonneg lam]
  have hlow : ∀ x, ρ ≤ x → lam ≤ x := by
    intro x hx
    rcases le_or_gt lam 0 with h | h
    · linarith
    · linarith [hsq h, hρl h]
  have hQρ : 0 ≤ (ρ - lam) * (1 - ρ) := mul_nonneg (by linarith [hlow ρ le_rfl]) (by linarith)
  rw [sec5r_mobPhi_real hρ₀0 hQ₀.le, sec5r_mobPhi_real hρ0 hQρ]
  -- the curve bound `K m(ρ₀) ≤ 2(1 - λ)^p` when `ρ₁ < ρ₀`
  have hKm : (1 + lam) / 2 < ρ₀ →
      K * ((2 * ρ₀ - 1 - lam) * ρ₀ ^ (1 - p) * ((ρ₀ - lam) * (1 - ρ₀)) ^ (p / 2 - 1)) ≤ 2 * (1 - lam) ^ p := by
    intro h1
    have hl' : -1 < lam := by
      rcases hl.lt_or_eq with h | h
      · exact h
      · exfalso
        have hr : r₀ = 1 := by rw [hr₀, ← h]; exact sec5r_root_neg_one hp2
        rw [hρ₀, hr, ← h] at h1
        norm_num at h1
    have h1l : 0 < 1 + lam := by linarith
    have hρ₀p : 0 < ρ₀ := by linarith
    have hT := sec5r_Kf_tendsto hl' hρ₀p (by linarith) hQ₀ hp2 hw
    have hθ0 : 0 < Real.pi / p := by positivity
    have hθπ : Real.pi / p < Real.pi := div_lt_self hpi hp1
    have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), K ≤ curveKf p lam θ := by
      filter_upwards [Ioo_mem_nhdsGT hθ0] with θ hθ
      have := hdec ⟨hθ.1, hθ.2.trans hθπ⟩ ⟨hθ0, hθπ⟩ hθ.2
      rw [hKf] at this
      exact this.le
    have hKL := ge_of_tendsto hT hev
    have hm0 : 0 ≤ (2 * ρ₀ - 1 - lam) * ρ₀ ^ (1 - p) * ((ρ₀ - lam) * (1 - ρ₀)) ^ (p / 2 - 1) :=
      mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hρ₀0 _)) (Real.rpow_nonneg hQ₀.le _)
    have hab : ρ₀ ^ (p - 2) * ρ₀ ^ (1 - p) * ρ₀ = 1 := by
      rw [← Real.rpow_add hρ₀p, ← Real.rpow_add_one hρ₀p.ne', show p - 2 + (1 - p) + 1 = (0 : ℝ) by ring,
        Real.rpow_zero]
    have hcd : ((ρ₀ - lam) * (1 - ρ₀)) ^ (1 - p / 2) * ((ρ₀ - lam) * (1 - ρ₀)) ^ (p / 2 - 1) = 1 := by
      rw [← Real.rpow_add hQ₀, show 1 - p / 2 + (p / 2 - 1) = (0 : ℝ) by ring, Real.rpow_zero]
    have hden_eq : 2 * (ρ₀ / (1 + lam)) * 1 - 1 = (2 * ρ₀ - 1 - lam) / (1 + lam) := by
      rw [eq_div_iff h1l.ne']
      linear_combination (2 * ρ₀) * mul_inv_cancel₀ h1l.ne'
    have hne : (2 * ρ₀ - 1 - lam) / (1 + lam) ≠ 0 := div_ne_zero (by linarith) h1l.ne'
    have hLm : 2 * (1 - lam) ^ p * ρ₀ ^ (p - 2) * (ρ₀ / (1 + lam)) * ((ρ₀ - lam) * (1 - ρ₀)) ^ (1 - p / 2) /
        (2 * (ρ₀ / (1 + lam)) * 1 - 1) *
        ((2 * ρ₀ - 1 - lam) * ρ₀ ^ (1 - p) * ((ρ₀ - lam) * (1 - ρ₀)) ^ (p / 2 - 1)) = 2 * (1 - lam) ^ p := by
      have key : 2 * (1 - lam) ^ p * ρ₀ ^ (p - 2) * (ρ₀ / (1 + lam)) * ((ρ₀ - lam) * (1 - ρ₀)) ^ (1 - p / 2) /
          (2 * (ρ₀ / (1 + lam)) * 1 - 1) *
          ((2 * ρ₀ - 1 - lam) * ρ₀ ^ (1 - p) * ((ρ₀ - lam) * (1 - ρ₀)) ^ (p / 2 - 1)) =
          2 * (1 - lam) ^ p * (ρ₀ ^ (p - 2) * ρ₀ ^ (1 - p) * ρ₀) *
            (((ρ₀ - lam) * (1 - ρ₀)) ^ (1 - p / 2) * ((ρ₀ - lam) * (1 - ρ₀)) ^ (p / 2 - 1)) *
            ((2 * ρ₀ - 1 - lam) / (1 + lam) / (2 * (ρ₀ / (1 + lam)) * 1 - 1)) := by ring
      rw [key, hab, hcd, hden_eq, div_self hne]
      ring
    calc K * ((2 * ρ₀ - 1 - lam) * ρ₀ ^ (1 - p) * ((ρ₀ - lam) * (1 - ρ₀)) ^ (p / 2 - 1))
        ≤ 2 * (1 - lam) ^ p * ρ₀ ^ (p - 2) * (ρ₀ / (1 + lam)) * ((ρ₀ - lam) * (1 - ρ₀)) ^ (1 - p / 2) /
            (2 * (ρ₀ / (1 + lam)) * 1 - 1) *
            ((2 * ρ₀ - 1 - lam) * ρ₀ ^ (1 - p) * ((ρ₀ - lam) * (1 - ρ₀)) ^ (p / 2 - 1)) :=
          mul_le_mul_of_nonneg_right hKL hm0
      _ = 2 * (1 - lam) ^ p := hLm
  -- `Φ` is antitone on `[ρ, ρ₀]`
  have hcont : ContinuousOn
      (fun y : ℝ => (1 - lam) ^ p * (gk p lam ^ p - y ^ p) - K * ((y - lam) * (1 - y)) ^ (p / 2)) (Icc ρ ρ₀) :=
    ((continuous_const.mul (continuous_const.sub (continuous_id.rpow_const fun _ => Or.inr hp0.le))).sub
      (continuous_const.mul (((continuous_id.sub continuous_const).mul (continuous_const.sub continuous_id)).rpow_const
        fun _ => Or.inr (by linarith)))).continuousOn
  have hint : ∀ x ∈ interior (Icc ρ ρ₀), 0 < x ∧ 0 < (x - lam) * (1 - x) := by
    intro x hx
    rw [interior_Icc] at hx
    refine ⟨by linarith [hx.1], mul_pos ?_ (by linarith [hx.2])⟩
    rcases le_or_gt lam 0 with h | h
    · linarith [hx.1]
    · linarith [hsq h, hρl h, hx.1]
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc ρ ρ₀) hcont
    (fun x hx => (sec5r_phi_deriv (C := gk p lam) (K := K) (hint x hx).1 (hint x hx).2).differentiableAt
      |>.differentiableWithinAt)
    (by
      intro x hx
      obtain ⟨hx0, hQx⟩ := hint x hx
      rw [interior_Icc] at hx
      rw [(sec5r_phi_deriv (C := gk p lam) (K := K) hx0 hQx).deriv]
      by_cases hx1 : 2 * x ≤ 1 + lam
      · have h1 : 0 ≤ (1 - lam) ^ p * (p * x ^ (p - 1)) :=
          mul_nonneg (Real.rpow_nonneg (by linarith) _) (mul_nonneg hp0.le (Real.rpow_nonneg hx0.le _))
        have h2 : 0 ≤ K * ((1 + lam - 2 * x) * (p / 2) * ((x - lam) * (1 - x)) ^ (p / 2 - 1)) :=
          mul_nonneg hK0 (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (Real.rpow_nonneg hQx.le _))
        rw [mul_neg]
        linarith
      · rw [not_le] at hx1
        have hρ₁x : (1 + lam) / 2 < x := by linarith
        have hmono := sec5r_m_mono hp1 hp2 hl hρ₁x hx.2.le hρ₀1
        have hKmx : K * ((2 * x - 1 - lam) * x ^ (1 - p) * ((x - lam) * (1 - x)) ^ (p / 2 - 1)) ≤
            2 * (1 - lam) ^ p :=
          (mul_le_mul_of_nonneg_left hmono hK0).trans (hKm (by linarith [hx.2]))
        have hxx : x ^ (1 - p) * x ^ (p - 1) = 1 := by
          rw [← Real.rpow_add hx0, show 1 - p + (p - 1) = (0 : ℝ) by ring, Real.rpow_zero]
        have hm := mul_le_mul_of_nonneg_right hKmx
          (mul_nonneg (by linarith : (0 : ℝ) ≤ p / 2) (Real.rpow_nonneg hx0.le (p - 1)))
        have e1 : K * ((2 * x - 1 - lam) * x ^ (1 - p) * ((x - lam) * (1 - x)) ^ (p / 2 - 1)) *
            (p / 2 * x ^ (p - 1)) = K * ((2 * x - 1 - lam) * (p / 2) * ((x - lam) * (1 - x)) ^ (p / 2 - 1)) := by
          linear_combination (K * (2 * x - 1 - lam) * (p / 2) * ((x - lam) * (1 - x)) ^ (p / 2 - 1)) * hxx
        rw [e1] at hm
        have e2 : (1 - lam) ^ p * -(p * x ^ (p - 1)) -
            K * ((1 + lam - 2 * x) * (p / 2) * ((x - lam) * (1 - x)) ^ (p / 2 - 1)) =
            K * ((2 * x - 1 - lam) * (p / 2) * ((x - lam) * (1 - x)) ^ (p / 2 - 1)) -
              2 * (1 - lam) ^ p * (p / 2 * x ^ (p - 1)) := by ring
        rw [e2]
        linarith)
  exact hanti ⟨le_rfl, hρρ₀⟩ ⟨hρρ₀, le_rfl⟩ hρρ₀

end GKSharp

