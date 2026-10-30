/-
GKSharp/Proofs/Q15Misc.lean — paper 019 short v1.80, norm_correspondence.tex l.56-57, sec2_obstacle.tex l.143 and
sec5e_cstar.tex l.22 (the Q15 routes): proofs of the rows q15_normcorr_real_ratio, q15_sec2_envelope_route and
q15_sec5e_star_holds.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Route: the classical endpoints (pencilNorm_one, gk_one; Theorem 5.1 at λ = −1); Lemma 2.2 uniqueness, bounded
minimizers and compactness for the minimizer limit, then the contact derivative row; the "if" half of Theorem 5.3.
-/
import GKSharp.Proofs.GKSymm
import GKSharp.Proofs.TheoremC1
import GKSharp.Proofs.TheoremCstar
import GKSharp.Proofs.ContactDerivativeFull
import GKSharp.Proofs.ObstacleMinimum
import GKSharp.Proofs.Gamma

namespace GKSharp.Proofs.Q15Misc

open Set Filter
open scoped Topology

/-- norm_correspondence l.56-57: for real `a, b` with `a − ib ≠ 0`, `ρ = (a + ib)/(a − ib)` is real only for `ρ = ±1`;
`ρ = 1` iff `b = 0` (multiples of `I`), `ρ = −1` iff `a = 0` (multiples of `H`); there the bound is sharp
(`N_p(ρ) = GK_p(ρ)`), so a failure `N_p(ρ) > GK_p(ρ)` in this real-coefficient family has a non-real ratio. -/
theorem q15_normcorr_real_ratio_proved {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p)
    (a b : ℝ) (hab : (a : ℂ) - Complex.I * b ≠ 0) :
    let ρ := ((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b)
    (ρ.im = 0 ↔ ρ = 1 ∨ ρ = -1) ∧ (ρ = 1 ↔ b = 0) ∧ (ρ = -1 ↔ a = 0) ∧
    (ρ.im = 0 → pencilNorm P ρ = gk p ρ) ∧ (gk p ρ < pencilNorm P ρ → ρ.im ≠ 0) := by
  intro ρ
  have h2 : a ^ 2 + b ^ 2 ≠ 0 := by
    intro h0
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    apply hab
    simp [ha, hb]
  have him : ρ.im = 2 * a * b / (a ^ 2 + b ^ 2) := by
    show (((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b)).im = _
    have hn : Complex.normSq ((a : ℂ) - Complex.I * b) = a ^ 2 + b ^ 2 := by
      rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    rw [Complex.div_im, hn]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hone : ρ = 1 ↔ b = 0 := by
    show ((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b) = 1 ↔ b = 0
    rw [div_eq_one_iff_eq hab]
    constructor
    · intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    · intro hb
      simp [hb]
  have hmone : ρ = -1 ↔ a = 0 := by
    show ((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b) = -1 ↔ a = 0
    rw [div_eq_iff hab]
    constructor
    · intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    · intro ha
      simp [ha]
  have hreal : ρ.im = 0 ↔ ρ = 1 ∨ ρ = -1 := by
    rw [him, hone, hmone, div_eq_zero_iff, or_iff_left h2, mul_eq_zero, mul_eq_zero]
    constructor
    · rintro ((h | h) | h)
      · norm_num at h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
  have hsharp : ρ.im = 0 → pencilNorm P ρ = gk p ρ := by
    intro h
    rcases hreal.mp h with h1 | h1
    · rw [h1, pencilNorm_one, gk_one]
    · have h' := GKSharp.Proofs.TheoremC1.thm_C1_proved hp P (lam := -1) le_rfl (by norm_num)
      rw [h1]
      simpa using h'
  refine ⟨hreal, hone, hmone, hsharp, fun hlt h0 => ?_⟩
  rw [hsharp h0] at hlt
  exact lt_irrefl _ hlt

/-- sec2_obstacle l.143 (`C = GK_p(λ)`, `θ₀ = π/p`, `y_* = log r_*`): the minimizer at `θ₀` is unique; minimality gives
`Γ_C(y_t, t) − Γ_C(y_t, θ₀) ≤ m_C(t) − m_C(θ₀) ≤ Γ_C(y_*, t) − Γ_C(y_*, θ₀)`; minimizers `y_t` for `t` near `θ₀` tend to
`y_*`; and `m_C′(θ₀) = ∂_tΓ_C(y_*, θ₀)`, hence `K = −m_C′(θ₀)/q`. -/
theorem q15_sec2_envelope_route_proved {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (lam : ℝ)
    (hlam : -1 ≤ lam ∧ lam < 1) :
    let C := gk p (lam : ℂ)
    let θ₀ := Real.pi / p
    let ystar := Real.log (contactRadius p lam)
    (∀ y : ℝ, GKSharp.gamma p C lam y θ₀ = GKSharp.obstacle p C lam θ₀ → y = ystar) ∧
    (∀ t yt : ℝ, GKSharp.gamma p C lam yt t = GKSharp.obstacle p C lam t →
      GKSharp.gamma p C lam yt t - GKSharp.gamma p C lam yt θ₀ ≤
          GKSharp.obstacle p C lam t - GKSharp.obstacle p C lam θ₀ ∧
        GKSharp.obstacle p C lam t - GKSharp.obstacle p C lam θ₀ ≤
          GKSharp.gamma p C lam ystar t - GKSharp.gamma p C lam ystar θ₀) ∧
    (∀ sel : ℝ → ℝ, (∀ᶠ t in 𝓝 θ₀, GKSharp.gamma p C lam (sel t) t = GKSharp.obstacle p C lam t) →
      Tendsto sel (𝓝 θ₀) (𝓝 ystar)) ∧
    DifferentiableAt ℝ (GKSharp.obstacle p C lam) θ₀ ∧
    deriv (GKSharp.obstacle p C lam) θ₀ = deriv (fun t => GKSharp.gamma p C lam ystar t) θ₀ ∧
    kConst p lam = -deriv (GKSharp.obstacle p C lam) θ₀ / (p / 2) := by
  intro C θ₀ ystar
  have hp0 : 0 < p := by linarith
  have hC : max 1 ‖(lam : ℂ)‖ < C :=
    gk_gt_max hp (ne_of_lt hp2) (fun hh => by
      have : lam = 1 := by exact_mod_cast hh
      linarith [hlam.2])
  have hlb : ∀ t y : ℝ, GKSharp.obstacle p C lam t ≤ GKSharp.gamma p C lam y t := fun t y =>
    csInf_le (obstacle_bddBelow hp0 (lam : ℂ) hC t) ⟨y, rfl⟩
  have hob0 : GKSharp.obstacle p C lam θ₀ = 0 :=
    (slice_O33_proved p hp hp2 C lam (lt_of_le_of_lt (le_max_left _ _) hC) hlam).2.2.1
  have hzero : ∀ y : ℝ, GKSharp.gamma p C lam y θ₀ = 0 → y = ystar := by
    intro y hy
    have hy' : Threshold.gammaGK p lam y (Threshold.theta p) = 0 := hy
    have he := (ContactLower.gamma_contact_zero_iff p lam y hp hp2 ⟨hlam.1, hlam.2⟩).mp hy'
    show y = Real.log (contactRadius p lam)
    rw [← he, Real.log_exp]
  obtain ⟨y0, -, heq0⟩ := obstacle_eq_min hp0 (lam : ℂ) hC θ₀
  have hy0 : y0 = ystar := hzero y0 (by rw [← heq0]; exact hob0)
  have hstar : GKSharp.gamma p C lam ystar θ₀ = GKSharp.obstacle p C lam θ₀ := by rw [← hy0, ← heq0]
  have huniq : ∀ y : ℝ, GKSharp.gamma p C lam y θ₀ = GKSharp.obstacle p C lam θ₀ → y = ystar :=
    fun y hy => hzero y (hy.trans hob0)
  have hsand : ∀ t yt : ℝ, GKSharp.gamma p C lam yt t = GKSharp.obstacle p C lam t →
      GKSharp.gamma p C lam yt t - GKSharp.gamma p C lam yt θ₀ ≤
          GKSharp.obstacle p C lam t - GKSharp.obstacle p C lam θ₀ ∧
        GKSharp.obstacle p C lam t - GKSharp.obstacle p C lam θ₀ ≤
          GKSharp.gamma p C lam ystar t - GKSharp.gamma p C lam ystar θ₀ := by
    intro t yt hyt
    refine ⟨by linarith [hlb θ₀ yt], by linarith [hlb t ystar]⟩
  -- minimizers near `θ₀` tend to `y_*`: bounded minimizers, joint continuity, uniqueness at `θ₀`
  have hlim : ∀ sel : ℝ → ℝ, (∀ᶠ t in 𝓝 θ₀, GKSharp.gamma p C lam (sel t) t = GKSharp.obstacle p C lam t) →
      Tendsto sel (𝓝 θ₀) (𝓝 ystar) := by
    intro sel hsel
    obtain ⟨Y, -, hY⟩ := gamma_minimizers_bounded hp0 (lam : ℂ) hC
    refine isCompact_Icc.tendsto_nhds_of_unique_mapClusterPt (s := Icc (-Y) Y) ?_ ?_
    · filter_upwards [hsel] with t ht
      exact abs_le.mp (hY t (sel t) (fun y => (le_of_eq ht).trans (hlb t y)))
    · intro x _ hx
      apply huniq x
      refine le_antisymm ?_ (hlb θ₀ x)
      by_contra hgt
      rw [not_le] at hgt
      obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (GKSharp.gamma p C lam x θ₀ - GKSharp.obstacle p C lam θ₀) / 3 :=
        ⟨_, rfl⟩
      have hε0 : 0 < ε := by rw [hε]; linarith
      have hcont : ContinuousAt (fun q : ℝ × ℝ => GKSharp.gamma p C lam q.1 q.2) (x, θ₀) :=
        (continuous_gamma hp0 C (lam : ℂ)).continuousAt
      have hnb : ∀ᶠ q in 𝓝 (x, θ₀), GKSharp.gamma p C lam x θ₀ - ε < GKSharp.gamma p C lam q.1 q.2 :=
        hcont.eventually (Ioi_mem_nhds
          (show GKSharp.gamma p C lam x θ₀ - ε < GKSharp.gamma p C lam x θ₀ by linarith))
      obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hnb
      have hobc : ∀ᶠ t in 𝓝 θ₀, GKSharp.obstacle p C lam t < GKSharp.obstacle p C lam θ₀ + ε :=
        (obstacle_continuous hp0 (lam : ℂ) hC).continuousAt.eventually (Iio_mem_nhds (by linarith))
      have hfreq := (mapClusterPt_iff_frequently.mp hx) U hU
      obtain ⟨t, htU, htV, htob, hteq⟩ :=
        (hfreq.and_eventually ((show ∀ᶠ t in 𝓝 θ₀, t ∈ V from hV).and (hobc.and hsel))).exists
      have hin := hUV (Set.mk_mem_prod htU htV)
      simp only [Set.mem_ofPred_eq] at hin
      linarith
  obtain ⟨hd1, -, hk1, hk2⟩ := slice_O35_proved p hp hp2 lam hlam
  have hderiv : deriv (GKSharp.obstacle p C lam) θ₀ = deriv (fun t => GKSharp.gamma p C lam ystar t) θ₀ := by
    have h := hk2.symm.trans hk1
    have hq : p / 2 ≠ 0 := by positivity
    field_simp at h
    linarith
  exact ⟨huniq, hsand, hlim, hd1, hderiv, hk2⟩

/-- sec5e_cstar l.12-22 ("If" part of Theorem 5.3, `1 < p < 2`, `0 < λ < 1`, `h(λ, p) ≥ 0`, `λ < λ_loc(p)`): "So (*)
holds (at z = −1 by continuity)": `𝒟_C ≥ 0` on all of `ℂ`, in particular at `z = −1`. No computer check is used. -/
theorem q15_sec5e_star_holds_proved {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam < 1) (hh : kConst p lam ≤ obstacle p (gk p lam) lam 0) (hloc : lam < Threshold.lambdaLoc p) :
    (∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) ∧
      0 ≤ critD p (gk p lam) (kConst p lam) lam (-1) := by
  have hl : -1 ≤ lam := by linarith
  have hA2 := sec5_A2_proved hp1 hp2 hl hl1
  have hρ0 : 0 ≤ (1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) :=
    hA2.2.2.2.2.1
  have hA3 : ∀ ρ : ℝ, 0 < ρ → _ := fun ρ hρ =>
    Proofs.SharpA3.sec5_A3_of_A1_A2 hp1 hp2 hl hl1 hρ (sec5_A1_proved hp1 hp2 hl hl1 hρ) hA2
  have hzero := CstarCurve.sec5e_Lambda_zero_proved hp1 hp2 hl0 hl1
  dsimp only at hzero
  have hcurve := CstarCurve.cstar_curve_nonneg_proved hp1 hp2 hl0 hl1
    (sec5e_Kf_below_proved TheoremCstar.kf_slope hp1 hp2 hl0 hl1 hh hloc).2 (hzero.2 hh)
  have hw := Proofs.Reduction.reduction_step3_nonneg_of (Proofs.Reduction.kConst_pos hp1 hp2 hl hl1)
    (fun ρ hgt => by
      have h := hA3 ρ (hρ0.trans_lt hgt)
      dsimp only at h
      obtain ⟨φc, -, θ, hθ, -, hpt, -, -, hmax⟩ := h.1 hgt
      exact ⟨φc, θ, hθ, hpt, hmax⟩)
    (fun ρ hρ hle hlam => by
      have h := hA3 ρ hρ
      dsimp only at h
      exact (h.2 hle hlam).2)
    hcurve (CstarSegment.cstar_real_segment_proved hp1 hp2 hl0 hl1 hh)
  have hall := Proofs.Reduction.critD_nonneg_of_step3 hp1 hp2 hl hl1 hw
  exact ⟨hall, hall (-1)⟩

end GKSharp.Proofs.Q15Misc
