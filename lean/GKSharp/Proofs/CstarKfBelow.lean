/- the sublevel set of K_f in the "If" part of Theorem C*, frozen sec5e_cstar.tex:15-17 (row sec5e_Kf_below;
type verbatim from the approved slice (c) proposal v0.61). CONDITIONAL only on the open row sec5e_Kf_slope, through its
second conjunct K_f'(θ₀) < 0 (premise type KfSlopeHyp).
Route = the text: by Lemmas B⁺ (3-√3 ≤ p) and U (p < 4/3) K_f is decreasing, or increasing on (0, θ_λ] and decreasing
afterwards; K_f'(θ₀) < 0 forces θ_λ < θ₀ (θ₀ = π/p). With K_f(θ₀) = K, monotonicity and the intermediate value theorem
give {K_f < K} = (0, θ_a) ∪ (θ₀, π) with θ_a ∈ [0, θ₀).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneSign
import GKSharp.Proofs.MonotoneUE
import GKSharp.Proofs.Contact
import GKSharp.Defs.Threshold

namespace GKSharp

namespace CstarBelow

open Set Filter Topology

/-- A function with negative derivative at `θ₀ > 0` is not strictly increasing on any `(0, θl]` containing `θ₀`. -/
theorem turn_before {f : ℝ → ℝ} {θ0 θl d : ℝ} (hd : HasDerivAt f d θ0) (hneg : d < 0) (hθ0 : 0 < θ0)
    (hmono : StrictMonoOn f (Ioc 0 θl)) : θl < θ0 := by
  by_contra hle
  have hle' : θ0 ≤ θl := not_lt.1 hle
  have hθ0s : θ0 ∈ Ioc 0 θl := ⟨hθ0, hle'⟩
  have hlim : Tendsto (slope f θ0) (𝓝[<] θ0) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.1 hd).mono_left (nhdsWithin_mono _ fun x hx => ne_of_lt hx)
  have hpos : ∀ᶠ x in 𝓝[<] θ0, 0 ≤ slope f θ0 x := by
    filter_upwards [Ioo_mem_nhdsLT hθ0] with x hx
    have hfx : f x < f θ0 := hmono ⟨hx.1, hx.2.le.trans hle'⟩ hθ0s hx.2
    rw [slope_def_field]
    exact (div_pos_of_neg_of_neg (by linarith) (by linarith [hx.2])).le
  exact absurd (ge_of_tendsto hlim hpos) (not_le.2 hneg)

/-- On `(0, θl]` a continuous strictly increasing `f` with `K < f θl` is below `K` exactly on an initial interval. -/
theorem initial_below {f : ℝ → ℝ} {K θl : ℝ} (hθl : 0 < θl) (hcont : ContinuousOn f (Ioc 0 θl))
    (hmono : StrictMonoOn f (Ioc 0 θl)) (hKl : K < f θl) :
    ∃ θa ∈ Icc 0 θl, ∀ θ ∈ Ioc 0 θl, (f θ < K ↔ θ < θa) := by
  by_cases hex : ∃ θ1 ∈ Ioc 0 θl, f θ1 < K
  · obtain ⟨θ1, hθ1, hf1⟩ := hex
    have hc : ContinuousOn f (Icc θ1 θl) := hcont.mono fun x hx => ⟨hθ1.1.trans_le hx.1, hx.2⟩
    obtain ⟨θa, hθa, hfa⟩ := intermediate_value_Icc hθ1.2 hc ⟨hf1.le, hKl.le⟩
    have hθas : θa ∈ Ioc 0 θl := ⟨hθ1.1.trans_le hθa.1, hθa.2⟩
    refine ⟨θa, ⟨hθas.1.le, hθa.2⟩, fun θ hθ => ?_⟩
    rw [← hfa]
    exact hmono.lt_iff_lt hθ hθas
  · simp only [not_exists, not_and, not_lt] at hex
    exact ⟨0, ⟨le_rfl, hθl.le⟩, fun θ hθ =>
      ⟨fun h => absurd h (not_lt.2 (hex θ hθ)), fun h => absurd h (not_lt.2 hθ.1.le)⟩⟩

/-- Sublevel set of a decreasing function through `f θ₀ = K`. -/
theorem below_set_anti {f : ℝ → ℝ} {K θ0 : ℝ} (hθ0 : 0 < θ0) (hθ0π : θ0 < Real.pi) (hK : f θ0 = K)
    (hanti : StrictAntiOn f (Ioo 0 Real.pi)) :
    {θ ∈ Ioo 0 Real.pi | f θ < K} = Ioo 0 0 ∪ Ioo θ0 Real.pi := by
  have hθ0s : θ0 ∈ Ioo 0 Real.pi := ⟨hθ0, hθ0π⟩
  ext θ
  constructor
  · rintro ⟨hθ, hlt⟩
    rw [← hK] at hlt
    exact Or.inr ⟨(hanti.lt_iff_gt hθ hθ0s).1 hlt, hθ.2⟩
  · rintro (h | h)
    · exact absurd (h.1.trans h.2) (lt_irrefl 0)
    · have hθ : θ ∈ Ioo 0 Real.pi := ⟨hθ0.trans h.1, h.2⟩
      refine ⟨hθ, ?_⟩
      rw [← hK]
      exact (hanti.lt_iff_gt hθ hθ0s).2 h.1

/-- Sublevel set of an increasing-then-decreasing function through `f θ₀ = K`, turning point `θl < θ₀`. -/
theorem below_set_turn {f : ℝ → ℝ} {K θ0 θl : ℝ} (hθ0π : θ0 < Real.pi) (hK : f θ0 = K)
    (hcont : ContinuousOn f (Ioo 0 Real.pi)) (hθl : θl ∈ Ioo 0 θ0) (hmono : StrictMonoOn f (Ioc 0 θl))
    (hanti : StrictAntiOn f (Ico θl Real.pi)) :
    ∃ θa ∈ Ico 0 θ0, {θ ∈ Ioo 0 Real.pi | f θ < K} = Ioo 0 θa ∪ Ioo θ0 Real.pi := by
  have hθlπ : θl < Real.pi := hθl.2.trans hθ0π
  have hθ0s : θ0 ∈ Ico θl Real.pi := ⟨hθl.2.le, hθ0π⟩
  have hKl : K < f θl := by
    rw [← hK]
    exact hanti ⟨le_rfl, hθlπ⟩ hθ0s hθl.2
  have hc : ContinuousOn f (Ioc 0 θl) := hcont.mono fun x hx => ⟨hx.1, hx.2.trans_lt hθlπ⟩
  obtain ⟨θa, hθa, hiff⟩ := initial_below hθl.1 hc hmono hKl
  refine ⟨θa, ⟨hθa.1, hθa.2.trans_lt hθl.2⟩, ?_⟩
  ext θ
  constructor
  · rintro ⟨hθ, hlt⟩
    rcases le_or_gt θ θl with hle | hgt
    · exact Or.inl ⟨hθ.1, (hiff θ ⟨hθ.1, hle⟩).1 hlt⟩
    · rw [← hK] at hlt
      exact Or.inr ⟨(hanti.lt_iff_gt ⟨hgt.le, hθ.2⟩ hθ0s).1 hlt, hθ.2⟩
  · rintro (h | h)
    · have hle : θ ≤ θl := h.2.le.trans hθa.2
      exact ⟨⟨h.1, hle.trans_lt hθlπ⟩, (hiff θ ⟨h.1, hle⟩).2 h.2⟩
    · have hθs : θ ∈ Ico θl Real.pi := ⟨hθl.2.le.trans h.1.le, h.2⟩
      refine ⟨⟨hθl.1.trans_le hθs.1, h.2⟩, ?_⟩
      rw [← hK]
      exact (hanti.lt_iff_gt hθs hθ0s).2 h.1

/-- The shape of `K_f` for `0 < λ < 1` (Lemma U for `p < 4/3`, Lemma B⁺ for `p ≥ 4/3 > 3 - √3`). -/
theorem Kf_shape {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1) :
    StrictAntiOn (curveKf p lam) (Ioo 0 Real.pi) ∨
      ∃ θl ∈ Ioo 0 Real.pi, StrictMonoOn (curveKf p lam) (Ioc 0 θl) ∧
        StrictAntiOn (curveKf p lam) (Ico θl Real.pi) := by
  rcases lt_or_ge p (4 / 3) with hp43 | hp43
  · exact (lemma_U_proved @lemma_onevar_proved hp1 hp43).2 lam ⟨hl0, hl1⟩
  · have hs : 3 - Real.sqrt 3 ≤ p := by
      have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [Real.sqrt_nonneg 3]
    exact Or.inl (lemma_Bplus_proved @lemma_onevar_proved hs hp2 (by linarith) hl1)

/-- The row's conclusion from the single fact `K_f'(θ₀) < 0`. -/
theorem Kf_below_of_slope {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hslope : deriv (curveKf p lam) (Real.pi / p) < 0) :
    (StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) ∨
      ∃ θl ∈ Set.Ioo 0 (Real.pi / p), StrictMonoOn (curveKf p lam) (Set.Ioc 0 θl) ∧
        StrictAntiOn (curveKf p lam) (Set.Ico θl Real.pi)) ∧
    ∃ θa ∈ Set.Ico 0 (Real.pi / p),
      {θ ∈ Set.Ioo 0 Real.pi | curveKf p lam θ < kConst p lam} =
        Set.Ioo 0 θa ∪ Set.Ioo (Real.pi / p) Real.pi := by
  have hθ0 : 0 < Real.pi / p := div_pos Real.pi_pos (by linarith)
  have hθ0π : Real.pi / p < Real.pi := div_lt_self Real.pi_pos hp1
  have hdiff : ∀ θ ∈ Ioo 0 Real.pi, DifferentiableAt ℝ (curveKf p lam) θ := fun θ hθ =>
    (lemma_onevar_proved hp1 hp2 (by linarith) hl1 hθ.1 hθ.2).1
  have hcont : ContinuousOn (curveKf p lam) (Ioo 0 Real.pi) := fun θ hθ =>
    (hdiff θ hθ).continuousAt.continuousWithinAt
  have hd := (hdiff _ ⟨hθ0, hθ0π⟩).hasDerivAt
  have hK := contact_Kf hp1 hp2 (by linarith) hl1
  rcases Kf_shape hp1 hp2 hl0 hl1 with hanti | ⟨θl, hθl, hmono, hanti⟩
  · exact ⟨Or.inl hanti, 0, ⟨le_rfl, hθ0⟩, below_set_anti hθ0 hθ0π hK hanti⟩
  · have hθl0 : θl ∈ Ioo 0 (Real.pi / p) := ⟨hθl.1, turn_before hd hslope hθ0 hmono⟩
    exact ⟨Or.inr ⟨θl, hθl0, hmono, hanti⟩, below_set_turn hθ0π hK hcont hθl0 hmono hanti⟩

end CstarBelow

/-- The second conjunct of the open row `sec5e_Kf_slope` (its first conjunct uses the proposal-local `lamCurve`). -/
abbrev KfSlopeHyp : Prop :=
  ∀ {p lam : ℝ}, 1 < p → p < 2 → 0 < lam → lam < 1 → kConst p lam ≤ obstacle p (gk p lam) lam 0 →
    lam < Threshold.lambdaLoc p → deriv (curveKf p lam) (Real.pi / p) < 0

/-- Row `sec5e_Kf_below`, premise-style on the open row `sec5e_Kf_slope` (second conjunct). -/
theorem sec5e_Kf_below_proved (slope : KfSlopeHyp) {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hh : kConst p lam ≤ obstacle p (gk p lam) lam 0) (hloc : lam < Threshold.lambdaLoc p) :
    (StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) ∨
      ∃ θl ∈ Set.Ioo 0 (Real.pi / p), StrictMonoOn (curveKf p lam) (Set.Ioc 0 θl) ∧
        StrictAntiOn (curveKf p lam) (Set.Ico θl Real.pi)) ∧
    ∃ θa ∈ Set.Ico 0 (Real.pi / p),
      {θ ∈ Set.Ioo 0 Real.pi | curveKf p lam θ < kConst p lam} =
        Set.Ioo 0 θa ∪ Set.Ioo (Real.pi / p) Real.pi :=
  CstarBelow.Kf_below_of_slope hp1 hp2 hl0 hl1 (slope hp1 hp2 hl0 hl1 hh hloc)

end GKSharp
