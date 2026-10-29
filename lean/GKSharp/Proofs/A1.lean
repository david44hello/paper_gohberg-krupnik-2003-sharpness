/-
A1.lean — consequence (A1) of Lemma A: f_ρ has at most one critical point in (0, π), project 019, Section 5.1.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.CriticalMaximum

namespace GKSharp

open Set Filter Topology

/-- At a critical point with negative second derivative, `f` is strictly smaller just to the right and just to the
left (from the sign of `f'` on both sides). -/
lemma lt_near_of_deriv_deriv_neg {f : ℝ → ℝ} {c : ℝ} {U : Set ℝ} (hU : U ∈ 𝓝 c)
    (hdiff : ∀ x ∈ U, DifferentiableAt ℝ f x) (hd : deriv f c = 0) (hdd : deriv (deriv f) c < 0) :
    (∀ᶠ x in 𝓝[>] c, f x < f c) ∧ (∀ᶠ x in 𝓝[<] c, f x < f c) := by
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg (f := deriv f) hdd hd
  have hsign' : ∀ᶠ x in 𝓝[≠] c, SignType.sign (deriv f x) = SignType.sign (c - x) :=
    nhdsWithin_le_nhds hsign
  have hright := deriv_neg_right_of_sign_deriv hsign'
  have hleft := deriv_pos_left_of_sign_deriv hsign'
  obtain ⟨ε, hε, hUball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨u, hu, hru⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hright
  obtain ⟨l, hl, hll⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hleft
  have hcont : ∀ x ∈ Metric.ball c ε, ContinuousAt f x := fun x hx =>
    (hdiff x (hUball hx)).continuousAt
  constructor
  · have hmem : Ioo c (min u (c + ε)) ∈ 𝓝[>] c :=
      Ioo_mem_nhdsGT (lt_min hu (by linarith))
    filter_upwards [hmem] with x hx
    have hsub : Icc c x ⊆ Metric.ball c ε := by
      intro y hy
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2, hx.2.trans_le (min_le_right _ _)]
    have hanti : StrictAntiOn f (Icc c x) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc c x)
      · exact fun y hy => (hcont y (hsub hy)).continuousWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        exact hru ⟨hy.1, hy.2.trans (hx.2.trans_le (min_le_left _ _))⟩
    exact hanti ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩ hx.1
  · have hmem : Ioo (max l (c - ε)) c ∈ 𝓝[<] c :=
      Ioo_mem_nhdsLT (max_lt hl (by linarith))
    filter_upwards [hmem] with x hx
    have hsub : Icc x c ⊆ Metric.ball c ε := by
      intro y hy
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2, (le_max_right l (c - ε)).trans_lt hx.1]
    have hmono : StrictMonoOn f (Icc x c) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc x c)
      · exact fun y hy => (hcont y (hsub hy)).continuousWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        exact hll ⟨(le_max_left _ _).trans_lt (hx.1.trans hy.1), hy.2⟩
    exact hmono ⟨le_rfl, hx.2.le⟩ ⟨hx.2.le, le_rfl⟩ hx.2

/-- If `f` is differentiable on `(a, b)` and every critical point there has `f'' < 0`, then `f` has at most one
critical point in `(a, b)`: between two of them there would be an interior minimum. -/
theorem subsingleton_critical_of_deriv_deriv_neg {f : ℝ → ℝ} {a b : ℝ}
    (hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hcrit : ∀ x ∈ Ioo a b, deriv f x = 0 → deriv (deriv f) x < 0) :
    Set.Subsingleton {x | x ∈ Ioo a b ∧ deriv f x = 0} := by
  have hloc : ∀ c ∈ Ioo a b, deriv f c = 0 →
      (∀ᶠ x in 𝓝[>] c, f x < f c) ∧ (∀ᶠ x in 𝓝[<] c, f x < f c) := fun c hc hd =>
    lt_near_of_deriv_deriv_neg (Ioo_mem_nhds hc.1 hc.2) hdiff hd (hcrit c hc hd)
  suffices key : ∀ c₁ c₂, c₁ ∈ Ioo a b → deriv f c₁ = 0 → c₂ ∈ Ioo a b → deriv f c₂ = 0 → ¬ c₁ < c₂ by
    intro c₁ h₁ c₂ h₂
    rcases lt_trichotomy c₁ c₂ with hlt | heq | hgt
    · exact absurd hlt (key c₁ c₂ h₁.1 h₁.2 h₂.1 h₂.2)
    · exact heq
    · exact absurd hgt (key c₂ c₁ h₂.1 h₂.2 h₁.1 h₁.2)
  intro c₁ c₂ hc₁ hd₁ hc₂ hd₂ hlt
  have hsub : Icc c₁ c₂ ⊆ Ioo a b := Icc_subset_Ioo hc₁.1 hc₂.2
  have hcontOn : ContinuousOn f (Icc c₁ c₂) := fun x hx =>
    (hdiff x (hsub hx)).continuousAt.continuousWithinAt
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hlt.le) hcontOn
  rcases eq_or_lt_of_le hm.2 with hm2 | hm2
  · -- the minimum sits at `c₂`: `f` is smaller just to the left of `c₂`
    subst hm2
    obtain ⟨x, hx, hxlt⟩ := ((hloc m (hsub hm) hd₂).2.and (Ioo_mem_nhdsLT hlt)).exists
    exact absurd (hmin ⟨hxlt.1.le, hxlt.2.le⟩) (not_le.mpr hx)
  · -- the minimum sits in `[c₁, c₂)`, so it is a critical point: `f` is smaller just to its right
    have hdm : deriv f m = 0 := by
      rcases eq_or_lt_of_le hm.1 with hm1 | hm1
      · rw [← hm1]; exact hd₁
      · exact (hmin.isLocalMin (Icc_mem_nhds hm1 hm2)).deriv_eq_zero
    obtain ⟨x, hx, hxlt⟩ := ((hloc m (hsub hm) hdm).1.and (Ioo_mem_nhdsGT hm2)).exists
    exact absurd (hmin ⟨hm.1.trans hxlt.1.le, hxlt.2.le⟩) (not_le.mpr hx)

/-- (A1), sec5_sharp_inequality.tex l.84-85: "For each ρ > 0, f_ρ has at most one critical point in (0, π)" (by
Lemma A, every critical point is a strict maximum). -/
theorem sec5_A1_proved {p lam ρ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) (hρ : 0 < ρ) :
    Set.Subsingleton {φ | φ ∈ Set.Ioo 0 Real.pi ∧
      deriv (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ = 0} := by
  apply subsingleton_critical_of_deriv_deriv_neg
  · intro x hx
    exact (Proofs.EllipseCalculus.eq_5_3_proved hp1 hp2 hl hl1 hρ hx.1 hx.2).2.2.differentiableAt
  · intro x hx hcrit
    obtain ⟨hdd, hneg⟩ := Proofs.CriticalMaximum.eq_5_6_proved hp1 hp2 hl hl1 hρ hx.1 hx.2 hcrit
    rw [hdd.deriv]
    exact hneg

end GKSharp

