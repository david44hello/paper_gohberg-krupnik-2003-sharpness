/- Theorem C* (sec5e_cstar.tex l.18-19, short v0.70): "Thus Λ ≥ min(Λ(0⁺), 0) and Λ > 0 away from θ₀ unless
Λ(0⁺) < 0", in the case Λ(0⁺) ≥ 0: Λ > 0 on (0, π) \ {θ₀}. No cited input.
Copyright (C) Dave Goel 2026--now.

  The text's step, with its premises explicit: the SHAPE of K_f (strictly decreasing, or strictly increasing on (0, θ_l]
  and strictly decreasing on [θ_l, π), θ_l < θ₀; Lemmas B⁺ and U), the SET {K_f < K} = (0, θ_a) ∪ (θ₀, π) (both = the
  conclusions of sec5e_Kf_below, l.15-17), and Φ(ρ₀) ≥ 0 (sec5e_Lambda_zero, l.19-20).
  (a) K_f > K on (θ_a, θ₀): on a decreasing piece K_f(x) > K_f(θ₀) = K; on the increasing piece K_f(x) > K_f(y) ≥ K for
      y ∈ (θ_a, x) (y is not in the set).
  (b) f(θ) = Φ(w(θ)), f′ = F(K - K_f), F > 0, f(θ₀) = 0 (CstarCurve). θ ∈ (0, θ_a): f′ > 0 on (0, θ], so
      f(θ) > f(θ/2) ≥ lim_{0⁺} f = Φ(ρ₀) ≥ 0. θ ∈ [θ_a, θ₀): f′ < 0 on (θ, θ₀) by (a), f(θ) > f(θ₀) = 0.
      θ ∈ (θ₀, π): f′ > 0 on (θ₀, θ), f(θ) > f(θ₀) = 0. Divide by (1-λ)^p > 0. -/
import GKSharp.Proofs.CstarCurve

open Filter Topology Set

namespace GKSharp

namespace CstarLambdaPos

/-- (a) The shape and the set give `K_f > K` on `(θ_a, θ₀)`. -/
theorem kf_gt_on_gap {p lam θa : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hshape : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) ∨
      ∃ θl ∈ Set.Ioo 0 (Real.pi / p), StrictMonoOn (curveKf p lam) (Set.Ioc 0 θl) ∧
        StrictAntiOn (curveKf p lam) (Set.Ico θl Real.pi))
    (hθa : θa ∈ Set.Ico 0 (Real.pi / p))
    (hS : {θ ∈ Set.Ioo 0 Real.pi | curveKf p lam θ < kConst p lam} = Set.Ioo 0 θa ∪ Set.Ioo (Real.pi / p) Real.pi)
    {x : ℝ} (hx : x ∈ Ioo θa (Real.pi / p)) : kConst p lam < curveKf p lam x := by
  obtain ⟨hθ0, hθπ, -, -⟩ := theta0_bounds hp1 hp2
  have hK : curveKf p lam (Real.pi / p) = kConst p lam := contact_Kf hp1 hp2 hl hl1
  rw [← hK]
  have hx0 : x ∈ Ioo 0 Real.pi := ⟨hθa.1.trans_lt hx.1, hx.2.trans hθπ⟩
  rcases hshape with hdec | ⟨θl, hθl, hinc, hdec⟩
  · exact hdec hx0 ⟨hθ0, hθπ⟩ hx.2
  · rcases le_or_gt θl x with hlx | hxl
    · exact hdec ⟨hlx, hx0.2⟩ ⟨hθl.2.le, hθπ⟩ hx.2
    · -- y ∈ (θ_a, x) is not in {K_f < K}, so K ≤ K_f(y) < K_f(x)
      set y := (θa + x) / 2 with hy
      have hy1 : θa < y := by rw [hy]; linarith [hx.1]
      have hy2 : y < x := by rw [hy]; linarith [hx.1]
      have hy0 : y ∈ Ioo 0 Real.pi := ⟨hθa.1.trans_lt hy1, hy2.trans hx0.2⟩
      have hyK : kConst p lam ≤ curveKf p lam y := by
        refine not_lt.mp fun hlt => ?_
        have hmem : y ∈ {θ ∈ Set.Ioo 0 Real.pi | curveKf p lam θ < kConst p lam} := ⟨hy0, hlt⟩
        rw [hS] at hmem
        rcases hmem with h1 | h1
        · exact absurd h1.2 (not_lt.mpr hy1.le)
        · exact absurd h1.1 (not_lt.mpr (hy2.trans hx.2).le)
      rw [hK]
      exact hyK.trans_lt (hinc ⟨hy0.1, (hy2.trans hxl).le⟩ ⟨hx0.1, hxl.le⟩ hy2)

/-- **sec5e_cstar.tex l.18-19**, the proof step: with the shape and the set of `K_f` (sec5e_Kf_below) and
`Φ(ρ₀) ≥ 0` (sec5e_Lambda_zero), `Λ(θ) = Φ(w(θ))/(1-λ)^p > 0` for every `θ ∈ (0, π)`, `θ ≠ θ₀`. -/
theorem lambda_pos_of_shape {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hshape : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) ∨
      ∃ θl ∈ Set.Ioo 0 (Real.pi / p), StrictMonoOn (curveKf p lam) (Set.Ioc 0 θl) ∧
        StrictAntiOn (curveKf p lam) (Set.Ico θl Real.pi))
    (hset : ∃ θa ∈ Set.Ico 0 (Real.pi / p),
      {θ ∈ Set.Ioo 0 Real.pi | curveKf p lam θ < kConst p lam} = Set.Ioo 0 θa ∪ Set.Ioo (Real.pi / p) Real.pi)
    (h0 : 0 ≤ mobPhi p (gk p lam) (kConst p lam) lam
      ((((1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) : ℝ)) : ℂ)) :
    ∀ θ ∈ Set.Ioo 0 Real.pi, θ ≠ Real.pi / p →
      0 < mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam θ)) / (1 - lam) ^ p := by
  have hl : -1 ≤ lam := by linarith
  obtain ⟨θa, hθa, hS⟩ := hset
  set f : ℝ → ℝ := fun θ => mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam θ)) with hfdef
  obtain ⟨hθ0, hθπ, -, -⟩ := theta0_bounds hp1 hp2
  have hD : ∀ x ∈ Ioo 0 Real.pi, ∃ F : ℝ, 0 < F ∧ HasDerivAt f (F * (kConst p lam - curveKf p lam x)) x :=
    fun x hx => CstarCurve.curve_Phi_hasDerivAt (gk p lam) (kConst p lam) hp1 hp2 hl hl1 hx
  have hcont : ∀ x ∈ Ioo 0 Real.pi, ContinuousAt f x := fun x hx => by
    obtain ⟨F, -, hd⟩ := hD x hx
    exact hd.continuousAt
  have hf0 : f (Real.pi / p) = 0 := CstarCurve.curve_Phi_contact hp1 hp2 hl hl1
  have hpos_d : ∀ x ∈ Ioo 0 Real.pi, curveKf p lam x < kConst p lam → 0 < deriv f x := fun x hx hlt => by
    obtain ⟨F, hF, hd⟩ := hD x hx
    rw [hd.deriv]
    exact mul_pos hF (by linarith)
  have hneg_d : ∀ x ∈ Ioo 0 Real.pi, kConst p lam < curveKf p lam x → deriv f x < 0 := fun x hx hlt => by
    obtain ⟨F, hF, hd⟩ := hD x hx
    rw [hd.deriv]
    exact mul_neg_of_pos_of_neg hF (by linarith)
  have hin : ∀ x ∈ Ioo 0 Real.pi, x ∈ Ioo 0 θa ∪ Ioo (Real.pi / p) Real.pi → curveKf p lam x < kConst p lam :=
    fun x hx h => by
      have hmem : x ∈ Ioo 0 θa ∪ Ioo (Real.pi / p) Real.pi := h
      rw [← hS] at hmem
      exact hmem.2
  intro θ hθ hne
  have hc : 0 < (1 - lam) ^ p := Real.rpow_pos_of_pos (by linarith) p
  refine div_pos ?_ hc
  show 0 < f θ
  rcases lt_or_ge θ θa with hlt | hge
  · -- θ ∈ (0, θ_a)
    have hsub : Ioc 0 θ ⊆ Ioo 0 Real.pi := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    have hmono : StrictMonoOn f (Ioc 0 θ) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioc 0 θ) (fun x hx => (hcont x (hsub hx)).continuousWithinAt)
        (fun x hx => ?_)
      rw [interior_Ioc] at hx
      have hx' := hsub (Ioo_subset_Ioc_self hx)
      exact hpos_d x hx' (hin x hx' (Or.inl ⟨hx.1, hx.2.trans hlt⟩))
    have hh2 : 0 < θ / 2 := half_pos hθ.1
    have hlt2 : θ / 2 < θ := half_lt_self hθ.1
    have hlimf := ((ReductionStep1.mobPhi_continuous (p := p) (by linarith) (gk p lam) (kConst p lam) lam).tendsto
      _).comp (curve_w_tendsto_rho0_proved hp1 hp2 hl hl1)
    have hev : ∀ᶠ x in 𝓝[>] 0, f x ≤ f (θ / 2) := by
      filter_upwards [Ioo_mem_nhdsGT hh2] with x hx
      exact (hmono.monotoneOn) ⟨hx.1, (hx.2.trans hlt2).le⟩ ⟨hh2, hlt2.le⟩ hx.2.le
    have hmid : 0 ≤ f (θ / 2) := h0.trans (le_of_tendsto hlimf hev)
    exact hmid.trans_lt (hmono ⟨hh2, hlt2.le⟩ ⟨hθ.1, le_rfl⟩ hlt2)
  · rcases lt_or_gt_of_ne hne with hlt0 | hgt0
    · -- θ ∈ [θ_a, θ₀)
      have hsub : Icc θ (Real.pi / p) ⊆ Ioo 0 Real.pi := fun x hx => ⟨hθ.1.trans_le hx.1, hx.2.trans_lt hθπ⟩
      have hanti : StrictAntiOn f (Icc θ (Real.pi / p)) := by
        refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (fun x hx => (hcont x (hsub hx)).continuousWithinAt)
          (fun x hx => ?_)
        rw [interior_Icc] at hx
        exact hneg_d x (hsub (Ioo_subset_Icc_self hx))
          (kf_gt_on_gap hp1 hp2 hl hl1 hshape hθa hS ⟨hge.trans_lt hx.1, hx.2⟩)
      have h := hanti ⟨le_rfl, hlt0.le⟩ ⟨hlt0.le, le_rfl⟩ hlt0
      rwa [hf0] at h
    · -- θ ∈ (θ₀, π)
      have hsub : Icc (Real.pi / p) θ ⊆ Ioo 0 Real.pi := fun x hx => ⟨hθ0.trans_le hx.1, hx.2.trans_lt hθ.2⟩
      have hmono : StrictMonoOn f (Icc (Real.pi / p) θ) := by
        refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun x hx => (hcont x (hsub hx)).continuousWithinAt)
          (fun x hx => ?_)
        rw [interior_Icc] at hx
        have hx' := hsub (Ioo_subset_Icc_self hx)
        exact hpos_d x hx' (hin x hx' (Or.inr ⟨hx.1, hx'.2⟩))
      have h := hmono ⟨le_rfl, hgt0.le⟩ ⟨hgt0.le, le_rfl⟩ hgt0
      rwa [hf0] at h

end CstarLambdaPos

end GKSharp
