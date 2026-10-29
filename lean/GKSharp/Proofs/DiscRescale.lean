/-
GKSharp/Proofs/DiscRescale.lean — paper 019 support lemma for the polynomial-disc (lift) route: a generic radial
rescaling. For continuous `M : ℂ → ℝ` with `M 0 = 0` and a complex polynomial `g` with
`∫₀^{2π} M(g(e^{iθ})) dθ < 0`, some `r ∈ (0,1)` puts no root of `g` on the circle `|z| = r` and keeps the integral
over that circle negative. A support lemma only — not a proof of any printed Blaschke/sqrt or Fejér claim.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Route: `r ↦ ∫ M(g(r e^{iθ}))` is continuous (parametric interval integral), so negative on `(1-δ, 1]`; `g ≠ 0`
(else the integral is `0`); the finitely many roots of modulus `< 1` have a largest modulus `ρ₁ < 1`; take `r`
strictly between `max(ρ₁, 1 - δ/2)` and `1`.
-/
import GKSharp.Defs.Potential

open Real Set Filter Topology

namespace GKSharp

namespace DiscRescale

lemma norm_unitPoint' (t : ℝ) : ‖unitPoint t‖ = 1 := by
  unfold unitPoint
  exact Complex.norm_exp_ofReal_mul_I t

lemma continuous_unitPoint' : Continuous unitPoint := by
  unfold unitPoint
  fun_prop

end DiscRescale

/-- Generic disc rescaling: a negative boundary integral survives on a slightly smaller circle that avoids every
root of `g`. -/
theorem disc_rescale (M : ℂ → ℝ) (hM : Continuous M) (hM0 : M 0 = 0) (g : Polynomial ℂ)
    (hneg : ∫ θ in (0 : ℝ)..(2 * π), M (g.eval (unitPoint θ)) < 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ (∀ θ : ℝ, g.eval ((r : ℂ) * unitPoint θ) ≠ 0) ∧
      ∫ θ in (0 : ℝ)..(2 * π), M (g.eval ((r : ℂ) * unitPoint θ)) < 0 := by
  obtain ⟨Φ, hΦ⟩ : ∃ f : ℝ → ℝ, f = fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * π), M (g.eval ((r : ℂ) * unitPoint θ)) :=
    ⟨_, rfl⟩
  have hΦc : Continuous Φ := by
    rw [hΦ]
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hM.comp ((Polynomial.continuous g).comp ((Complex.continuous_ofReal.comp continuous_fst).mul
      (DiscRescale.continuous_unitPoint'.comp continuous_snd)))
  have hΦ1 : Φ 1 < 0 := by simpa [hΦ] using hneg
  obtain ⟨δ, hδ, hδΦ⟩ := Metric.eventually_nhds_iff.mp ((hΦc.tendsto 1).eventually (gt_mem_nhds hΦ1))
  have hg : g ≠ 0 := by
    rintro rfl
    simp [hM0] at hneg
  -- the largest modulus `ρ₁ < 1` among the roots inside the unit disc
  obtain ⟨ρ1, hρ1, hρ1b, hbound⟩ : ∃ ρ1 : ℝ, 0 ≤ ρ1 ∧ ρ1 < 1 ∧ ∀ z ∈ g.roots, ‖z‖ < 1 → ‖z‖ ≤ ρ1 := by
    by_cases hS : (g.roots.toFinset.filter fun z => ‖z‖ < 1).Nonempty
    · obtain ⟨z0, hz0, hmax⟩ := Finset.exists_max_image _ (fun z : ℂ => ‖z‖) hS
      exact ⟨‖z0‖, norm_nonneg _, (Finset.mem_filter.mp hz0).2, fun z hz hz1 =>
        hmax z (Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hz, hz1⟩)⟩
    · exact ⟨0, le_refl _, one_pos, fun z hz hz1 =>
        absurd ⟨z, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hz, hz1⟩⟩ hS⟩
  obtain ⟨r, hr⟩ : ∃ x : ℝ, x = (max ρ1 (1 - δ / 2) + 1) / 2 := ⟨_, rfl⟩
  have hmax1 : max ρ1 (1 - δ / 2) < 1 := max_lt hρ1b (by linarith)
  have hm1 := le_max_left ρ1 (1 - δ / 2)
  have hm2 := le_max_right ρ1 (1 - δ / 2)
  have hrpos : 0 < r := by rw [hr]; linarith
  have hρr : ρ1 < r := by rw [hr]; linarith
  have hrlt : r < 1 := by rw [hr]; linarith
  have hdist : dist r 1 < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> rw [hr] <;> linarith
  refine ⟨r, hrpos, hrlt, fun θ h0 => ?_, ?_⟩
  · have hmem : (r : ℂ) * unitPoint θ ∈ g.roots := (Polynomial.mem_roots hg).mpr h0
    have hn : ‖(r : ℂ) * unitPoint θ‖ = r := by
      rw [norm_mul, DiscRescale.norm_unitPoint', mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    have hle := hbound _ hmem (by rw [hn]; exact hrlt)
    rw [hn] at hle
    linarith
  · have := hδΦ hdist
    rw [hΦ] at this
    exact this

end GKSharp
