/- O23 part 1 (sec2_obstacle.tex l.81-82, short v0.40): for every ε > 0 a bounded, measurable,
2π-periodic u with Γ(u(t), t) < m_C(t) + ε for EVERY t. No cited input.
Copyright (C) Dave Goel 2026--now.

  Minimizers of y ↦ Γ(y, t) lie in a fixed [-Y, Y] (exists_obstacle_min_compact). Γ and m_C are uniformly continuous
  on [0, 2π] × [-(Y+1), Y+1] (box_uc), with modulus δ for ε/2. Take M cells per period with 2π/M < δ, and let u(t) be a
  minimizer at the left end s of t's cell (cell index ⌊t M/2π⌋ mod M). Then t - 2πk ∈ [s, s + 2π/M) for some k ∈ ℤ, so
  Γ(u t, t) = Γ(y*, t - 2πk) < Γ(y*, s) + ε/2 = m_C(s) + ε/2 < m_C(t - 2πk) + ε = m_C(t) + ε.
  u factors through an integer, so it is measurable; the index is 2π-periodic. -/
import GKSharp.Proofs.ObstacleMinimum
import GKSharp.Proofs.Gamma
import GKSharp.Proofs.Select
import Mathlib.MeasureTheory.Function.Floor

namespace GKSharp

namespace NearMinSelect

open Real Set

/-- The cell index of `t` for `M` cells per period: `⌊t M / 2π⌋ mod M`. -/
noncomputable def cell (M : ℕ) (t : ℝ) : ℤ := ⌊t * M / (2 * π)⌋ % (M : ℤ)

lemma cell_periodic (M : ℕ) : Function.Periodic (cell M) (2 * π) := by
  intro t
  have h : (t + 2 * π) * M / (2 * π) = t * M / (2 * π) + (M : ℝ) := by
    field_simp
  simp only [cell, h, Int.floor_add_natCast, Int.add_emod_right]

lemma cell_nonneg {M : ℕ} (hM : 0 < M) (t : ℝ) : 0 ≤ cell M t :=
  Int.emod_nonneg _ (by exact_mod_cast hM.ne')

lemma cell_lt {M : ℕ} (hM : 0 < M) (t : ℝ) : cell M t < M :=
  Int.emod_lt_of_pos _ (by exact_mod_cast hM)

/-- `t` shifted by a whole number of periods lies in its cell `[s, s + 2π/M)`, `s = 2π cell / M`. -/
lemma exists_shift_mem_cell {M : ℕ} (hM : 0 < M) (t : ℝ) :
    ∃ k : ℤ, 2 * π * cell M t / M ≤ t - k * (2 * π) ∧ t - k * (2 * π) < 2 * π * cell M t / M + 2 * π / M := by
  set j := ⌊t * M / (2 * π)⌋ with hj
  refine ⟨j / M, ?_, ?_⟩
  all_goals
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hπ : 0 < 2 * π := by positivity
    have hdiv : (j : ℝ) = M * ((j / M : ℤ) : ℝ) + (cell M t : ℝ) := by
      have := Int.mul_ediv_add_emod j M
      simp only [cell, ← hj]
      exact_mod_cast this.symm
    have h1 := Int.floor_le (t * M / (2 * π))
    have h2 := Int.lt_floor_add_one (t * M / (2 * π))
    rw [← hj] at h1 h2
    rw [hdiv] at h1 h2
  · rw [div_le_iff₀ hMpos]
    rw [le_div_iff₀ hπ] at h1
    nlinarith
  · rw [← add_div, lt_div_iff₀ hMpos]
    rw [div_lt_iff₀ hπ] at h2
    nlinarith

lemma shift_mem_Icc {M : ℕ} (hM : 0 < M) {t s : ℝ} (hs : s = 2 * π * cell M t / M) {k : ℤ}
    (h1 : s ≤ t - k * (2 * π)) (h2 : t - k * (2 * π) < s + 2 * π / M) :
    s ∈ Icc (0 : ℝ) (2 * π) ∧ t - k * (2 * π) ∈ Icc (0 : ℝ) (2 * π) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hc0 : (0 : ℝ) ≤ cell M t := by exact_mod_cast cell_nonneg hM t
  have hc1 : (cell M t : ℝ) + 1 ≤ M := by exact_mod_cast cell_lt hM t
  have hs0 : 0 ≤ s := by rw [hs]; exact div_nonneg (mul_nonneg (by positivity) hc0) hMpos.le
  have hs1 : s + 2 * π / M ≤ 2 * π := by
    rw [hs, ← add_div, div_le_iff₀ hMpos]
    nlinarith [pi_pos]
  exact ⟨⟨hs0, by linarith [div_pos (by positivity : (0:ℝ) < 2 * π) hMpos]⟩, ⟨by linarith, by linarith⟩⟩

/-- The grid selector: the chosen point `ystar s` at the left end `s` of `t`'s cell. -/
noncomputable def selector (ystar : ℝ → ℝ) (M : ℕ) (t : ℝ) : ℝ := ystar (2 * π * cell M t / M)

lemma selector_measurable (ystar : ℝ → ℝ) (M : ℕ) : Measurable (selector ystar M) := by
  have hcell : Measurable (cell M) :=
    (Measurable.of_discrete (f := fun j : ℤ => j % (M : ℤ))).comp (Measurable.floor (by fun_prop))
  exact (Measurable.of_discrete (f := fun r : ℤ => ystar (2 * π * r / M))).comp hcell

lemma selector_periodic (ystar : ℝ → ℝ) (M : ℕ) : Function.Periodic (selector ystar M) (2 * π) := by
  intro t
  simp only [selector, cell_periodic M t]

/-- The abstract step: periodic `G y`, `m`, uniform moduli `δ` for `ε/2`, a grid finer than `δ`, and exact
minimizers `ystar` give a pointwise `ε`-near-minimizer. -/
lemma selector_near {G : ℝ → ℝ → ℝ} {m ystar : ℝ → ℝ} {Y ε δ : ℝ} {M : ℕ} (hM : 0 < M)
    (hGper : ∀ y, Function.Periodic (G y) (2 * π)) (hmper : Function.Periodic m (2 * π))
    (hyIcc : ∀ s, ystar s ∈ Icc (-Y) Y) (hyEq : ∀ s, m s = G (ystar s) s)
    (hUG : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ θ' ∈ Icc (0 : ℝ) (2 * π), ∀ y ∈ Icc (-Y) Y, |θ - θ'| < δ →
      |G y θ - G y θ'| < ε / 2)
    (hUm : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ θ' ∈ Icc (0 : ℝ) (2 * π), |θ - θ'| < δ → |m θ - m θ'| < ε / 2)
    (hstep : 2 * π / M < δ) (t : ℝ) : G (selector ystar M t) t < m t + ε := by
  obtain ⟨k, hk1, hk2⟩ := exists_shift_mem_cell hM t
  obtain ⟨hsI, ht'I⟩ := shift_mem_Icc hM rfl hk1 hk2
  have hdist : |t - k * (2 * π) - 2 * π * cell M t / M| < δ := by
    rw [abs_lt]; constructor <;> linarith
  have hγ := hUG _ ht'I _ hsI _ (hyIcc (2 * π * cell M t / M)) hdist
  have hm := hUm _ hsI _ ht'I (by rw [abs_sub_comm]; exact hdist)
  have hper_g : G (selector ystar M t) t = G (ystar (2 * π * cell M t / M)) (t - k * (2 * π)) :=
    ((hGper _).sub_int_mul_eq k).symm
  rw [hper_g, ← (hmper.sub_int_mul_eq k)]
  have hEq := hyEq (2 * π * cell M t / M)
  rw [abs_lt] at hγ hm
  linarith [hγ.1, hγ.2, hm.1, hm.2]

/-- A grid finer than any `δ > 0`. -/
lemma exists_fine_grid {δ : ℝ} (hδ : 0 < δ) : ∃ M : ℕ, 0 < M ∧ 2 * π / M < δ := by
  refine ⟨⌈2 * π / δ⌉₊ + 1, Nat.succ_pos _, ?_⟩
  have hc := Nat.le_ceil (2 * π / δ)
  rw [div_le_iff₀ hδ] at hc
  have hMpos : (0 : ℝ) < ((⌈2 * π / δ⌉₊ + 1 : ℕ) : ℝ) := by positivity
  rw [div_lt_iff₀ hMpos, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- O23 part 1: a bounded, measurable, 2π-periodic pointwise ε-near-minimizer of the angular obstacle. -/
theorem exists_near_min {p : ℝ} (hp : 1 < p) (C : ℝ) (ρ : ℂ) (hC : max 1 ‖ρ‖ < C) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Y : ℝ) (u : ℝ → ℝ), 0 ≤ Y ∧ Measurable u ∧ Function.Periodic u (2 * Real.pi) ∧ (∀ t, |u t| ≤ Y) ∧
      (∀ t, gamma p C ρ (u t) t < obstacle p C ρ t + ε) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Y, hY0, hY⟩ := exists_obstacle_min_compact hp0 ρ hC
  choose ystar hyIcc hyMin hyEq using hY
  clear hyMin
  have hcγ : Continuous (Function.uncurry fun θ v => gamma p C ρ v θ) :=
    Continuous.comp (g := fun x : ℝ × ℝ => gamma p C ρ x.1 x.2) (f := Prod.swap)
      (continuous_gamma hp0 C ρ) continuous_swap
  have hcm : Continuous (Function.uncurry fun θ (_ : ℝ) => obstacle p C ρ θ) :=
    Continuous.comp (g := obstacle p C ρ) (f := Prod.fst) (obstacle_continuous hp0 ρ hC) continuous_fst
  obtain ⟨δ1, hδ1, hUγ⟩ := box_uc _ hcγ Y (ε / 2) (by positivity)
  obtain ⟨δ2, hδ2, hUm⟩ := box_uc _ hcm Y (ε / 2) (by positivity)
  obtain ⟨M, hM, hstep⟩ := exists_fine_grid (lt_min hδ1 hδ2)
  have hwide : ∀ y ∈ Icc (-Y) Y, y ∈ Icc (-(Y + 1)) (Y + 1) := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h0 : (0 : ℝ) ∈ Icc (-(Y + 1)) (Y + 1) := ⟨by linarith, by linarith⟩
  have hUG : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ θ' ∈ Icc (0 : ℝ) (2 * π), ∀ y ∈ Icc (-Y) Y,
      |θ - θ'| < min δ1 δ2 → |gamma p C ρ y θ - gamma p C ρ y θ'| < ε / 2 := by
    intro θ hθ θ' hθ' y hy hd
    have h := hUγ θ hθ θ' hθ' y (hwide y hy) y (hwide y hy) (hd.trans_le (min_le_left _ _)) (by simpa using hδ1)
    simpa using h
  have hUM : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ θ' ∈ Icc (0 : ℝ) (2 * π),
      |θ - θ'| < min δ1 δ2 → |obstacle p C ρ θ - obstacle p C ρ θ'| < ε / 2 := by
    intro θ hθ θ' hθ' hd
    have h := hUm θ hθ θ' hθ' 0 h0 0 h0 (hd.trans_le (min_le_right _ _)) (by simpa using hδ2)
    simpa using h
  have hnear : ∀ t, gamma p C ρ (selector ystar M t) t < obstacle p C ρ t + ε :=
    selector_near (G := gamma p C ρ) hM (gamma_periodic p C ρ) (obstacle_periodic p C ρ) hyIcc hyEq hUG hUM hstep
  have hbd : ∀ t, |selector ystar M t| ≤ Y := fun t => abs_le.2 (hyIcc _)
  exact ⟨Y, selector ystar M, hY0.le, selector_measurable ystar M, selector_periodic ystar M, hbd, hnear⟩

end NearMinSelect

end GKSharp
