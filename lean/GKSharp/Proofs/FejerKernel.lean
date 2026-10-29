/- the Fejér kernel F_N(x) = Σ_{|n| ≤ N} (1 - |n|/(N+1)) cos(n x) (the weights of fejerMean, O23):
F_N ≥ 0, F_N ≤ N + 1, F_N(x) ≤ π²/((N+1) x²) for 0 < |x| ≤ π, ∫_{-π}^{π} F_N = 2π, F_N even and 2π-periodic.
No cited input.
Copyright (C) Dave Goel 2026--now.

  G_N = (N+1) F_N = Σ (N+1-|n|) cos(n x) and the Dirichlet sum D_N = Σ_{|n| ≤ N} cos(n x) satisfy
  D_{N+1} = D_N + 2 cos((N+1)x), G_{N+1} = G_N + D_{N+1}, D_N (1 - cos x) = cos(N x) - cos((N+1)x), hence
  G_N (1 - cos x) = 1 - cos((N+1)x). Where cos x = 1 every cos(n x) = 1 and G_N = G_N(0) = (N+1)² ≥ 0; elsewhere
  G_N = (1 - cos((N+1)x))/(1 - cos x) ∈ [0, 2/(1 - cos x)], and 1 - cos x = 2 sin²(x/2) ≥ 2x²/π² (Jordan). -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace GKSharp

namespace Fejer

open Real Finset

/-- `G_N(x) = Σ_{|n| ≤ N} (N + 1 - |n|) cos(n x)`. -/
noncomputable def kerG (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), ((N : ℝ) + 1 - (n.natAbs : ℝ)) * cos (n * x)

/-- The Dirichlet sum `D_N(x) = Σ_{|n| ≤ N} cos(n x)`. -/
noncomputable def kerD (N : ℕ) (x : ℝ) : ℝ := ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), cos (n * x)

/-- The Fejér kernel `F_N(x) = Σ_{|n| ≤ N} (1 - |n|/(N+1)) cos(n x)`. -/
noncomputable def kerF (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), (1 - (n.natAbs : ℝ) / (N + 1)) * cos (n * x)

lemma Icc_succ_eq (N : ℕ) : Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
    insert ((N : ℤ) + 1) (insert (-((N : ℤ) + 1)) (Icc (-(N : ℤ)) (N : ℤ))) := by
  ext n
  simp only [mem_Icc, mem_insert]
  omega

lemma sum_Icc_succ (f : ℤ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ), f n =
      ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), f n + f ((N : ℤ) + 1) + f (-((N : ℤ) + 1)) := by
  rw [Icc_succ_eq, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
    sum_insert (by simp only [mem_Icc]; omega)]
  ring

lemma natAbs_cast_le {N : ℕ} {n : ℤ} (hn : n ∈ Icc (-(N : ℤ)) (N : ℤ)) : (n.natAbs : ℝ) ≤ N := by
  rw [mem_Icc] at hn
  exact_mod_cast (by omega : n.natAbs ≤ N)

lemma kerD_succ (N : ℕ) (x : ℝ) : kerD (N + 1) x = kerD N x + 2 * cos ((N + 1) * x) := by
  simp only [kerD]
  rw [sum_Icc_succ]
  push_cast
  rw [show (-((N : ℝ) + 1)) * x = -(((N : ℝ) + 1) * x) by ring, cos_neg]
  ring

lemma kerG_succ (N : ℕ) (x : ℝ) : kerG (N + 1) x = kerG N x + kerD (N + 1) x := by
  rw [kerD_succ]
  simp only [kerG, kerD]
  rw [sum_Icc_succ]
  have h1 : ((N : ℤ) + 1).natAbs = N + 1 := by omega
  have h2 : (-((N : ℤ) + 1)).natAbs = N + 1 := by omega
  rw [h1, h2]
  push_cast
  rw [show (-((N : ℝ) + 1)) * x = -(((N : ℝ) + 1) * x) by ring, cos_neg]
  have hsum : ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), ((N : ℝ) + 1 + 1 - (n.natAbs : ℝ)) * cos (n * x) =
      ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), ((N : ℝ) + 1 - (n.natAbs : ℝ)) * cos (n * x) +
        ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), cos (n * x) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hsum]
  ring

lemma two_cos_mul_cos (a b : ℝ) : 2 * cos a * cos b = cos (a + b) + cos (a - b) := by
  rw [cos_add, cos_sub]
  ring

lemma kerD_mul (N : ℕ) (x : ℝ) : kerD N x * (1 - cos x) = cos (N * x) - cos ((N + 1) * x) := by
  induction N with
  | zero => simp [kerD]
  | succ N ih =>
    rw [kerD_succ, add_mul, ih]
    push_cast
    have h := two_cos_mul_cos (((N : ℝ) + 1) * x) x
    rw [show ((N : ℝ) + 1) * x + x = ((N : ℝ) + 1 + 1) * x by ring,
      show ((N : ℝ) + 1) * x - x = (N : ℝ) * x by ring] at h
    linear_combination -h

lemma kerG_mul (N : ℕ) (x : ℝ) : kerG N x * (1 - cos x) = 1 - cos ((N + 1) * x) := by
  induction N with
  | zero => simp [kerG]
  | succ N ih =>
    rw [kerG_succ, add_mul, ih, kerD_mul]
    push_cast
    ring

lemma kerD_at_zero (N : ℕ) : kerD N 0 = 2 * N + 1 := by
  induction N with
  | zero => simp [kerD]
  | succ N ih => rw [kerD_succ, ih]; push_cast; simp; ring

lemma kerG_at_zero (N : ℕ) : kerG N 0 = ((N : ℝ) + 1) ^ 2 := by
  induction N with
  | zero => simp [kerG]
  | succ N ih => rw [kerG_succ, ih, kerD_at_zero]; push_cast; ring

lemma weight_nonneg {N : ℕ} {n : ℤ} (hn : n ∈ Icc (-(N : ℤ)) (N : ℤ)) : 0 ≤ (N : ℝ) + 1 - (n.natAbs : ℝ) := by
  have := natAbs_cast_le hn
  linarith

lemma kerG_le_at_zero (N : ℕ) (x : ℝ) : kerG N x ≤ ((N : ℝ) + 1) ^ 2 := by
  rw [← kerG_at_zero]
  simp only [kerG, mul_zero, cos_zero, mul_one]
  exact sum_le_sum fun n hn => mul_le_of_le_one_right (weight_nonneg hn) (cos_le_one _)

lemma kerG_nonneg (N : ℕ) (x : ℝ) : 0 ≤ kerG N x := by
  by_cases hx : cos x = 1
  · obtain ⟨m, hm⟩ := (cos_eq_one_iff x).1 hx
    have hall : ∀ n : ℤ, cos (n * x) = 1 := fun n => by
      rw [← hm, show (n : ℝ) * (m * (2 * π)) = ((n * m : ℤ) : ℝ) * (2 * π) by push_cast; ring]
      exact (cos_eq_one_iff _).2 ⟨n * m, rfl⟩
    have h0 : kerG N x = kerG N 0 := by simp only [kerG, hall, mul_zero, cos_zero]
    rw [h0, kerG_at_zero]
    positivity
  · have hpos : 0 < 1 - cos x := by
      have := cos_le_one x
      have : cos x < 1 := lt_of_le_of_ne this hx
      linarith
    have h := kerG_mul N x
    have hnum : 0 ≤ 1 - cos ((N + 1) * x) := by linarith [cos_le_one ((N + 1) * x)]
    exact le_of_mul_le_mul_right (by rw [zero_mul, h]; exact hnum) hpos

/-- `1 - cos x ≥ 2 x²/π²` for `|x| ≤ π` (Jordan's inequality at `|x|/2`). -/
lemma one_sub_cos_ge {x : ℝ} (hx : |x| ≤ π) : 2 * x ^ 2 / π ^ 2 ≤ 1 - cos x := by
  have hhalf : cos x = 1 - 2 * sin (|x| / 2) ^ 2 := by
    have h2 : cos x = cos (2 * (|x| / 2)) := by rw [show 2 * (|x| / 2) = |x| by ring, cos_abs]
    rw [h2, cos_two_mul, cos_sq']
    ring
  have hj := mul_le_sin (by positivity : 0 ≤ |x| / 2) (by linarith : |x| / 2 ≤ π / 2)
  have hj' : |x| / π ≤ sin (|x| / 2) := by
    calc |x| / π = 2 / π * (|x| / 2) := by field_simp
      _ ≤ sin (|x| / 2) := hj
  have hsq : (|x| / π) ^ 2 ≤ sin (|x| / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hj' 2
  rw [div_pow, sq_abs] at hsq
  rw [hhalf]
  have hπ : 0 < π ^ 2 := by positivity
  calc 2 * x ^ 2 / π ^ 2 = 2 * (x ^ 2 / π ^ 2) := by ring
    _ ≤ 2 * sin (|x| / 2) ^ 2 := by linarith
    _ = 1 - (1 - 2 * sin (|x| / 2) ^ 2) := by ring

lemma kerG_le_tail (N : ℕ) {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ π) : kerG N x ≤ π ^ 2 / x ^ 2 := by
  have hJ := one_sub_cos_ge hx
  have hx2 : 0 < x ^ 2 := by positivity
  have hpos : 0 < 1 - cos x := lt_of_lt_of_le (by positivity) hJ
  have h := kerG_mul N x
  have hnum : 1 - cos ((N + 1) * x) ≤ 2 := by linarith [neg_one_le_cos ((N + 1) * x)]
  have hG : kerG N x ≤ 2 / (1 - cos x) := by
    rw [le_div_iff₀ hpos]
    linarith
  calc kerG N x ≤ 2 / (1 - cos x) := hG
    _ ≤ 2 / (2 * x ^ 2 / π ^ 2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hJ
    _ = π ^ 2 / x ^ 2 := by field_simp

lemma kerF_eq (N : ℕ) (x : ℝ) : kerF N x = kerG N x / ((N : ℝ) + 1) := by
  simp only [kerF, kerG, sum_div]
  refine sum_congr rfl fun n _ => ?_
  field_simp

lemma kerF_nonneg (N : ℕ) (x : ℝ) : 0 ≤ kerF N x := by
  rw [kerF_eq]
  exact div_nonneg (kerG_nonneg N x) (by positivity)

lemma kerF_le (N : ℕ) (x : ℝ) : kerF N x ≤ (N : ℝ) + 1 := by
  rw [kerF_eq, div_le_iff₀ (by positivity)]
  nlinarith [kerG_le_at_zero N x]

lemma kerF_le_tail (N : ℕ) {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ π) :
    kerF N x ≤ π ^ 2 / (((N : ℝ) + 1) * x ^ 2) := by
  rw [kerF_eq, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right (kerG_le_tail N hx0 hx) (by positivity)

lemma kerF_periodic (N : ℕ) : Function.Periodic (kerF N) (2 * π) := by
  intro x
  simp only [kerF]
  refine sum_congr rfl fun n _ => ?_
  rw [show (n : ℝ) * (x + 2 * π) = (n : ℝ) * x + (n : ℤ) * (2 * π) by ring, cos_add_int_mul_two_pi]

lemma kerF_neg (N : ℕ) (x : ℝ) : kerF N (-x) = kerF N x := by
  simp only [kerF]
  refine sum_congr rfl fun n _ => ?_
  rw [mul_neg, cos_neg]

lemma continuous_kerF (N : ℕ) : Continuous (kerF N) := by
  unfold kerF
  fun_prop

/-- `∫_{-π}^{π} cos(n x) dx = 0` for `n ≠ 0`. -/
lemma integral_cos_int_mul {n : ℤ} (hn : n ≠ 0) : ∫ x in (-π)..π, cos (n * x) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [intervalIntegral.integral_comp_mul_left (fun x => cos x) hn', integral_cos]
  rw [show (n : ℝ) * π = n * π by ring, show (n : ℝ) * -π = -(n * π) by ring, sin_neg, sin_int_mul_pi]
  simp

lemma integral_kerF (N : ℕ) : ∫ x in (-π)..π, kerF N x = 2 * π := by
  simp only [kerF]
  rw [intervalIntegral.integral_finsetSum fun (n : ℤ) _ => (by fun_prop : Continuous fun x : ℝ =>
    (1 - (n.natAbs : ℝ) / (N + 1)) * cos (n * x)).intervalIntegrable _ _]
  rw [sum_eq_single (0 : ℤ)]
  · simp
    ring
  · intro n _ hn
    rw [intervalIntegral.integral_const_mul, integral_cos_int_mul hn, mul_zero]
  · intro h
    exact absurd (mem_Icc.2 ⟨by omega, by omega⟩) h

end Fejer

end GKSharp
