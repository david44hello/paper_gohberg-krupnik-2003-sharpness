/- Lemma B+ scalar and series inputs, frozen sec5d_monotone.tex:74-80 (rows sec5d_lambda_threshold_lt_one,
sec5d_Bplus_first_bracket, sec5d_Bplus_higher_bracket, sec5d_log_series, sec5d_euler_sine_product; types verbatim from
the dM5 ADDED_ROWS v0.10).
Euler product: the logarithms of the factors are summable (|log(1-u)| <= u/(1-u_0), u_n <= C/(n+1)^2), so `HasSum.rexp`
gives an unconditional product; its partial products converge to sin x / x by `Real.tendsto_euler_sin_prod`.
Copyright (C) Dave Goel 2026--now. -/
import Mathlib

namespace GKSharp

open Filter Topology

/-- Row `sec5d_lambda_threshold_lt_one`. -/
theorem sec5d_lambda_threshold_lt_one_proved {lam : ℝ} (hl : -1 < lam) (hl1 : lam < 1) :
    4 * lam / (1 + lam) ^ 2 < 1 := by
  rw [div_lt_one (pow_pos (by linarith) 2)]
  nlinarith [pow_pos (show 0 < 1 - lam by linarith) 2]

/-- Row `sec5d_Bplus_first_bracket`. -/
theorem sec5d_Bplus_first_bracket_proved {eps : ℝ} (he : 2 - Real.sqrt 3 ≤ eps) (he1 : eps < 1) :
    1 + eps ^ 2 - 2 * (1 - eps) ^ 2 = -(eps ^ 2 - 4 * eps + 1) ∧
    0 ≤ 1 + eps ^ 2 - 2 * (1 - eps) ^ 2 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg 3
  refine ⟨by ring, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ 2 + Real.sqrt 3 - eps by linarith)]

/-- Row `sec5d_Bplus_higher_bracket`. -/
theorem sec5d_Bplus_higher_bracket_proved {eps : ℝ} (he : 2 - Real.sqrt 3 ≤ eps) (he1 : eps < 1)
    {k : ℕ} (hk : 2 ≤ k) :
    2 * (1 - eps) ^ (2 * k) ≤ 2 * (4 - 2 * Real.sqrt 3) ^ 2 ∧
    2 * (4 - 2 * Real.sqrt 3) ^ 2 < (58 / 100 : ℝ) := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs1 : (17319 / 10000 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hs2 : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h0 : 0 ≤ 1 - eps := by linarith
  have h1 : 1 - eps ≤ 1 := by linarith
  have hle : 1 - eps ≤ Real.sqrt 3 - 1 := by linarith
  refine ⟨?_, by nlinarith⟩
  have step1 : (1 - eps) ^ (2 * k) ≤ (1 - eps) ^ 4 := pow_le_pow_of_le_one h0 h1 (by omega)
  have step2 : (1 - eps) ^ 4 ≤ (Real.sqrt 3 - 1) ^ 4 := pow_le_pow_left₀ h0 hle 4
  have step3 : (Real.sqrt 3 - 1) ^ 4 = (4 - 2 * Real.sqrt 3) ^ 2 := by
    have e : (Real.sqrt 3 - 1) ^ 2 = 4 - 2 * Real.sqrt 3 := by nlinarith
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e]
  linarith

/-- Row `sec5d_log_series`. -/
theorem sec5d_log_series_proved {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun k : ℕ => u ^ (k + 1) / ((k : ℝ) + 1)) (-Real.log (1 - u)) :=
  Real.hasSum_pow_div_log_of_abs_lt_one (abs_lt.mpr ⟨by linarith, hu1⟩)

/-- Row `sec5d_euler_sine_product`. -/
theorem sec5d_euler_sine_product_proved {x : ℝ} (hx : 0 < x) (hxπ : x < Real.pi) :
    HasProd (fun n : ℕ => 1 - x ^ 2 / (((n : ℝ) + 1) * Real.pi) ^ 2) (Real.sin x / x) := by
  have hπ := Real.pi_pos
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ n, u n = x ^ 2 / (((n : ℝ) + 1) * Real.pi) ^ 2 := ⟨_, fun _ => rfl⟩
  have hu0 : ∀ n, 0 < u n := fun n => by rw [hu]; positivity
  have hu_le : ∀ n, u n ≤ u 0 := fun n => by
    rw [hu, hu]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have hn : ((0 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 := by simp
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hn hπ.le) 2
  have hu01 : u 0 < 1 := by
    rw [hu, div_lt_one (by positivity)]
    simp only [Nat.cast_zero, zero_add, one_mul]
    exact pow_lt_pow_left₀ hxπ hx.le two_ne_zero
  have hlt : ∀ n, u n < 1 := fun n => (hu_le n).trans_lt hu01
  -- the logarithms are summable
  have hs2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hneg : Summable (fun n => -Real.log (1 - u n)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (hs2.mul_left (x ^ 2 / Real.pi ^ 2 / (1 - u 0)))
    · have ha : 0 ≤ 1 - u n := by linarith [hlt n]
      have hb : 1 - u n ≤ 1 := by linarith [hu0 n]
      linarith [Real.log_nonpos ha hb]
    · have h1u : 0 < 1 - u n := by linarith [hlt n]
      have hlog : -Real.log (1 - u n) ≤ 1 / (1 - u n) - 1 := by
        rw [← Real.log_inv, ← one_div]
        exact Real.log_le_sub_one_of_pos (by positivity)
      have hfrac : 1 / (1 - u n) - 1 = u n / (1 - u n) := by rw [div_sub_one h1u.ne', sub_sub_cancel]
      have hden : u n / (1 - u n) ≤ u n / (1 - u 0) :=
        div_le_div_of_nonneg_left (hu0 n).le (by linarith) (by linarith [hu_le n])
      have hun : u n = x ^ 2 / Real.pi ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
        rw [hu, mul_pow, div_mul_div_comm, mul_one, mul_comm (Real.pi ^ 2)]
      calc -Real.log (1 - u n) ≤ u n / (1 - u 0) := by linarith
        _ = x ^ 2 / Real.pi ^ 2 / (1 - u 0) * (1 / ((n : ℝ) + 1) ^ 2) := by
          rw [hun]
          ring
  have hsum : Summable (fun n => Real.log (1 - u n)) := by simpa using hneg.neg
  have hprod := hsum.hasSum.rexp
  have hfac : (Real.exp ∘ fun n => Real.log (1 - u n)) = fun n => 1 - u n :=
    funext fun n => Real.exp_log (by linarith [hlt n])
  rw [hfac] at hprod
  obtain ⟨P, hP⟩ : ∃ P, P = Real.exp (∑' n, Real.log (1 - u n)) := ⟨_, rfl⟩
  rw [← hP] at hprod
  have htend : Tendsto (fun n => x * ∏ j ∈ Finset.range n, (1 - u j)) atTop (𝓝 (x * P)) :=
    hprod.tendsto_prod_nat.const_mul x
  have hxx : Real.pi * (x / Real.pi) = x := by field_simp
  have hlim := Real.tendsto_euler_sin_prod (x / Real.pi)
  have e1 : (fun n : ℕ => Real.pi * (x / Real.pi) *
      ∏ j ∈ Finset.range n, (1 - (x / Real.pi) ^ 2 / ((j : ℝ) + 1) ^ 2)) =
      fun n => x * ∏ j ∈ Finset.range n, (1 - u j) := by
    funext n
    rw [hxx]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by rw [hu, div_pow, mul_pow, div_div, mul_comm (Real.pi ^ 2)]
  rw [e1, hxx] at hlim
  have heq : x * P = Real.sin x := tendsto_nhds_unique htend hlim
  have hP' : P = Real.sin x / x := by rw [← heq]; field_simp
  rw [hP'] at hprod
  convert hprod using 2 with n
  rw [hu]

end GKSharp
