/- Lemma U coefficient series, frozen sec5d_monotone.tex:99-103 (rows sec5d_sine_square_series,
sec5d_Psi_beta_series; types verbatim from the proposal v020).
Route = the text: sin²(mα) = (1 - cos 2mα)/2 = -(1/2) Σ_(n≥1) a_n tⁿ (t = sin²α); the printed product coefficient
equals -a_(n+1)/2 (same ratio 4((n+1)²-m²)/((2n+3)(2n+4)), same first value m²). Removing the n = 1 term m²t and
dividing by t² gives Ψ_m = Σ β_n tⁿ with β_n = -(printed coefficient at n+2) (the j = 1 factor is 1 - m²).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneUC

namespace GKSharp

namespace USeries

/-- The printed sine-square coefficient at n+2 is the one at n+1 times 4((n+1)²-m²)/((2n+3)(2n+4)). -/
theorem monoSinCoeff_succ (m : ℝ) (n : ℕ) :
    monoSinCoeff m (n + 1 + 1) = monoSinCoeff m (n + 1) *
      (4 * (((n : ℝ) + 1) ^ 2 - m ^ 2) / ((2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 4))) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hf : ((Nat.factorial (2 * (n + 1)) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd : (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 4) ≠ 0 := by positivity
  unfold monoSinCoeff
  rw [show n + 1 + 1 - 1 = n + 1 by omega, Nat.add_sub_cancel, Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1),
    show 2 * (n + 1 + 1) - 1 = (2 * (n + 1) - 1) + 2 by omega, pow_add,
    show 2 * (n + 1 + 1) = 2 * (n + 1) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The printed sine-square coefficient is -a_(n+1)/2. -/
theorem monoSinCoeff_eq (m : ℝ) (n : ℕ) : monoSinCoeff m (n + 1) = -monoCoeffA m (n + 1) / 2 := by
  have hrec := (sec5d_coefficient_recurrence_proved m)
  induction n with
  | zero =>
    rw [hrec.2 0, hrec.1]
    unfold monoSinCoeff
    rw [show Finset.Icc 1 (0 + 1 - 1) = (∅ : Finset ℕ) by decide, Finset.prod_empty]
    norm_num [Nat.factorial]
    ring
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hd1 : ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 1 / 2) ≠ 0 := by positivity
    have hd2 : (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 4) ≠ 0 := by positivity
    rw [monoSinCoeff_succ, ih, hrec.2 (n + 1)]
    push_cast
    field_simp
    ring

/-- β_n is minus the printed sine-square coefficient at n+2. -/
theorem monoBeta_eq (m : ℝ) (n : ℕ) : monoBeta m n = -monoSinCoeff m (n + 1 + 1) := by
  have hI : Finset.Icc 1 (n + 1) = insert 1 (Finset.Icc 2 (n + 1)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  unfold monoBeta monoSinCoeff
  rw [show n + 1 + 1 - 1 = n + 1 by omega, show 2 * (n + 1 + 1) - 1 = 2 * n + 3 by omega,
    show 2 * (n + 1 + 1) = 2 * n + 4 by ring, hI, Finset.prod_insert (by simp)]
  push_cast
  ring

end USeries

open USeries

/-- Row `sec5d_sine_square_series`. -/
theorem sec5d_sine_square_series_proved (m : ℝ) {α : ℝ} (hα : 0 < α) (hαπ : α < Real.pi / 2) :
    HasSum (fun n : ℕ => monoSinCoeff m (n + 1) * (Real.sin α ^ 2) ^ (n + 1))
      (Real.sin (m * α) ^ 2) := by
  have hpi := Real.pi_pos
  have hs := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith, hαπ⟩
  have ht0 : 0 ≤ Real.sin α ^ 2 := sq_nonneg _
  have ht1 : Real.sin α ^ 2 < 1 := by nlinarith [Real.sin_sq_add_cos_sq α, mul_pos hc hc]
  have hY := sec5d_Y_series_proved m ht0 ht1
  rw [sec5d_Y_coordinate_proved m hα hαπ] at hY
  -- drop the n = 0 term a_0 = 1
  have hY1 := (hasSum_nat_add_iff' 1).mpr hY
  simp only [Finset.range_one, Finset.sum_singleton, (sec5d_coefficient_recurrence_proved m).1, pow_zero,
    mul_one] at hY1
  have hval : Real.sin (m * α) ^ 2 = -(1 / 2) * (Real.cos (2 * m * α) - 1) := by
    rw [show 2 * m * α = 2 * (m * α) by ring, Real.cos_two_mul]
    linear_combination Real.sin_sq_add_cos_sq (m * α)
  rw [hval]
  convert hY1.mul_left (-(1 / 2)) using 1
  funext n
  rw [monoSinCoeff_eq]
  ring

/-- Row `sec5d_Psi_beta_series`. -/
theorem sec5d_Psi_beta_series_proved {m α : ℝ} (hm : 1 < m) (hm2 : m < 2)
    (hα : 0 < α) (hαπ : α < Real.pi / 2) :
    HasSum (fun n : ℕ => monoBeta m n * (Real.sin α ^ 2) ^ n) (monoPsi m α) := by
  have hpi := Real.pi_pos
  have hs := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have ht : 0 < Real.sin α ^ 2 := by positivity
  have hs' : Real.sin α ≠ 0 := hs.ne'
  have h := sec5d_sine_square_series_proved m hα hαπ
  -- drop the n = 0 term (coefficient m², power t)
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  have hc1 : monoSinCoeff m 1 = m ^ 2 := by
    rw [monoSinCoeff_eq, (sec5d_coefficient_recurrence_proved m).2 0, (sec5d_coefficient_recurrence_proved m).1]
    push_cast
    ring
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, hc1, pow_one] at h1
  have h2 := h1.mul_left (-(1 / (Real.sin α ^ 2) ^ 2))
  convert h2 using 1
  · funext n
    rw [monoBeta_eq]
    field_simp
    ring
  · rw [monoPsi]
    field_simp
    ring

end GKSharp

