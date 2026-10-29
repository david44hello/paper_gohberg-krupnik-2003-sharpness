/- Lemma U elementary inputs, frozen sec5d_monotone.tex:89-108 (rows sec5d_t_derivatives,
sec5d_coefficient_recurrence, sec5d_beta_positive, sec5d_sin_square_strictMono, sec5d_U_endpoint; types verbatim from
the proposal v020).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.MonotonicityCurve
import GKSharp.Proofs.MonotoneBplusA

namespace GKSharp

/-- Row `sec5d_t_derivatives`. -/
theorem sec5d_t_derivatives_proved (α : ℝ) :
    HasDerivAt (fun x => Real.sin x ^ 2) (2 * Real.sin α * Real.cos α) α ∧
    (2 * Real.sin α * Real.cos α) ^ 2 = 4 * Real.sin α ^ 2 * (1 - Real.sin α ^ 2) ∧
    deriv (deriv fun x => Real.sin x ^ 2) α = 2 - 4 * Real.sin α ^ 2 := by
  have h1 : ∀ x : ℝ, HasDerivAt (fun x => Real.sin x ^ 2) (2 * Real.sin x * Real.cos x) x := fun x => by
    convert (Real.hasDerivAt_sin x).pow 2 using 1
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have hd : deriv (fun x => Real.sin x ^ 2) = fun x => 2 * Real.sin x * Real.cos x :=
    funext fun x => (h1 x).deriv
  have h2 : HasDerivAt (fun x => 2 * Real.sin x * Real.cos x)
      (2 * (Real.cos α * Real.cos α + Real.sin α * -Real.sin α)) α := by
    convert ((Real.hasDerivAt_sin α).mul (Real.hasDerivAt_cos α)).const_mul 2 using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  refine ⟨h1 α, by linear_combination (4 * Real.sin α ^ 2) * Real.sin_sq_add_cos_sq α, ?_⟩
  rw [hd, h2.deriv]
  linear_combination 2 * Real.sin_sq_add_cos_sq α

/-- Row `sec5d_coefficient_recurrence`. -/
theorem sec5d_coefficient_recurrence_proved (m : ℝ) :
    monoCoeffA m 0 = 1 ∧ ∀ n : ℕ,
      monoCoeffA m (n + 1) = ((n : ℝ) ^ 2 - m ^ 2) /
        (((n : ℝ) + 1) * ((n : ℝ) + 1 / 2)) * monoCoeffA m n :=
  ⟨by rw [monoCoeffA], fun n => by rw [monoCoeffA]⟩

/-- Row `sec5d_beta_positive`. -/
theorem sec5d_beta_positive_proved {m : ℝ} (hm : 1 < m) (hm2 : m < 2) (n : ℕ) :
    0 < monoBeta m n := by
  unfold monoBeta
  have hprod : 0 < ∏ j ∈ Finset.Icc 2 (n + 1), ((j : ℝ) ^ 2 - m ^ 2) := by
    apply Finset.prod_pos
    intro j hj
    have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    nlinarith
  have hm1 : 0 < m ^ 2 - 1 := by nlinarith
  exact div_pos (mul_pos (mul_pos (mul_pos (by positivity) (pow_pos (by linarith) 2)) hm1) hprod)
    (Nat.cast_pos.mpr (Nat.factorial_pos _))

/-- Row `sec5d_sin_square_strictMono`. -/
theorem sec5d_sin_square_strictMono_proved :
    StrictMonoOn (fun α : ℝ => Real.sin α ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
  intro x hx y hy hxy
  have hpi := Real.pi_pos
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2])
  have hlt : Real.sin x < Real.sin y :=
    Real.strictMonoOn_sin ⟨by linarith [hx.1], hx.2.le⟩ ⟨by linarith [hy.1], hy.2.le⟩ hxy
  exact pow_lt_pow_left₀ hlt hsx.le two_ne_zero

/-- Row `sec5d_U_endpoint`. -/
theorem sec5d_U_endpoint_proved {m lam : ℝ} (hm : 1 < m) (hm2 : m < 2) (hl : 0 < lam) (hl1 : lam < 1) :
    Real.sin (m * (Real.pi / (m + 1))) = Real.sin (Real.pi / (m + 1)) ∧
    monoPsi m (Real.pi / (m + 1)) = (m ^ 2 - 1) / Real.sin (Real.pi / (m + 1)) ^ 2 ∧
    m ^ 2 - 1 < monoPsi m (Real.pi / (m + 1)) ∧
    4 * (m ^ 2 - 1) * lam / (1 + lam) ^ 2 < m ^ 2 - 1 := by
  have hpi := Real.pi_pos
  have hm1 : 0 < m + 1 := by linarith
  have hm1' : m + 1 ≠ 0 := hm1.ne'
  have hx0 : 0 < Real.pi / (m + 1) := div_pos hpi hm1
  have hx2 : Real.pi / (m + 1) < Real.pi / 2 := by
    rw [div_lt_div_iff₀ hm1 two_pos]
    nlinarith
  have hs : 0 < Real.sin (Real.pi / (m + 1)) := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)
  have hc : 0 < Real.cos (Real.pi / (m + 1)) := Real.cos_pos_of_mem_Ioo ⟨by linarith, hx2⟩
  have hsin : Real.sin (m * (Real.pi / (m + 1))) = Real.sin (Real.pi / (m + 1)) := by
    rw [← Real.sin_pi_sub]
    congr 1
    field_simp
    ring
  have hmsq : 0 < m ^ 2 - 1 := by nlinarith
  have hpsi : monoPsi m (Real.pi / (m + 1)) = (m ^ 2 - 1) / Real.sin (Real.pi / (m + 1)) ^ 2 := by
    rw [monoPsi, hsin, div_eq_div_iff (pow_pos hs 4).ne' (pow_pos hs 2).ne']
    ring
  have hs1 : Real.sin (Real.pi / (m + 1)) ^ 2 < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / (m + 1)), mul_pos hc hc]
  refine ⟨hsin, hpsi, ?_, ?_⟩
  · rw [hpsi, lt_div_iff₀ (pow_pos hs 2)]
    nlinarith [mul_lt_mul_of_pos_left hs1 hmsq]
  · have hthr := sec5d_lambda_threshold_lt_one_proved (show -1 < lam by linarith) hl1
    have e : 4 * (m ^ 2 - 1) * lam / (1 + lam) ^ 2 = (m ^ 2 - 1) * (4 * lam / (1 + lam) ^ 2) := by ring
    rw [e]
    nlinarith [mul_lt_mul_of_pos_left hthr hmsq]

end GKSharp

