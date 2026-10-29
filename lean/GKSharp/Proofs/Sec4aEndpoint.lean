/- GKSharp/Proofs/Sec4aEndpoint.lean - slice (b): the analytic Omega endpoint and the root p0 (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v0.80, each as `<row>_proved` with the row's exact type. The computer checks
(GKSharp.ComputerChecked.Check...) enter ONLY as the rows' own explicit hypotheses.
- omega_endpoint_factors (A:55-56), `1 < p ≤ 1.001`, `L = log 2 ∈ (0.6931471803, 0.6931471808)`:
  `2^{q-1} = e^{L(q-1)} ≤ e^{-L/2} e^{L/2000}`, `(e^{-L/2})² = 1/2`, `e^{L/2000} < 1/(1 - L/2000)`, so
  `p 2^{q-1} ≤ 1.001 · 0.70711 · 1.0003468 ≤ 0.7081`. With `x = π - π/p ∈ [0, 0.0031416]`: `sn = sin x ≥ 2x/π ≥ p - 1`
  (Jordan), `sn^{p-1} = e^{(p-1) log sn} ≥ 1 + (p-1) log(p-1) ≥ 1 + (p-1)(1 - 10L) - 1/1024` (from
  `log(1024(p-1)) ≥ 1 - 1/(1024(p-1))`), and `cs^{1-q} ≥ cs = cos x ≥ 1 - x²/2` (`cs ≤ 1`, `1 - q ≤ 1`).
- omega_endpoint (A:54-56): `Ω ≤ p 2^{p-1}/sn - κ₀ = (2^q/sn)(p 2^{q-1} - sn^{p-1} cs^{1-q}) < 0`
  (omega_midpoint_bound and the two factors).
- p0_spec (A:41, S:43-44): `Ω < 0` on `(1, a0]` (omega_endpoint, CheckOmegaNeg); `Ω' > 0` on `[a0, b0]`, so `Ω` is
  continuous and strictly increasing there; `Ω > 0` on `[b0, 1.268]` (CheckOmegaRoot). The intermediate value theorem
  gives the one zero `z ∈ (a0, b0)` below `1.268`; it is the least element of `omegaZeros`, so `p0 = z`.
-/
import GKSharp.Proofs.Sec4aOmega
import GKSharp.ComputerChecked

namespace GKSharp

open Set GKSharp.Threshold GKSharp.ComputerChecked

/-- First endpoint factor: `p 2^{q-1} ≤ 0.7081` for `1 < p ≤ 1.001`. -/
lemma sec4a_two_pow_factor {p : ℝ} (hp : 1 < p) (hhi : p ≤ 1001 / 1000) :
    p * 2 ^ (q p - 1) ≤ 7081 / 10000 := by
  have hp0 : 0 < p := by linarith
  have hL1 : 6931471803 / 10000000000 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL2 : Real.log 2 < 6931471808 / 10000000000 := by linarith [Real.log_two_lt_d9]
  have hq : q p - 1 ≤ -(4995 / 10000) := by unfold q; linarith
  have h2 : (2 : ℝ) ^ (q p - 1) ≤ Real.exp (-(Real.log 2 / 2)) * Real.exp (Real.log 2 / 2000) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ Real.log 2)
    linarith
  have hu : Real.exp (-(Real.log 2 / 2)) * Real.exp (-(Real.log 2 / 2)) = (2 : ℝ)⁻¹ := by
    rw [← Real.exp_add, show -(Real.log 2 / 2) + -(Real.log 2 / 2) = -Real.log 2 by ring, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hu0 := Real.exp_pos (-(Real.log 2 / 2))
  have hu' : Real.exp (-(Real.log 2 / 2)) ≤ 70711 / 100000 := by nlinarith
  have hv := Real.exp_bound_div_one_sub_of_interval' (x := Real.log 2 / 2000) (by linarith) (by linarith)
  have hv' : Real.exp (Real.log 2 / 2000) ≤ 10003468 / 10000000 := by
    refine hv.le.trans ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  have huv : Real.exp (-(Real.log 2 / 2)) * Real.exp (Real.log 2 / 2000) ≤
      70711 / 100000 * (10003468 / 10000000) :=
    mul_le_mul hu' hv' (Real.exp_pos _).le (by norm_num)
  calc p * 2 ^ (q p - 1) ≤ p * (Real.exp (-(Real.log 2 / 2)) * Real.exp (Real.log 2 / 2000)) :=
        mul_le_mul_of_nonneg_left h2 hp0.le
    _ ≤ 1001 / 1000 * (70711 / 100000 * (10003468 / 10000000)) :=
        mul_le_mul hhi huv (by positivity) (by norm_num)
    _ ≤ 7081 / 10000 := by norm_num

/-- Second endpoint factor: `0.993 < sn^{p-1} cs^{1-q}` for `1 < p ≤ 1.001`. -/
lemma sec4a_sn_cs_factor {p : ℝ} (hp : 1 < p) (hhi : p ≤ 1001 / 1000) :
    993 / 1000 < sn p ^ (p - 1) * cs p ^ (1 - q p) := by
  have hp0 : 0 < p := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpi4 : Real.pi < 31416 / 10000 := by linarith [Real.pi_lt_d4]
  have hL1 : 6931471803 / 10000000000 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL2 : Real.log 2 < 6931471808 / 10000000000 := by linarith [Real.log_two_lt_d9]
  have hsn0 := sec4a_sn_pos hp
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.pi - Real.pi / p := ⟨_, rfl⟩
  have hsn : sn p = Real.sin x := by rw [hx, Real.sin_pi_sub]; rfl
  have hcs : cs p = Real.cos x := by rw [hx, Real.cos_pi_sub]; rfl
  -- the angle: `0 ≤ x ≤ π (p - 1) ≤ 0.0031416`
  have hx0 : 0 ≤ x := by
    have := div_lt_self hpi hp
    linarith
  have hlow : Real.pi * (2 - p) ≤ Real.pi / p := by
    have h1p : 2 - p ≤ 1 / p := by
      rw [le_div_iff₀ hp0]
      nlinarith
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h1p hpi.le
  have hpp := mul_le_mul_of_nonneg_left hhi hpi.le
  have hxle : x ≤ 31416 / 10000000 := by rw [hx]; linarith
  -- `sn ≥ p - 1` (Jordan)
  have hJ := Real.mul_le_sin hx0 (by linarith : x ≤ Real.pi / 2)
  have hJe : 2 / Real.pi * x = 2 - 2 / p := by rw [hx]; field_simp
  have h2p : 2 / p ≤ 3 - p := by
    rw [div_le_iff₀ hp0]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ p - 1) (by linarith : (0 : ℝ) ≤ 2 - p)]
  rw [hJe] at hJ
  have hsn_ge : p - 1 ≤ sn p := by rw [hsn]; linarith
  -- `cs^{1-q} ≥ cs ≥ 1 - x²/2 ≥ 0.999995`
  have hcs_ge : 1 - x ^ 2 / 2 ≤ cs p := by rw [hcs]; exact Real.one_sub_sq_div_two_le_cos
  have hcs_le : cs p ≤ 1 := by rw [hcs]; exact Real.cos_le_one x
  have hxx : x * x ≤ 31416 / 10000000 * (31416 / 10000000) := mul_le_mul hxle hxle hx0 (by norm_num)
  have hcs_b : 999995 / 1000000 ≤ cs p := by nlinarith
  have hcs0 : 0 < cs p := by linarith
  have hB : cs p ≤ cs p ^ (1 - q p) := by
    have := Real.rpow_le_rpow_of_exponent_ge hcs0 hcs_le (show 1 - q p ≤ 1 by unfold q; linarith)
    rwa [Real.rpow_one] at this
  -- `sn^{p-1} ≥ 1 + (p-1) log sn ≥ 1 + (p-1) log(p-1) ≥ 0.99309`
  have he0 : 0 < p - 1 := by linarith
  have hA : 1 + Real.log (sn p) * (p - 1) ≤ sn p ^ (p - 1) := by
    rw [Real.rpow_def_of_pos hsn0]
    linarith [Real.add_one_le_exp (Real.log (sn p) * (p - 1))]
  have hlogle : Real.log (p - 1) ≤ Real.log (sn p) := Real.log_le_log he0 hsn_ge
  have h1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num]
    simp [Real.log_pow]
  have hlog : Real.log (1024 * (p - 1)) = 10 * Real.log 2 + Real.log (p - 1) := by
    rw [Real.log_mul (by norm_num : (1024 : ℝ) ≠ 0) he0.ne', h1024]
  have hinv := Real.one_sub_inv_le_log_of_pos (by positivity : (0 : ℝ) < 1024 * (p - 1))
  rw [hlog] at hinv
  have hmul : (p - 1) * (1024 * (p - 1))⁻¹ = 1 / 1024 := by field_simp
  have hAb : 99309 / 100000 ≤ sn p ^ (p - 1) := by
    have h1 := mul_le_mul_of_nonneg_left hlogle he0.le
    have h2 := mul_le_mul_of_nonneg_left hinv he0.le
    have h3 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1001 / 1000 - p)
      (by linarith : (0 : ℝ) ≤ 10 * Real.log 2 - 1)
    linarith
  have hBb : 999995 / 1000000 ≤ cs p ^ (1 - q p) := hcs_b.trans hB
  calc (993 / 1000 : ℝ) < 99309 / 100000 * (999995 / 1000000) := by norm_num
    _ ≤ sn p ^ (p - 1) * cs p ^ (1 - q p) := mul_le_mul hAb hBb (by norm_num) (by linarith)

/-- A:55-56, row `omega_endpoint_factors`. -/
theorem omega_endpoint_factors_proved (p : ℝ) (hp : 1 < p) (hhi : p ≤ 1001 / 1000) :
    p * 2 ^ (q p - 1) ≤ 7081 / 10000 ∧
    993 / 1000 < sn p ^ (p - 1) * cs p ^ (1 - q p) :=
  ⟨sec4a_two_pow_factor hp hhi, sec4a_sn_cs_factor hp hhi⟩

/-- A:54-56, row `omega_endpoint`. -/
theorem omega_endpoint_proved (p : ℝ) (hp : 1 < p) (hhi : p ≤ 1001 / 1000) : omega p < 0 := by
  have hp2 : p < 2 := by linarith
  have hsn0 := sec4a_sn_pos hp
  have hmid := omega_midpoint_bound_proved p hp hp2
  have hf1 := sec4a_two_pow_factor hp hhi
  have hf2 := sec4a_sn_cs_factor hp hhi
  have h2q : (0 : ℝ) < 2 ^ q p := Real.rpow_pos_of_pos (by norm_num) _
  have hsplit : (2 : ℝ) ^ (p - 1) = 2 ^ q p * 2 ^ (q p - 1) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    unfold q
    ring
  have hkap : kappaZero p = 2 ^ q p * (sn p ^ (p - 1) * cs p ^ (1 - q p)) / sn p := by
    unfold kappaZero
    rw [show p - 2 = p - 1 - 1 by ring, Real.rpow_sub_one hsn0.ne' (p - 1)]
    ring
  have hkey : p * 2 ^ (p - 1) / sn p - kappaZero p =
      2 ^ q p / sn p * (p * 2 ^ (q p - 1) - sn p ^ (p - 1) * cs p ^ (1 - q p)) := by
    rw [hkap, hsplit]
    ring
  have hneg : 2 ^ q p / sn p * (p * 2 ^ (q p - 1) - sn p ^ (p - 1) * cs p ^ (1 - q p)) < 0 :=
    mul_neg_of_pos_of_neg (div_pos h2q hsn0) (by linarith)
  show omegaFirst p (sStar p) - kappaZero p < 0
  linarith

/-- A:41, S:43-44, row `p0_spec`. -/
theorem p0_spec_proved (hn : CheckOmegaNeg) (hr : CheckOmegaRoot) :
    IsLeast omegaZeros p0 ∧ a0 < p0 ∧ p0 < b0 ∧
    (∀ p ∈ Ioc (1 : ℝ) (317 / 250), omega p = 0 ↔ p = p0) ∧
    (∀ p ∈ Ioo (1 : ℝ) p0, omega p < 0) ∧
    (∀ p ∈ Icc p0 (317 / 250), 0 ≤ omega p) := by
  obtain ⟨hd, hpos⟩ := hr
  have hneg : ∀ p ∈ Ioc (1 : ℝ) a0, omega p < 0 := by
    rintro p ⟨hp1, hp2⟩
    by_cases hp : p ≤ 1001 / 1000
    · exact omega_endpoint_proved p hp1 hp
    · push Not at hp
      exact hn p ⟨hp.le, hp2⟩
  have hcont : ContinuousOn omega (Icc a0 b0) := fun x hx =>
    (differentiableAt_of_deriv_ne_zero (hd x hx).ne').continuousAt.continuousWithinAt
  have hmono : StrictMonoOn omega (Icc a0 b0) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont fun x hx => hd x (interior_subset hx)
  have ha1 : (1 : ℝ) < a0 := by norm_num [a0]
  have hb1 : b0 < 317 / 250 := by norm_num [b0]
  have ha0 : omega a0 < 0 := hn a0 ⟨by norm_num [a0], le_rfl⟩
  have hb0 : 0 < omega b0 := hpos b0 ⟨le_rfl, hb1.le⟩
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo (by norm_num [a0, b0]) hcont ⟨ha0, hb0⟩
  have hzab : z ∈ Icc a0 b0 := Ioo_subset_Icc_self hz
  have hbelow : ∀ p ∈ Ioo (1 : ℝ) z, omega p < 0 := by
    rintro p ⟨hp1, hp2⟩
    by_cases ha : p ≤ a0
    · exact hneg p ⟨hp1, ha⟩
    push Not at ha
    have := hmono ⟨ha.le, by linarith [hz.2]⟩ hzab hp2
    linarith
  have habove : ∀ p ∈ Ioc z (317 / 250), 0 < omega p := by
    rintro p ⟨hp1, hp2⟩
    by_cases hb : b0 ≤ p
    · exact hpos p ⟨hb, hp2⟩
    push Not at hb
    have := hmono hzab ⟨by linarith [hz.1], hb.le⟩ hp1
    linarith
  have hleast : IsLeast omegaZeros z := by
    refine ⟨⟨by linarith [hz.1], by linarith [hz.2], hz0⟩, ?_⟩
    rintro p ⟨hp1, hp2, hp⟩
    by_contra hlt
    push Not at hlt
    exact absurd hp (hbelow p ⟨hp1, hlt⟩).ne
  have hp0 : p0 = z := hleast.csInf_eq
  rw [hp0]
  refine ⟨hleast, hz.1, hz.2, ?_, hbelow, ?_⟩
  · rintro p ⟨hp1, hp2⟩
    constructor
    · intro hp
      by_cases hlt : p < z
      · exact absurd hp (hbelow p ⟨hp1, hlt⟩).ne
      by_cases hgt : z < p
      · exact absurd hp (habove p ⟨hgt, hp2⟩).ne'
      push Not at hlt hgt
      exact le_antisymm hgt hlt
    · rintro rfl
      exact hz0
  · rintro p ⟨hp1, hp2⟩
    rcases hp1.lt_or_eq with hlt | heq
    · exact (habove p ⟨hlt, hp2⟩).le
    · rw [← heq]
      exact hz0.symm.le

end GKSharp
