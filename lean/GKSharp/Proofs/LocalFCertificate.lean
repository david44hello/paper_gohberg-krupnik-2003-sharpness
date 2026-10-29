/- GKSharp/Proofs/LocalFCertificate.lean - kernel pc bracket signs.
Frozen source: short_v0.40/.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Threshold
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

namespace GKSharp
open GKSharp.Threshold

noncomputable def cosTaylor12 (x : ℝ) : ℝ :=
  1 - ((1 / 2 : ℚ) : ℝ) * x ^ 2 + ((1 / 24 : ℚ) : ℝ) * x ^ 4 -
    ((1 / 720 : ℚ) : ℝ) * x ^ 6 + ((1 / 40320 : ℚ) : ℝ) * x ^ 8 -
    ((1 / 3628800 : ℚ) : ℝ) * x ^ 10 + ((1 / 479001600 : ℚ) : ℝ) * x ^ 12

/-- Fixed finite exponential remainder, projected to the real part, bounds
the cosine polynomial. Every arithmetic operation remains kernel checked. -/
theorem cosTaylor12_bound (x : ℝ) (hx : |x| ≤ 1) :
    |Real.cos x - cosTaylor12 x| ≤ 1 / 10000000000 := by
  have hz : ‖(x : ℂ) * Complex.I‖ ≤ 1 := by simpa using hx
  have hb := Complex.exp_bound (x := (x : ℂ) * Complex.I) (n := 14) hz (by norm_num)
  have hpow : |x| ^ 14 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hnum : ‖Complex.exp ((x : ℂ) * Complex.I) -
      ∑ m ∈ Finset.range 14, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)‖ ≤ 1 / 10000000000 := by
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one] at hb
    norm_num [Nat.factorial] at hb
    nlinarith
  have heq : Real.cos x - cosTaylor12 x =
      (Complex.exp ((x : ℂ) * Complex.I) -
        ∑ m ∈ Finset.range 14, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re := by
    norm_num [cosTaylor12, Complex.sub_re, Complex.exp_ofReal_mul_I_re,
      Finset.sum_range_succ, Nat.factorial, mul_pow, Complex.I_sq,
      Complex.mul_re, Complex.mul_im]
    simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [heq]
  exact (Complex.abs_re_le_norm _).trans hnum

theorem localF_angle (p : ℝ) (hp : 1 < p) :
    localF p = p * dual p - 4 * (1 + Real.cos (Real.pi * (p - 1) / p) ^ 2) := by
  have ha : Real.pi * (p - 1) / p = Real.pi - Real.pi / p := by
    field_simp
  rw [ha, Real.cos_pi_sub]
  simp [localF]

/-- sec4b_failure.tex:95,103: lower bracket endpoint has F>0, now proved
without the CheckLocalF hypothesis. -/
theorem localF_bracket_lower : 0 < localF (1213490304 / 1000000000) := by
  let aa : ℝ := Real.pi * ((1667893 / 9480393 : ℚ) : ℝ)
  have hpi : Real.pi ∈ Set.Icc (3.14159265358979323846 : ℝ) 3.14159265358979323847 :=
    ⟨Real.pi_gt_d20.le, Real.pi_lt_d20.le⟩
  have ha : |aa| ≤ 1 := by
    dsimp [aa]
    rw [abs_of_pos (by positivity)]
    nlinarith [hpi.1, hpi.2]
  have hpoly : cosTaylor12 aa ≤ ((851108655422 / 1000000000000 : ℚ) : ℝ) := by
    unfold cosTaylor12 aa
    dyadic_interval [prec := 100]
  norm_num at hpoly
  have hb := cosTaylor12_bound aa ha
  have hcos : Real.cos aa ≤ 851108655522 / 1000000000000 := by
    have hh := (abs_le.mp hb).2
    linarith
  have hnonneg : 0 ≤ Real.cos aa := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> dsimp [aa] <;> nlinarith [hpi.1, hpi.2]
  rw [localF_angle _ (by norm_num)]
  have hangle : Real.pi * ((1213490304 / 1000000000 : ℝ) - 1) /
      (1213490304 / 1000000000 : ℝ) = aa := by dsimp [aa]; norm_num; ring
  rw [hangle]
  norm_num [dual]
  nlinarith [sq_nonneg (Real.cos aa - 851108655522 / 1000000000000)]

/-- sec4b_failure.tex:95,103: upper bracket endpoint has F<0, proved in kernel. -/
theorem localF_bracket_upper : localF (1213490305 / 1000000000) < 0 := by
  let aa : ℝ := Real.pi * ((42698061 / 242698061 : ℚ) : ℝ)
  have hpi : Real.pi ∈ Set.Icc (3.14159265358979323846 : ℝ) 3.14159265358979323847 :=
    ⟨Real.pi_gt_d20.le, Real.pi_lt_d20.le⟩
  have ha : |aa| ≤ 1 := by
    dsimp [aa]
    rw [abs_of_pos (by positivity)]
    nlinarith [hpi.1, hpi.2]
  have hpoly : ((851108654301 / 1000000000000 : ℚ) : ℝ) ≤ cosTaylor12 aa := by
    unfold cosTaylor12 aa
    dyadic_interval [prec := 100]
  norm_num at hpoly
  have hb := cosTaylor12_bound aa ha
  have hcos : 851108654201 / 1000000000000 ≤ Real.cos aa := by
    have hh := (abs_le.mp hb).1
    linarith
  rw [localF_angle _ (by norm_num)]
  have hangle : Real.pi * ((1213490305 / 1000000000 : ℝ) - 1) /
      (1213490305 / 1000000000 : ℝ) = aa := by dsimp [aa]; norm_num; ring
  rw [hangle]
  norm_num [dual]
  nlinarith [sq_nonneg (Real.cos aa - 851108654201 / 1000000000000)]

end GKSharp

#print axioms GKSharp.cosTaylor12_bound
#print axioms GKSharp.localF_bracket_lower
#print axioms GKSharp.localF_bracket_upper
