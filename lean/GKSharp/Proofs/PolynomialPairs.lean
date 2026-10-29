/- polynomial/Fourier correspondence, generic018 Discs port.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.FourierDensity

open Real

namespace GKSharp

/-- The point `e^{iθ}` of the unit circle (the form used in `DiscIneq`). -/
noncomputable def unitPt (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem continuous_unitPt : Continuous unitPt :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

theorem mode_natCast (k : ℕ) (a : ℂ) (θ : ℝ) : mode (k : ℤ) a θ = a * unitPt θ ^ k := by
  unfold mode unitPt
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem mode_neg_natCast (k : ℕ) (a : ℂ) (θ : ℝ) :
    mode (-(k : ℤ)) a θ = a * (starRingEnd ℂ) (unitPt θ) ^ k := by
  unfold mode unitPt
  rw [← Complex.exp_conj, ← Complex.exp_nat_mul]
  congr 2
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem mode_add (n : ℤ) (a b : ℂ) (θ : ℝ) : mode n (a + b) θ = mode n a θ + mode n b θ := by
  unfold mode; ring

theorem mode_zero (n : ℤ) (θ : ℝ) : mode n 0 θ = 0 := by
  unfold mode; ring

/-- `P₋f = Σ_{n<0} c_n e^{inθ}`. -/
theorem Pminus_eq_sum (c : ℤ →₀ ℂ) (θ : ℝ) :
    Pminus c θ = c.sum fun n a => if n < 0 then mode n a θ else 0 := by
  unfold Pminus trig Pplus Finsupp.sum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  split_ifs <;> first | (exfalso; omega) | ring1

theorem trig_eq_add (c : ℤ →₀ ℂ) (θ : ℝ) : trig c θ = Pplus c θ + Pminus c θ := by
  unfold Pminus; ring

/-! ### (1a) coefficients ↦ polynomials -/

/-- `z = Σ_{n ≥ 0} c_n ζ^n`. -/
noncomputable def toZ (c : ℤ →₀ ℂ) : Polynomial ℂ :=
  c.sum fun n a => if 0 ≤ n then Polynomial.monomial n.toNat a else 0

/-- `w = Σ_{n < 0} conj(c_n) ζ^{-n}`. -/
noncomputable def toW (c : ℤ →₀ ℂ) : Polynomial ℂ :=
  c.sum fun n a => if n < 0 then Polynomial.monomial (-n).toNat ((starRingEnd ℂ) a) else 0

theorem toW_coeff_zero (c : ℤ →₀ ℂ) : (toW c).coeff 0 = 0 := by
  unfold toW Finsupp.sum
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro n _
  dsimp only
  split_ifs with h
  · rw [Polynomial.coeff_monomial]
    split_ifs with h' <;> first | rfl | (exfalso; omega)
  · rw [Polynomial.coeff_zero]

theorem eval_toZ (c : ℤ →₀ ℂ) (θ : ℝ) : (toZ c).eval (unitPt θ) = Pplus c θ := by
  unfold toZ Pplus Finsupp.sum
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  split_ifs with h
  · rw [Polynomial.eval_monomial]
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [mode_natCast, Int.toNat_natCast]
  · rw [Polynomial.eval_zero]

theorem conj_eval_toW (c : ℤ →₀ ℂ) (θ : ℝ) : (starRingEnd ℂ) ((toW c).eval (unitPt θ)) = Pminus c θ := by
  rw [Pminus_eq_sum]
  unfold toW Finsupp.sum
  rw [Polynomial.eval_finsetSum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  split_ifs with h
  · rw [Polynomial.eval_monomial, map_mul, map_pow, Complex.conj_conj]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    rw [mode_neg_natCast, neg_neg, Int.toNat_natCast]
  · rw [Polynomial.eval_zero, map_zero]

theorem eval_toW (c : ℤ →₀ ℂ) (θ : ℝ) : (toW c).eval (unitPt θ) = (starRingEnd ℂ) (Pminus c θ) := by
  rw [← conj_eval_toW, Complex.conj_conj]

theorem continuous_Pplus (c : ℤ →₀ ℂ) : Continuous (Pplus c) := by
  have h : Pplus c = fun θ => (toZ c).eval (unitPt θ) := funext fun θ => (eval_toZ c θ).symm
  rw [h]
  exact (Polynomial.continuous _).comp continuous_unitPt

theorem continuous_Pminus (c : ℤ →₀ ℂ) : Continuous (Pminus c) := by
  have h : Pminus c = fun θ => (starRingEnd ℂ) ((toW c).eval (unitPt θ)) :=
    funext fun θ => (conj_eval_toW c θ).symm
  rw [h]
  exact Complex.continuous_conj.comp ((Polynomial.continuous _).comp continuous_unitPt)

/-! ### (1b) polynomials ↦ coefficients -/

/-- `c_n = z_n` for `n ≥ 0`, `c_{-k} = conj(w_k)` for `k ≥ 1`. -/
noncomputable def ofZW (z w : Polynomial ℂ) : ℤ →₀ ℂ :=
  (∑ k ∈ z.support, Finsupp.single (k : ℤ) (z.coeff k)) +
    ∑ k ∈ w.support, Finsupp.single (-(k : ℤ)) ((starRingEnd ℂ) (w.coeff k))

theorem sum_ofZW (z w : Polynomial ℂ) (F : ℤ → ℂ → ℂ) (h0 : ∀ n, F n 0 = 0)
    (hadd : ∀ n a b, F n (a + b) = F n a + F n b) :
    (ofZW z w).sum F =
      ∑ k ∈ z.support, F k (z.coeff k) + ∑ k ∈ w.support, F (-(k : ℤ)) ((starRingEnd ℂ) (w.coeff k)) := by
  unfold ofZW
  rw [Finsupp.sum_add_index' h0 hadd, ← Finsupp.sum_finsetSum_index h0 hadd,
    ← Finsupp.sum_finsetSum_index h0 hadd]
  simp only [Finsupp.sum_single_index, h0]

theorem mem_support_ne_zero {w : Polynomial ℂ} (hw : w.coeff 0 = 0) {k : ℕ} (hk : k ∈ w.support) : k ≠ 0 := by
  rintro rfl
  exact (Polynomial.mem_support_iff.mp hk) hw

theorem Pplus_ofZW (z w : Polynomial ℂ) (hw : w.coeff 0 = 0) (θ : ℝ) :
    Pplus (ofZW z w) θ = z.eval (unitPt θ) := by
  unfold Pplus
  rw [sum_ofZW z w _ (fun n => by simp [mode_zero])
    (fun n a b => by by_cases h : 0 ≤ n <;> simp [h, mode_add])]
  have hz : ∀ k ∈ w.support,
      (if 0 ≤ -(k : ℤ) then mode (-(k : ℤ)) ((starRingEnd ℂ) (w.coeff k)) θ else 0) = 0 := by
    intro k hk
    have := mem_support_ne_zero hw hk
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, add_zero, Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with h
  · rw [mode_natCast]
  · exfalso; omega

theorem Pminus_ofZW (z w : Polynomial ℂ) (hw : w.coeff 0 = 0) (θ : ℝ) :
    Pminus (ofZW z w) θ = (starRingEnd ℂ) (w.eval (unitPt θ)) := by
  rw [Pminus_eq_sum, sum_ofZW z w _ (fun n => by simp [mode_zero])
    (fun n a b => by by_cases h : n < 0 <;> simp [h, mode_add])]
  have hz : ∀ k ∈ z.support, (if (k : ℤ) < 0 then mode (k : ℤ) (z.coeff k) θ else 0) = 0 := by
    intro k _
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, zero_add, Polynomial.eval_eq_sum, Polynomial.sum_def,
    map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have := mem_support_ne_zero hw hk
  split_ifs with h
  · rw [mode_neg_natCast, map_mul, map_pow]
  · exfalso; omega


/-- sec2_obstacle.tex:37–38. Every finite Fourier sum and every analytic polynomial pair correspond exactly. -/
theorem polynomial_pair_correspondence :
    (∀ c : ℤ →₀ ℂ, ∃ z w : Polynomial ℂ, w.eval 0 = 0 ∧
      ∀ t, Pplus c t = z.eval (unitPoint t) ∧ Pminus c t = star (w.eval (unitPoint t))) ∧
    (∀ z w : Polynomial ℂ, w.eval 0 = 0 → ∃ c : ℤ →₀ ℂ,
      ∀ t, Pplus c t = z.eval (unitPoint t) ∧ Pminus c t = star (w.eval (unitPoint t))) := by
  constructor
  · intro c
    refine ⟨toZ c, toW c, ?_, fun t => ⟨(eval_toZ c t).symm, (conj_eval_toW c t).symm⟩⟩
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact toW_coeff_zero c
  · intro z w hw
    have hw0 : w.coeff 0 = 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
    exact ⟨ofZW z w, fun t => ⟨Pplus_ofZW z w hw0 t, Pminus_ofZW z w hw0 t⟩⟩

end GKSharp

