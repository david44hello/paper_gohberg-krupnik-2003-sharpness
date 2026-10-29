/- Lemma B+ series, W sign, scalar criterion and assembly, frozen sec5d_monotone.tex:70-80 (rows
sec5d_Bplus_double_series, sec5d_Bplus_W_negative, sec5d_Bplus_scalar_criterion, lemma_Bplus; types verbatim from
the proposal v020).
Double series: for fixed n the sum over k is three logarithm series; the sum over n is three logarithms of Euler
products (log of an unconditional product). lemma_Bplus is premise-style on the open row lemma_onevar.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.MonotonicityCurve
import GKSharp.Proofs.MonotoneBplusA

namespace GKSharp

open Filter Topology

namespace BplusB

/-- The logarithm of an unconditional product of nonzero reals with nonzero value. -/
theorem hasSum_log_of_hasProd {f : ℕ → ℝ} {a : ℝ} (hf : ∀ n, f n ≠ 0) (ha : a ≠ 0) (h : HasProd f a) :
    HasSum (fun n => Real.log (f n)) (Real.log a) := by
  have ht := (Real.continuousAt_log ha).tendsto.comp h
  unfold HasSum
  refine ht.congr fun s => ?_
  exact Real.log_prod (fun i _ => hf i)

/-- sec5d:75-77: the Euler product in logarithmic form. -/
theorem hasSum_log_sinc {y : ℝ} (hy : 0 < y) (hyπ : y < Real.pi) :
    HasSum (fun n : ℕ => Real.log (1 - y ^ 2 / (((n : ℝ) + 1) * Real.pi) ^ 2))
      (Real.log (Real.sin y / y)) := by
  refine hasSum_log_of_hasProd (fun n => ?_) ?_ (sec5d_euler_sine_product_proved hy hyπ)
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hpi : Real.pi ≤ ((n : ℝ) + 1) * Real.pi := by nlinarith [Real.pi_pos]
    have h1 : y ^ 2 / (((n : ℝ) + 1) * Real.pi) ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]
      exact pow_lt_pow_left₀ (hyπ.trans_le hpi) hy.le two_ne_zero
    exact (sub_pos.mpr h1).ne'
  · exact (div_pos (Real.sin_pos_of_pos_of_lt_pi hy hyπ) hy).ne'

/-- sec5d:77: for fixed n the inner series over k is three logarithm series. -/
theorem hasSum_inner {eps y a : ℝ} (he0 : 0 ≤ eps) (he1 : eps ≤ 1) (hy0 : 0 ≤ y / a) (hy1 : y / a < 1) :
    HasSum (fun k : ℕ => (y / a) ^ (2 * (k + 1)) / ((k : ℝ) + 1) *
        (1 + eps ^ (2 * (k + 1)) - 2 * (1 - eps) ^ (2 * (k + 1))))
      (-Real.log (1 - y ^ 2 / a ^ 2) - Real.log (1 - (eps * y) ^ 2 / a ^ 2) +
        2 * Real.log (1 - ((1 - eps) * y) ^ 2 / a ^ 2)) := by
  -- x = y / a and u = 1 - eps as atoms, so `ring` sees monomials under the symbolic powers
  obtain ⟨x, hx⟩ : ∃ x, x = y / a := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = 1 - eps := ⟨_, rfl⟩
  rw [← hx] at hy0 hy1 ⊢
  rw [← hu]
  have hsq : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → 0 ≤ (c * x) ^ 2 ∧ (c * x) ^ 2 < 1 := fun c hc0 hc1 => by
    refine ⟨by positivity, ?_⟩
    have h0 : 0 ≤ c * x := mul_nonneg hc0 hy0
    have h1 : c * x < 1 := by nlinarith
    nlinarith
  obtain ⟨h1a, h1b⟩ := hsq 1 zero_le_one le_rfl
  obtain ⟨h2a, h2b⟩ := hsq eps he0 he1
  obtain ⟨h3a, h3b⟩ := hsq u (by rw [hu]; linarith) (by rw [hu]; linarith)
  have hs := ((sec5d_log_series_proved h1a h1b).add (sec5d_log_series_proved h2a h2b)).sub
    ((sec5d_log_series_proved h3a h3b).mul_left 2)
  simp only [one_mul] at hs
  have e1 : x ^ 2 = y ^ 2 / a ^ 2 := by rw [hx, div_pow]
  have e2 : (eps * x) ^ 2 = (eps * y) ^ 2 / a ^ 2 := by rw [hx, mul_div_assoc', div_pow]
  have e3 : (u * x) ^ 2 = (u * y) ^ 2 / a ^ 2 := by rw [hx, mul_div_assoc', div_pow]
  convert hs using 1
  · funext k
    ring
  · rw [e1, e2, e3]
    ring

/-- sec5d:77-78: the outer series over n sums to the logarithmic ratio. -/
theorem hasSum_outer {eps θ : ℝ} (he0 : 0 < eps) (he1 : eps < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    HasSum (fun n : ℕ => -Real.log (1 - θ ^ 2 / (((n : ℝ) + 1) * Real.pi) ^ 2) -
        Real.log (1 - (eps * θ) ^ 2 / (((n : ℝ) + 1) * Real.pi) ^ 2) +
        2 * Real.log (1 - ((1 - eps) * θ) ^ 2 / (((n : ℝ) + 1) * Real.pi) ^ 2))
      (monoLogRatio eps θ) := by
  have hf0 : 0 < 1 - eps := by linarith
  have ha : 0 < eps * θ := mul_pos he0 hθ0
  have hb : 0 < (1 - eps) * θ := mul_pos hf0 hθ0
  have ha' : eps * θ < Real.pi := by nlinarith
  have hb' : (1 - eps) * θ < Real.pi := by nlinarith
  have h := ((hasSum_log_sinc hθ0 hθ).neg.sub (hasSum_log_sinc ha ha')).add
    ((hasSum_log_sinc hb hb').mul_left 2)
  convert h using 1
  have s1 := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
  have s2 := Real.sin_pos_of_pos_of_lt_pi ha ha'
  have s3 := Real.sin_pos_of_pos_of_lt_pi hb hb'
  have q1 : 0 < Real.sin θ / θ := div_pos s1 hθ0
  have q2 : 0 < Real.sin (eps * θ) / (eps * θ) := div_pos s2 ha
  have q3 : 0 < Real.sin ((1 - eps) * θ) / ((1 - eps) * θ) := div_pos s3 hb
  have hR : eps * Real.sin ((1 - eps) * θ) ^ 2 / ((1 - eps) ^ 2 * Real.sin θ * Real.sin (eps * θ)) =
      (Real.sin ((1 - eps) * θ) / ((1 - eps) * θ)) ^ 2 /
        (Real.sin θ / θ * (Real.sin (eps * θ) / (eps * θ))) := by
    field_simp
  rw [monoLogRatio, hR, Real.log_div (pow_pos q3 2).ne' (mul_pos q1 q2).ne', Real.log_mul q1.ne' q2.ne',
    Real.log_pow]
  push_cast
  ring

/-- The exact type of the open row `GKSharp.Paper.lemma_onevar` (sec5d:43-45), used as a premise. -/
abbrev OnevarHyp : Prop :=
  ∀ {p lam θ : ℝ}, 1 < p → p < 2 → -1 < lam → lam < 1 → 0 < θ → θ < Real.pi →
    DifferentiableAt ℝ (curveKf p lam) θ ∧
    SignType.sign (deriv (curveKf p lam) θ) =
      SignType.sign (4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 -
        monoPsi (p / (2 - p)) ((1 - p / 2) * θ))

theorem sqrt3_lt_two : Real.sqrt 3 < 2 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

end BplusB

open BplusB

/-- Row `sec5d_Bplus_double_series`. -/
theorem sec5d_Bplus_double_series_proved {eps θ : ℝ} (he : 2 - Real.sqrt 3 ≤ eps) (he1 : eps < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (∀ n : ℕ, Summable (monoDoubleTerm eps θ n)) ∧
    Summable (fun n : ℕ => ∑' k : ℕ, monoDoubleTerm eps θ n k) ∧
    monoLogRatio eps θ = ∑' n : ℕ, ∑' k : ℕ, monoDoubleTerm eps θ n k := by
  have he0 : 0 < eps := by linarith [sqrt3_lt_two]
  have hx : ∀ n : ℕ, 0 ≤ θ / (((n : ℝ) + 1) * Real.pi) ∧ θ / (((n : ℝ) + 1) * Real.pi) < 1 := fun n => by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hpi : Real.pi ≤ ((n : ℝ) + 1) * Real.pi := by nlinarith [Real.pi_pos]
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by positivity)]
    linarith
  have hin : ∀ n : ℕ, HasSum (monoDoubleTerm eps θ n)
      (-Real.log (1 - θ ^ 2 / (((n : ℝ) + 1) * Real.pi) ^ 2) -
        Real.log (1 - (eps * θ) ^ 2 / (((n : ℝ) + 1) * Real.pi) ^ 2) +
        2 * Real.log (1 - ((1 - eps) * θ) ^ 2 / (((n : ℝ) + 1) * Real.pi) ^ 2)) :=
    fun n => hasSum_inner he0.le he1.le (hx n).1 (hx n).2
  have hsum : HasSum (fun n : ℕ => ∑' k : ℕ, monoDoubleTerm eps θ n k) (monoLogRatio eps θ) := by
    convert hasSum_outer he0 he1 hθ0 hθ using 2 with n
    exact (hin n).tsum_eq
  exact ⟨fun n => (hin n).summable, hsum.summable, hsum.tsum_eq.symm⟩

/-- Row `sec5d_Bplus_W_negative`. -/
theorem sec5d_Bplus_W_negative_proved {p θ : ℝ} (hp1 : 3 - Real.sqrt 3 ≤ p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    0 < monoLogRatio (p - 1) θ ∧ monoW (p - 1) θ < 0 := by
  have he : 2 - Real.sqrt 3 ≤ p - 1 := by linarith
  have he1 : p - 1 < 1 := by linarith
  have he0 : 0 < p - 1 := by linarith [sqrt3_lt_two]
  obtain ⟨hsumk, hsumn, heq⟩ := sec5d_Bplus_double_series_proved he he1 hθ0 hθ
  -- every bracket is nonnegative: k = 0 is the first bracket, k ≥ 1 the higher bracket at k + 1 ≥ 2
  have hbr : ∀ k : ℕ, 0 ≤ 1 + (p - 1) ^ (2 * (k + 1)) - 2 * (1 - (p - 1)) ^ (2 * (k + 1)) := fun k => by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact (sec5d_Bplus_first_bracket_proved he he1).2
    · have hb := sec5d_Bplus_higher_bracket_proved he he1 (k := k + 1) (by omega)
      linarith [hb.1, hb.2, pow_nonneg he0.le (2 * (k + 1))]
  have hterm : ∀ n k, 0 ≤ monoDoubleTerm (p - 1) θ n k := fun n k => by
    unfold monoDoubleTerm
    exact mul_nonneg (by positivity) (hbr k)
  have hterm01 : 0 < monoDoubleTerm (p - 1) θ 0 1 := by
    unfold monoDoubleTerm
    have hb := sec5d_Bplus_higher_bracket_proved he he1 (k := 1 + 1) (by norm_num)
    exact mul_pos (by positivity) (by linarith [hb.1, hb.2, pow_nonneg he0.le (2 * (1 + 1))])
  have hinner0 : 0 < ∑' k : ℕ, monoDoubleTerm (p - 1) θ 0 k := (hsumk 0).tsum_pos (hterm 0) 1 hterm01
  have hpos : 0 < monoLogRatio (p - 1) θ := by
    rw [heq]
    exact hsumn.tsum_pos (fun n => tsum_nonneg (hterm n)) 0 hinner0
  refine ⟨hpos, ?_⟩
  have hD : 0 < (1 - (p - 1)) ^ 2 * Real.sin θ * Real.sin ((p - 1) * θ) :=
    mul_pos (mul_pos (pow_pos (by linarith) 2) (Real.sin_pos_of_pos_of_lt_pi hθ0 hθ))
      (Real.sin_pos_of_pos_of_lt_pi (mul_pos he0 hθ0) (by nlinarith))
  rw [monoLogRatio, Real.log_pos_iff (div_nonneg (mul_nonneg he0.le (sq_nonneg _)) hD.le),
    one_lt_div hD] at hpos
  rw [monoW]
  linarith

/-- Row `sec5d_Bplus_scalar_criterion`. -/
theorem sec5d_Bplus_scalar_criterion_proved {p θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (monoPsi (p / (2 - p)) ((1 - p / 2) * θ) ≥ (p / (2 - p)) ^ 2 - 1 ↔ monoW (p - 1) θ ≤ 0) ∧
    (p - 1) * θ ∈ Set.Ioo 0 Real.pi ∧ (1 - (p - 1)) * θ ∈ Set.Ioo 0 Real.pi := by
  have h2p : 0 < 2 - p := by linarith
  have h2p' : 2 - p ≠ 0 := h2p.ne'
  have hlt1 : (p - 1) * θ < θ := by nlinarith
  have hlt2 : (1 - (p - 1)) * θ < θ := by nlinarith
  refine ⟨?_, ⟨mul_pos (by linarith) hθ0, by linarith⟩, ⟨mul_pos (by linarith) hθ0, by linarith⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, m = p / (2 - p) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (1 - p / 2) * θ := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = p / 2 * θ := ⟨_, rfl⟩
  rw [← hm, ← hB]
  have hmB : m * B = A := by
    rw [hm, hB, hA, div_mul_eq_mul_div, div_eq_iff h2p']
    ring
  have hm2 : (2 - p) ^ 2 * m ^ 2 = p ^ 2 := by
    have h1 : (2 - p) * m = p := by
      rw [hm, mul_div_assoc', mul_comm, mul_div_assoc, div_self h2p', mul_one]
    calc (2 - p) ^ 2 * m ^ 2 = ((2 - p) * m) ^ 2 := by ring
      _ = p ^ 2 := by rw [h1]
  have hsθ : Real.sin θ = Real.sin A * Real.cos B + Real.cos A * Real.sin B := by
    rw [← Real.sin_add, hA, hB]
    ring_nf
  have hsε : Real.sin ((p - 1) * θ) = Real.sin A * Real.cos B - Real.cos A * Real.sin B := by
    rw [← Real.sin_sub, hA, hB]
    ring_nf
  have hs2 : Real.sin ((1 - (p - 1)) * θ) = 2 * Real.sin B * Real.cos B := by
    rw [← Real.sin_two_mul, hB]
    ring_nf
  have hsB : 0 < Real.sin B :=
    Real.sin_pos_of_pos_of_lt_pi (by rw [hB]; nlinarith) (by rw [hB]; nlinarith)
  have key : monoW (p - 1) θ =
      (2 - p) ^ 2 * ((m ^ 2 - 1) * Real.sin B ^ 4 - (m ^ 2 * Real.sin B ^ 2 - Real.sin A ^ 2)) := by
    rw [monoW, hsθ, hsε, hs2]
    linear_combination (Real.sin B ^ 2 - Real.sin B ^ 4) * hm2 +
      ((2 - p) ^ 2 * Real.sin A ^ 2 - 4 * (p - 1) * Real.sin B ^ 2) * Real.sin_sq_add_cos_sq B -
      (2 - p) ^ 2 * Real.sin B ^ 2 * Real.sin_sq_add_cos_sq A
  rw [key, monoPsi, hmB, ge_iff_le, le_div_iff₀ (pow_pos hsB 4)]
  constructor
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
  · intro h
    by_contra hc
    have := mul_pos (pow_pos h2p 2)
      (show 0 < (m ^ 2 - 1) * Real.sin B ^ 4 - (m ^ 2 * Real.sin B ^ 2 - Real.sin A ^ 2) by
        linarith [not_le.mp hc])
    linarith

/-- Row `lemma_Bplus`, premise-style on the open row `lemma_onevar` (its exact type `OnevarHyp`). -/
theorem lemma_Bplus_proved (onevar : OnevarHyp) {p lam : ℝ} (hp1 : 3 - Real.sqrt 3 ≤ p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) := by
  have hp1' : 1 < p := by linarith [sqrt3_lt_two]
  have hm : 1 < p / (2 - p) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hm2 : 0 < (p / (2 - p)) ^ 2 - 1 := by nlinarith
  have hthr := sec5d_lambda_threshold_lt_one_proved hl hl1
  have hderiv : ∀ θ ∈ Set.Ioo 0 Real.pi, deriv (curveKf p lam) θ < 0 := by
    rintro θ ⟨hθ0, hθ⟩
    have hsign := (onevar hp1' hp2 hl hl1 hθ0 hθ).2
    have hW := (sec5d_Bplus_W_negative_proved hp1 hp2 hθ0 hθ).2
    have hPsi := (sec5d_Bplus_scalar_criterion_proved hp1' hp2 hθ0 hθ).1.mpr hW.le
    have e : 4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 =
        ((p / (2 - p)) ^ 2 - 1) * (4 * lam / (1 + lam) ^ 2) := by ring
    have hlt := mul_lt_mul_of_pos_left hthr hm2
    have hneg : 4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 -
        monoPsi (p / (2 - p)) ((1 - p / 2) * θ) < 0 := by
      rw [e]
      linarith
    exact sign_eq_neg_one_iff.mp (hsign.trans (sign_eq_neg_one_iff.mpr hneg))
  have hcont : ContinuousOn (curveKf p lam) (Set.Ioo 0 Real.pi) := fun θ hθ =>
    (onevar hp1' hp2 hl hl1 hθ.1 hθ.2).1.continuousAt.continuousWithinAt
  exact strictAntiOn_of_deriv_neg (convex_Ioo 0 Real.pi) hcont (by rwa [interior_Ioo])

end GKSharp

