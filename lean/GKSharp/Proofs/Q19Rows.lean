/-
GKSharp/Proofs/Q19Rows.lean — paper 019 short v2.30: proofs of the rows added for the formulas newly printed in short
v2.20 and v2.30 (q19_intro_hkv_example, q19_sec2_gk_explicit, q19_sec2_rescale, q19_sec5d_q_closed,
q19_sec5d_constant_term, q20_sec5d_D_split).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
No Paper import (the rows live in Paper/Statements.lean, which imports this file).
-/
import GKSharp.Proofs.GKRoot
import GKSharp.Proofs.GKProps
import GKSharp.Defs.CriticalCurve

namespace GKSharp.Proofs.Q19Rows

open GKSharp

/-- The worked example of P019_paper.tex l.108 at t = 1 (λ = 0). -/
theorem q19_intro_hkv_example_proved {p : ℝ} (hp : 1 < p) :
    Real.sqrt (1 + 1 ^ 2 * Real.tan (Real.pi / (2 * p)) ^ 2) / (1 + 1) = 1 / (2 * Real.cos (Real.pi / (2 * p))) ∧
    1 / (2 * Real.cos (Real.pi / (2 * p))) = Real.sin (Real.pi / (2 * p)) * gk p 0 ∧
    Real.sin (Real.pi / (2 * p)) * gk p 0 < gk p 0 ∧
    gk p 0 = 1 / Real.sin (Real.pi / p) := by
  have hp0 : 0 < p := by linarith
  set x := Real.pi / (2 * p) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < Real.pi / 2 := by
    rw [hx, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)
  have hsin1 : Real.sin x < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl hx1
  have htwo : Real.pi / p = 2 * x := by rw [hx]; field_simp
  have hgk : gk p 0 = 1 / Real.sin (Real.pi / p) := gk_zero p hp
  have hsin2 : Real.sin (Real.pi / p) = 2 * Real.sin x * Real.cos x := by rw [htwo, Real.sin_two_mul]
  have hgk_pos : 0 < gk p 0 := by rw [hgk, hsin2]; positivity
  refine ⟨?_, ?_, ?_, hgk⟩
  · have hsq : 1 + 1 ^ 2 * Real.tan x ^ 2 = (1 / Real.cos x) ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      linear_combination Real.sin_sq_add_cos_sq x
    rw [hsq, Real.sqrt_sq (by positivity)]
    field_simp
    ring
  · rw [hgk, hsin2]
    field_simp
  · nlinarith

/-- The explicit larger root of (2.2) (sec2_obstacle.tex l.40), for every λ < 1. -/
theorem q19_sec2_gk_explicit_proved {p : ℝ} (hp : 1 < p) {lam : ℝ} (hlam : lam < 1) :
    0 ≤ (1 - lam) ^ 2 + 4 * lam * Real.sin (Real.pi / p) ^ 2 ∧
    gk p lam = ((1 - lam) + Real.sqrt ((1 - lam) ^ 2 + 4 * lam * Real.sin (Real.pi / p) ^ 2)) /
      (2 * Real.sin (Real.pi / p)) := by
  set s := Real.sin (Real.pi / p) with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by
    rw [div_lt_iff₀ (by linarith)]; nlinarith [Real.pi_pos])
  have hs1 : s ≤ 1 := Real.sin_le_one _
  have hdisc : 0 ≤ (1 - lam) ^ 2 + 4 * lam * s ^ 2 := by
    rcases le_or_gt 0 lam with hl | hl
    · positivity
    · nlinarith [sq_nonneg (1 + lam), mul_le_mul_of_nonneg_left (pow_le_one₀ hs0.le hs1 : s ^ 2 ≤ 1) (by linarith : 0 ≤ -lam)]
  refine ⟨hdisc, ?_⟩
  set D := Real.sqrt ((1 - lam) ^ 2 + 4 * lam * s ^ 2) with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hDsq : D ^ 2 = (1 - lam) ^ 2 + 4 * lam * s ^ 2 := Real.sq_sqrt hdisc
  obtain ⟨hC, hmax⟩ := gk_real_eq hp hlam
  set C := gk p lam
  set r := ((1 - lam) + D) / (2 * s)
  set r' := ((1 - lam) - D) / (2 * s)
  have hsum : r + r' = (1 - lam) / s := by simp only [r, r']; field_simp; ring
  have hrr0 : r * r' = ((1 - lam) ^ 2 - D ^ 2) / (4 * s ^ 2) := by simp only [r, r']; field_simp; ring
  have hrr : r * r' = -lam := by rw [hrr0, hDsq]; field_simp; ring
  have hquad : ∀ y : ℝ, s * (y ^ 2 - lam) - (1 - lam) * y = s * (y ^ 2 - y * (r + r') + r * r') := by
    intro y; rw [hsum, hrr]; field_simp; ring
  have hr : (1 - lam) * r = s * (r ^ 2 - lam) := by
    have h0 : r ^ 2 - r * (r + r') + r * r' = 0 := by ring
    have h1 := hquad r
    rw [h0, mul_zero] at h1
    linarith
  have hrC : r ≤ C := hmax r hr
  have hprod : (C - r) * (C - r') = 0 := by
    have h1 := hquad C
    rw [← hC, sub_self] at h1
    have h2 : C ^ 2 - C * (r + r') + r * r' = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact absurd h hs0.ne'
      · exact h
    linear_combination h2
  have hr'r : r' ≤ r := by
    simp only [r, r']
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  rcases mul_eq_zero.mp hprod with h | h
  · linarith
  · linarith

/-- The rescaling identity of sec2_obstacle.tex (after Definition 2.1), for twice-differentiable φ. -/
theorem q19_sec2_rescale_proved {q : ℝ} (hq : q ≠ 0) {φ : ℝ → ℝ} (hφ1 : Differentiable ℝ φ)
    (hφ2 : Differentiable ℝ (deriv φ)) (x : ℝ) :
    deriv (deriv (fun y => φ (y / q))) x + φ (x / q) =
      (q ^ 2)⁻¹ * (deriv (deriv φ) (x / q) + q ^ 2 * φ (x / q)) := by
  have hlin : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y / q) (1 / q) y := fun y => (hasDerivAt_id y).div_const q
  have h1 : ∀ y : ℝ, HasDerivAt (fun y => φ (y / q)) (deriv φ (y / q) * (1 / q)) y :=
    fun y => (hφ1 (y / q)).hasDerivAt.comp y (hlin y)
  have hd1 : deriv (fun y => φ (y / q)) = fun y => deriv φ (y / q) * (1 / q) := funext fun y => (h1 y).deriv
  have h2 : HasDerivAt (fun y => deriv φ (y / q) * (1 / q)) (deriv (deriv φ) (x / q) * (1 / q) * (1 / q)) x :=
    ((hφ2 (x / q)).hasDerivAt.comp x (hlin x)).mul_const (1 / q)
  rw [hd1, h2.deriv]
  field_simp

/-- The numerator of `q` equals `UV` times the closed form, modulo `sin² + cos² = 1` at `2a` and `2b`. -/
theorem num_eq_closed_mul (e X s c t d : ℝ) (h1 : s ^ 2 + c ^ 2 = 1) (h2 : t ^ 2 + d ^ 2 = 1) :
    e * (s * ((d - X) / 2) - t * ((c - X) / 2)) ^ 2 -
        ((c - X) / 2 - e * ((d - X) / 2)) * (e * ((c - X) / 2) - (d - X) / 2) * (1 - X ^ 2) =
      ((c - X) / 2 * ((d - X) / 2)) * (-(1 - e) ^ 2 * X ^ 2 + 1 + e ^ 2 - 2 * e * (c * d + s * t)) := by
  linear_combination (e * (d - X) ^ 2 / 4) * h1 + (e * (c - X) ^ 2 / 4) * h2

/-- `cos x ≠ ±1` follows from `sin x > 0`: `cos x ^ 2 < 1`. -/
theorem cos_ne_pm_one {x : ℝ} (hs : 0 < Real.sin x) : Real.cos x - 1 ≠ 0 ∧ Real.cos x - -1 ≠ 0 := by
  have hsq := Real.sin_sq_add_cos_sq x
  constructor <;> intro hh <;> nlinarith [sq_nonneg (Real.sin x)]

theorem one_sub_cos_two_mul (x : ℝ) : 2 * (1 - Real.cos (2 * x)) = 4 * Real.sin x ^ 2 := by
  rw [Real.cos_two_mul]
  linear_combination (-4) * Real.sin_sq_add_cos_sq x

/-- The printed identities of the proof of Lemma 5.4 (sec5d_monotone.tex l.28). -/
theorem q19_sec5d_q_closed_proved {p a : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ha0 : 0 < a)
    (ha : a < Real.pi / 2) :
    let ε := p - 1
    let b := (p - 1) * a
    let U := fun X : ℝ => (Real.cos (2 * a) - X) / 2
    let V := fun X : ℝ => (Real.cos (2 * b) - X) / 2
    let N := fun X : ℝ => Real.sin (2 * a) * V X - Real.sin (2 * b) * U X
    let num := fun X : ℝ => ε * N X ^ 2 - (U X - ε * V X) * (ε * U X - V X) * (1 - X ^ 2)
    let q := fun X : ℝ => num X / (U X * V X)
    (num (Real.cos (2 * a)) = 0 ∧ 1 - Real.cos (2 * a) ^ 2 = Real.sin (2 * a) ^ 2 ∧
      N (Real.cos (2 * a)) = V (Real.cos (2 * a)) * Real.sin (2 * a)) ∧
    (num (Real.cos (2 * b)) = 0 ∧ 1 - Real.cos (2 * b) ^ 2 = Real.sin (2 * b) ^ 2 ∧
      N (Real.cos (2 * b)) = -(U (Real.cos (2 * b)) * Real.sin (2 * b))) ∧
    (∀ X : ℝ, U X ≠ 0 → V X ≠ 0 →
      q X = -(1 - ε) ^ 2 * X ^ 2 + 1 + ε ^ 2 - 2 * ε * Real.cos (2 * (a - b))) ∧
    q 1 = 4 * ε * Real.sin (a - b) ^ 2 ∧ q (-1) = 4 * ε * Real.sin (a - b) ^ 2 ∧
    4 * ε * Real.sin (a - b) ^ 2 = 2 * ε * (1 - Real.cos (2 * (a - b))) ∧
    ∀ X : ℝ, 2 * N X = Real.sin (2 * (a - b)) - (Real.sin (2 * a) - Real.sin (2 * b)) * X := by
  intro ε b U V N num q
  have hb0 : 0 < b := mul_pos (by linarith) ha0
  have hba : b < a := by
    show (p - 1) * a < a
    nlinarith
  have h2a : 0 < Real.sin (2 * a) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h2b : 0 < Real.sin (2 * b) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h1 := Real.sin_sq_add_cos_sq (2 * a)
  have h2 := Real.sin_sq_add_cos_sq (2 * b)
  have hcos : Real.cos (2 * (a - b)) =
      Real.cos (2 * a) * Real.cos (2 * b) + Real.sin (2 * a) * Real.sin (2 * b) := by
    rw [show 2 * (a - b) = 2 * a - 2 * b by ring, Real.cos_sub]
  have hsin : Real.sin (2 * (a - b)) =
      Real.sin (2 * a) * Real.cos (2 * b) - Real.cos (2 * a) * Real.sin (2 * b) := by
    rw [show 2 * (a - b) = 2 * a - 2 * b by ring, Real.sin_sub]
  have hclosed : ∀ X : ℝ, U X ≠ 0 → V X ≠ 0 →
      q X = -(1 - ε) ^ 2 * X ^ 2 + 1 + ε ^ 2 - 2 * ε * Real.cos (2 * (a - b)) := by
    intro X hU hV
    show num X / (U X * V X) = _
    rw [div_eq_iff (mul_ne_zero hU hV), hcos]
    exact (num_eq_closed_mul ε X _ _ _ _ h1 h2).trans (mul_comm _ _)
  have hU1 : U 1 ≠ 0 := fun hh => (cos_ne_pm_one h2a).1 (by simpa [U] using hh)
  have hV1 : V 1 ≠ 0 := fun hh => (cos_ne_pm_one h2b).1 (by simpa [V] using hh)
  have hUm : U (-1) ≠ 0 := fun hh => (cos_ne_pm_one h2a).2 (by simpa [U] using hh)
  have hVm : V (-1) ≠ 0 := fun hh => (cos_ne_pm_one h2b).2 (by simpa [V] using hh)
  have hvalue : -(1 - ε) ^ 2 * 1 + 1 + ε ^ 2 - 2 * ε * Real.cos (2 * (a - b)) =
      4 * ε * Real.sin (a - b) ^ 2 := by
    linear_combination ε * one_sub_cos_two_mul (a - b)
  refine ⟨⟨?_, by linarith, ?_⟩, ⟨?_, by linarith, ?_⟩, hclosed, ?_, ?_, ?_, ?_⟩
  · show ε * (Real.sin (2 * a) * ((Real.cos (2 * b) - Real.cos (2 * a)) / 2) -
        Real.sin (2 * b) * ((Real.cos (2 * a) - Real.cos (2 * a)) / 2)) ^ 2 -
      ((Real.cos (2 * a) - Real.cos (2 * a)) / 2 - ε * ((Real.cos (2 * b) - Real.cos (2 * a)) / 2)) *
        (ε * ((Real.cos (2 * a) - Real.cos (2 * a)) / 2) - (Real.cos (2 * b) - Real.cos (2 * a)) / 2) *
        (1 - Real.cos (2 * a) ^ 2) = 0
    linear_combination (ε * (Real.cos (2 * b) - Real.cos (2 * a)) ^ 2 / 4) * h1
  · show Real.sin (2 * a) * V (Real.cos (2 * a)) - Real.sin (2 * b) * ((Real.cos (2 * a) - Real.cos (2 * a)) / 2) =
      V (Real.cos (2 * a)) * Real.sin (2 * a)
    ring
  · show ε * (Real.sin (2 * a) * ((Real.cos (2 * b) - Real.cos (2 * b)) / 2) -
        Real.sin (2 * b) * ((Real.cos (2 * a) - Real.cos (2 * b)) / 2)) ^ 2 -
      ((Real.cos (2 * a) - Real.cos (2 * b)) / 2 - ε * ((Real.cos (2 * b) - Real.cos (2 * b)) / 2)) *
        (ε * ((Real.cos (2 * a) - Real.cos (2 * b)) / 2) - (Real.cos (2 * b) - Real.cos (2 * b)) / 2) *
        (1 - Real.cos (2 * b) ^ 2) = 0
    linear_combination (ε * (Real.cos (2 * a) - Real.cos (2 * b)) ^ 2 / 4) * h2
  · show Real.sin (2 * a) * ((Real.cos (2 * b) - Real.cos (2 * b)) / 2) - Real.sin (2 * b) * U (Real.cos (2 * b)) =
      -(U (Real.cos (2 * b)) * Real.sin (2 * b))
    ring
  · rw [hclosed 1 hU1 hV1, ← hvalue]
    ring
  · rw [hclosed (-1) hUm hVm, ← hvalue]
    ring
  · linear_combination (-ε) * one_sub_cos_two_mul (a - b)
  · intro X
    show 2 * (Real.sin (2 * a) * ((Real.cos (2 * b) - X) / 2) - Real.sin (2 * b) * ((Real.cos (2 * a) - X) / 2)) = _
    rw [hsin]
    ring

/-- The constant-term identity of Lemma 5.5 (sec5d_monotone.tex l.49), with u₃ = u₁ − u₂. -/
theorem q19_sec5d_constant_term_proved (u₁ u₂ : ℝ) :
    Real.sin (u₁ - u₂) ^ 2 =
      Real.sin u₁ ^ 2 + Real.sin u₂ ^ 2 - 2 * Real.sin u₁ * Real.sin u₂ * Real.cos (u₁ - u₂) := by
  rw [Real.sin_sub, Real.cos_sub]
  linear_combination Real.sin u₁ ^ 2 * Real.sin_sq_add_cos_sq u₂ + Real.sin u₂ ^ 2 * Real.sin_sq_add_cos_sq u₁

/-- The derivation of (5.9) (sec5d_monotone.tex l.11): the split of `D(θ, r)` and the two product-to-sum identities,
with `a = θ/2`, `b = (p − 1)a`, `s₁ = sin(a − b)`, `s₂ = sin(a + b)`, `r = sin(γ − b)/sin(γ + b)`. -/
theorem q20_sec5d_D_split_proved (p lam θ γ : ℝ) (hplus : Real.sin (γ + (p - 1) * (θ / 2)) ≠ 0) :
    let a := θ / 2
    let b := (p - 1) * (θ / 2)
    let r := Real.sin (γ - b) / Real.sin (γ + b)
    curveD p lam θ r = (r * Real.sin (a + b) - Real.sin (a - b)) +
        lam * r * (Real.sin (a + b) - r * Real.sin (a - b)) ∧
    Real.sin (a - b) - r * Real.sin (a + b) = Real.sin (2 * b) * Real.sin (a - γ) / Real.sin (γ + b) ∧
    Real.sin (a + b) - r * Real.sin (a - b) = Real.sin (2 * b) * Real.sin (γ + a) / Real.sin (γ + b) := by
  intro a b r
  have hb : Real.sin (γ + b) ≠ 0 := hplus
  have ht1 : p / 2 * θ = a + b := by simp only [a, b]; ring
  have ht2 : (1 - p / 2) * θ = a - b := by simp only [a, b]; ring
  refine ⟨?_, ?_, ?_⟩
  · unfold curveD
    rw [ht1, ht2]
    ring
  · simp only [r]
    rw [Real.sin_two_mul, eq_div_iff hb]
    field_simp [hb]
    simp only [Real.sin_add, Real.sin_sub]
    ring
  · simp only [r]
    rw [Real.sin_two_mul, eq_div_iff hb]
    field_simp [hb]
    simp only [Real.sin_add, Real.sin_sub]
    ring

end GKSharp.Proofs.Q19Rows
