/- O21 (sec2_obstacle.tex l.73-76, short v0.40): a polynomial g ≠ 0 with g(0) = 0 is, on the closed unit
disk, z^k · B · h with k ≥ 1, B a finite Blaschke product, h zero-free on the open disk, and h = H² with H continuous
on the closed disk and holomorphic inside. No cited input.
Copyright (C) Dave Goel 2026--now.

  Root by root, g = c ∏ (z - a): a = 0 raises k; 0 < |a| < 1 gives z - a = b_a(z) (1 - ā z) with the Blaschke factor
  b_a(z) = (z - a)/(1 - ā z) (|z| ≤ 1 keeps 1 - ā z ≠ 0); |a| ≥ 1 gives z - a = (-a)(1 - a⁻¹ z). So h = C ∏ (1 - u z)
  with C ≠ 0 and every |u| ≤ 1, and Re(1 - u z) ≥ 1 - |z| ≥ 0 on the closed disk (> 0 inside). There the principal
  square root w ↦ w^(1/2) is continuous (holomorphic where Re w > 0), so H = C^(1/2) ∏ (1 - u z)^(1/2).
  k ≥ 1: at z = 0, B(0) = ∏ (-a) ≠ 0 and h(0) = C ≠ 0, so g(0) = 0 forces k ≠ 0. -/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace GKSharp

namespace BlaschkeLift

open Polynomial Complex Metric

/-- `∏ (z - a)/(1 - ā z)` over `roots` (the product in `FiniteBlaschke`, phase 1). -/
noncomputable def bProd (roots : List ℂ) (z : ℂ) : ℂ := (roots.map fun a => (z - a) / (1 - star a * z)).prod

/-- `∏ (1 - u z)` over `us`. -/
noncomputable def hProd (us : List ℂ) (z : ℂ) : ℂ := (us.map fun u => 1 - u * z).prod

/-- `∏ (1 - u z)^(1/2)` over `us` (principal branch). -/
noncomputable def sProd (us : List ℂ) (z : ℂ) : ℂ := (us.map fun u => (1 - u * z) ^ (2⁻¹ : ℂ)).prod

lemma hProd_nil (z : ℂ) : hProd [] z = 1 := by simp [hProd]

lemma sProd_nil (z : ℂ) : sProd [] z = 1 := by simp [sProd]

lemma bProd_cons (a : ℂ) (roots : List ℂ) (z : ℂ) :
    bProd (a :: roots) z = (z - a) / (1 - star a * z) * bProd roots z := by
  simp [bProd]

lemma hProd_cons (u : ℂ) (us : List ℂ) (z : ℂ) : hProd (u :: us) z = (1 - u * z) * hProd us z := by
  simp [hProd]

lemma sProd_cons (u : ℂ) (us : List ℂ) (z : ℂ) :
    sProd (u :: us) z = (1 - u * z) ^ (2⁻¹ : ℂ) * sProd us z := by
  simp [sProd]

lemma re_one_sub_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (1 - w).re := by
  have := re_le_norm w
  simp only [sub_re, one_re]
  linarith

lemma re_one_sub_nonneg {w : ℂ} (hw : ‖w‖ ≤ 1) : 0 ≤ (1 - w).re := by
  have := re_le_norm w
  simp only [sub_re, one_re]
  linarith

lemma ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) : w ≠ 0 := by
  rintro rfl
  simp at hw

lemma norm_mul_lt_one {u z : ℂ} (hu : ‖u‖ ≤ 1) (hz : ‖z‖ < 1) : ‖u * z‖ < 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg z) hu).trans_lt hz

lemma norm_mul_le_one {u z : ℂ} (hu : ‖u‖ ≤ 1) (hz : ‖z‖ ≤ 1) : ‖u * z‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg z) hu).trans hz

/-! ### The factorization -/

/-- `f = z^k · bProd roots · (C · hProd us)` on the closed unit disk, with nonzero `C`, Blaschke roots `0 < |a| < 1`
and factors `|u| ≤ 1`. -/
def LiftData (f : ℂ → ℂ) : Prop :=
  ∃ (k : ℕ) (roots us : List ℂ) (C : ℂ), C ≠ 0 ∧ (∀ a ∈ roots, a ≠ 0 ∧ ‖a‖ < 1) ∧ (∀ u ∈ us, ‖u‖ ≤ 1) ∧
    ∀ z ∈ closedBall (0 : ℂ) 1, f z = z ^ k * bProd roots z * (C * hProd us z)

/-- One more root `a`: the three cases `a = 0`, `0 < |a| < 1`, `|a| ≥ 1`. -/
lemma liftData_mul {f g : ℂ → ℂ} (a : ℂ) (hf : LiftData f) (hg : ∀ z, g z = (z - a) * f z) : LiftData g := by
  obtain ⟨k, roots, us, C, hC, hroots, hus, heq⟩ := hf
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨k + 1, roots, us, C, hC, hroots, hus, fun z hz => ?_⟩
    rw [hg, heq z hz]
    ring
  by_cases ha1 : ‖a‖ < 1
  · refine ⟨k, a :: roots, star a :: us, C, hC, List.forall_mem_cons.2 ⟨⟨ha0, ha1⟩, hroots⟩,
      List.forall_mem_cons.2 ⟨by rw [norm_star]; exact ha1.le, hus⟩, fun z hz => ?_⟩
    have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.1 hz
    have hlt : ‖star a * z‖ < 1 := by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_right (norm_nonneg a) hz1).trans_lt ha1
    have key : (z - a) / (1 - star a * z) * (1 - star a * z) = z - a :=
      div_mul_cancel₀ _ (ne_zero_of_re_pos (re_one_sub_pos hlt))
    rw [hg, heq z hz, bProd_cons, hProd_cons]
    linear_combination (-(z ^ k * bProd roots z * (C * hProd us z))) * key
  · rw [not_lt] at ha1
    refine ⟨k, roots, a⁻¹ :: us, -a * C, mul_ne_zero (neg_ne_zero.2 ha0) hC, hroots,
      List.forall_mem_cons.2 ⟨by rw [norm_inv]; exact inv_le_one_of_one_le₀ ha1, hus⟩, fun z hz => ?_⟩
    have key : z - a = -a * (1 - a⁻¹ * z) := by
      rw [mul_sub, mul_one, neg_mul, mul_inv_cancel_left₀ ha0]
      ring
    rw [hg, heq z hz, hProd_cons, key]
    ring

/-- `c ∏_{a ∈ s} (z - a)` has lift data, by induction on the multiset `s`. -/
lemma liftData_prod (c : ℂ) (hc : c ≠ 0) (s : Multiset ℂ) : LiftData fun z => c * (s.map fun a => z - a).prod := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, [], [], c, hc, by simp, by simp, fun z _ => by simp [bProd, hProd]⟩
  | cons a s ih =>
    exact liftData_mul a ih fun z => by
      simp only [Multiset.map_cons, Multiset.prod_cons]
      ring

/-- `g(z) = lc(g) ∏_{a ∈ roots g} (z - a)` (ℂ is algebraically closed). -/
lemma eval_eq_prod_roots (g : ℂ[X]) (z : ℂ) : g.eval z = g.leadingCoeff * (g.roots.map fun a => z - a).prod := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (p := g) IsAlgClosed.card_roots_eq_natDegree]
  simp [eval_multiset_prod, Multiset.map_map]

/-! ### The zero-free factor and its square root -/

lemma hProd_differentiable (us : List ℂ) : Differentiable ℂ (hProd us) := by
  induction us with
  | nil => rw [show hProd [] = fun _ => 1 from funext hProd_nil]; exact differentiable_const 1
  | cons u us ih =>
    have h : hProd (u :: us) = fun z => (1 - u * z) * hProd us z := funext (hProd_cons u us)
    rw [h]
    fun_prop

lemma hProd_ne_zero {us : List ℂ} (hus : ∀ u ∈ us, ‖u‖ ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) : hProd us z ≠ 0 := by
  induction us with
  | nil => simp [hProd]
  | cons u us ih =>
    rw [List.forall_mem_cons] at hus
    rw [hProd_cons]
    exact mul_ne_zero (ne_zero_of_re_pos (re_one_sub_pos (norm_mul_lt_one hus.1 hz))) (ih hus.2)

lemma sProd_sq (us : List ℂ) (z : ℂ) : sProd us z ^ 2 = hProd us z := by
  induction us with
  | nil => simp [sProd, hProd]
  | cons u us ih => rw [sProd_cons, hProd_cons, mul_pow, cpow_ofNat_inv_pow, ih]

lemma re_half_pos : 0 < (2⁻¹ : ℂ).re := by norm_num

lemma sProd_continuousOn {us : List ℂ} (hus : ∀ u ∈ us, ‖u‖ ≤ 1) : ContinuousOn (sProd us) (closedBall 0 1) := by
  induction us with
  | nil => rw [show sProd [] = fun _ => 1 from funext sProd_nil]; exact continuousOn_const
  | cons u us ih =>
    rw [List.forall_mem_cons] at hus
    have h : sProd (u :: us) = fun z => (1 - u * z) ^ (2⁻¹ : ℂ) * sProd us z := funext (sProd_cons u us)
    rw [h]
    refine ContinuousOn.mul (fun z hz => ?_) (ih hus.2)
    have hre := re_one_sub_nonneg (norm_mul_le_one hus.1 (mem_closedBall_zero_iff.1 hz))
    exact ((continuousAt_cpow_const_of_re_pos (Or.inl hre) re_half_pos).comp
      (f := fun z : ℂ => 1 - u * z) (by fun_prop)).continuousWithinAt

lemma sProd_differentiableOn {us : List ℂ} (hus : ∀ u ∈ us, ‖u‖ ≤ 1) :
    DifferentiableOn ℂ (sProd us) (ball 0 1) := by
  induction us with
  | nil => rw [show sProd [] = fun _ => 1 from funext sProd_nil]; exact differentiableOn_const 1
  | cons u us ih =>
    rw [List.forall_mem_cons] at hus
    have h : sProd (u :: us) = fun z => (1 - u * z) ^ (2⁻¹ : ℂ) * sProd us z := funext (sProd_cons u us)
    rw [h]
    refine DifferentiableOn.mul (fun z hz => ?_) (ih hus.2)
    have hre := re_one_sub_pos (norm_mul_lt_one hus.1 (mem_ball_zero_iff.1 hz))
    exact (DifferentiableAt.cpow_const (f := fun z : ℂ => 1 - u * z) (by fun_prop)
      (mem_slitPlane_iff.2 (Or.inl hre))).differentiableWithinAt

lemma bProd_zero_ne_zero {roots : List ℂ} (h : ∀ a ∈ roots, a ≠ 0 ∧ ‖a‖ < 1) : bProd roots 0 ≠ 0 := by
  induction roots with
  | nil => simp [bProd]
  | cons a l ih =>
    rw [List.forall_mem_cons] at h
    rw [bProd_cons]
    refine mul_ne_zero ?_ (ih h.2)
    simpa using h.1.1

/-! ### The row -/

/-- O21, sec2_obstacle.tex l.73-76 (v0.40), with `FiniteBlaschke B` written out. -/
theorem slice_O21_proved (g : Polynomial ℂ) (hg0 : g.eval 0 = 0) (hg : g ≠ 0) :
    ∃ (k : ℕ) (B h H : ℂ → ℂ), 1 ≤ k ∧
      (∃ (phase : ℂ) (roots : List ℂ), ‖phase‖ = 1 ∧ (∀ a ∈ roots, ‖a‖ < 1) ∧
        ∀ z : ℂ, B z = phase * (roots.map fun a => (z - a) / (1 - star a * z)).prod) ∧
      DifferentiableOn ℂ h (Metric.ball 0 1) ∧ DifferentiableOn ℂ H (Metric.ball 0 1) ∧
      ContinuousOn h (Metric.closedBall 0 1) ∧ ContinuousOn H (Metric.closedBall 0 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, h z ≠ 0) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, H z ^ 2 = h z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, g.eval z = z ^ k * B z * h z) := by
  obtain ⟨k, roots, us, C, hC, hroots, hus, heq⟩ :=
    liftData_prod g.leadingCoeff (leadingCoeff_ne_zero.2 hg) g.roots
  have hev : ∀ z ∈ closedBall (0 : ℂ) 1, g.eval z = z ^ k * bProd roots z * (C * hProd us z) :=
    fun z hz => (eval_eq_prod_roots g z).trans (heq z hz)
  have hh0 : ∀ z ∈ ball (0 : ℂ) 1, C * hProd us z ≠ 0 :=
    fun z hz => mul_ne_zero hC (hProd_ne_zero hus (mem_ball_zero_iff.1 hz))
  refine ⟨k, bProd roots, fun z => C * hProd us z, fun z => C ^ (2⁻¹ : ℂ) * sProd us z, ?_,
    ⟨1, roots, norm_one, fun a ha => (hroots a ha).2, fun z => (one_mul _).symm⟩,
    ((hProd_differentiable us).const_mul C).differentiableOn, (sProd_differentiableOn hus).const_mul _,
    ((hProd_differentiable us).const_mul C).continuous.continuousOn, continuousOn_const.mul (sProd_continuousOn hus),
    hh0, fun z _ => by rw [mul_pow, cpow_ofNat_inv_pow, sProd_sq], hev⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exfalso
    have h0 := hev 0 (mem_closedBall_self zero_le_one)
    rw [hg0, hk, pow_zero, one_mul] at h0
    exact mul_ne_zero (bProd_zero_ne_zero hroots) (hh0 0 (mem_ball_self one_pos)) h0.symm
  · exact hk

end BlaschkeLift

end GKSharp
