/- RealLineUnique.lean - project 019, N family: a real-line Lp function killed by all one-sided weak tests is zero;
   consequences for RealLinePencil (identification of outputs, uniqueness, one-sided frequency inputs).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.RealLineFourier

open MeasureTheory Real Filter Topology
open scoped FourierTransform ENNReal

namespace GKSharp.Proofs.RealLineUnique

open GKSharp.RealLineFourier

/-- The frozen N10 statement (density of separated compact-frequency Schwartz tests), for every exponent q > 1. -/
def N10Prop : Prop :=
  ∀ (q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)], 1 < q → ∀ (f : LpR q) (ε : ℝ), 0 < ε →
    ∃ g : SchwartzMap ℝ ℂ, ‖g.toLp (ENNReal.ofReal q) volume - f‖ < ε ∧
      HasCompactSupport (paperFourier g) ∧ 0 ∉ tsupport (paperFourier g)

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- Hölder: an Lp function (1 < p) times a Schwartz function is integrable. -/
theorem integrable_mul_schwartz (hp : 1 < p) (h : LpR p) (g : SchwartzMap ℝ ℂ) :
    Integrable (fun x => h x * g x) := by
  have hconjR : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal (p / (p - 1))) :=
    ⟨by rw [inv_one]; exact hconjR.inv_add_inv_ennreal⟩
  exact (Lp.memLp h).integrable_mul (g.memLp (ENNReal.ofReal (p / (p - 1))) volume)

/-- The paper's Fourier integral is Mathlib's Fourier transform at ξ/(2π) (same proof as the N03 helper). -/
theorem paper_eq_fourier (f : ℝ → ℂ) (ξ : ℝ) : paperFourier f ξ = 𝓕 f (ξ / (2 * Real.pi)) := by
  unfold paperFourier
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hreal : -2 * Real.pi * x * (ξ / (2 * Real.pi)) = -(x * ξ) := by
    field_simp
  rw [hreal]
  simp only [smul_eq_mul]
  have hcomplex : ((-(x * ξ) : ℝ) : ℂ) * Complex.I = -Complex.I * (x : ℂ) * (ξ : ℂ) := by push_cast; ring
  rw [hcomplex, mul_comm]

/-- 𝓕⁻ψ at x is the paper transform of ψ at -2πx. -/
theorem fourierInv_eq_paper (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    (𝓕⁻ ψ : SchwartzMap ℝ ℂ) x = paperFourier ψ (x * (-(2 * Real.pi))) := by
  rw [paper_eq_fourier, SchwartzMap.fourierInv_apply_eq]
  have hx : x * (-(2 * Real.pi)) / (2 * Real.pi) = -x := by field_simp
  rw [hx]
  rfl

/-- A compactly supported Schwartz function vanishing on (-δ, δ) splits into two one-sided Schwartz pieces. -/
theorem split_halflines (φ : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (φ : ℝ → ℂ)) {δ : ℝ} (hδ : 0 < δ)
    (h0 : ∀ x, |x| < δ → φ x = 0) :
    ∃ φp φm : SchwartzMap ℝ ℂ, Function.support φp ⊆ Set.Ioi 0 ∧ Function.support φm ⊆ Set.Iio 0 ∧
      φ = φp + φm := by
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : ℝ → ℂ) := φ.smooth ⊤
  have hp_s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => if 0 < x then φ x else 0) := by
    refine contDiff_iff_contDiffAt.mpr fun x => ?_
    rcases lt_or_ge 0 x with hx | hx
    · refine hsm.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [show (0 : ℝ) < y from hy]
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds (show x < δ by linarith)] with y hy
      by_cases hy0 : 0 < y
      · simp [hy0, h0 y (by rw [abs_of_pos hy0]; exact hy)]
      · simp [hy0]
  have hm_s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => if x < 0 then φ x else 0) := by
    refine contDiff_iff_contDiffAt.mpr fun x => ?_
    rcases lt_or_ge x 0 with hx | hx
    · refine hsm.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [show y < (0 : ℝ) from hy]
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds (show -δ < x by linarith)] with y hy
      by_cases hy0 : y < 0
      · simp [hy0, h0 y (by rw [abs_of_neg hy0]; linarith [show -δ < y from hy])]
      · simp [hy0]
  have hp_c : HasCompactSupport (fun x : ℝ => if 0 < x then φ x else 0) :=
    hc.mono fun x hx => by by_cases hx0 : 0 < x <;> simp_all
  have hm_c : HasCompactSupport (fun x : ℝ => if x < 0 then φ x else 0) :=
    hc.mono fun x hx => by by_cases hx0 : x < 0 <;> simp_all
  refine ⟨hp_c.toSchwartzMap hp_s, hm_c.toSchwartzMap hm_s, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · have hx' : (if 0 < x then φ x else 0) ≠ 0 := hx
    by_contra hx0
    exact hx' (by simp [show ¬ (0 : ℝ) < x from hx0])
  · have hx' : (if x < 0 then φ x else 0) ≠ 0 := hx
    by_contra hx0
    exact hx' (by simp [show ¬ x < (0 : ℝ) from hx0])
  · ext x
    rw [SchwartzMap.add_apply]
    change φ x = (if 0 < x then φ x else 0) + (if x < 0 then φ x else 0)
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · simp [hx, not_lt.mpr hx.le]
    · simp [h0 0 (by simpa using hδ)]
    · simp [hx, not_lt.mpr hx.le]

/-- Step 1: an N10-type test ψ is a sum of Fourier transforms of one-sided Schwartz functions, so it is killed. -/
theorem integral_mul_eq_zero_of_test (hp : 1 < p) (h : LpR p)
    (hpos : ∀ φ : SchwartzMap ℝ ℂ, Function.support φ ⊆ Set.Ioi 0 → ∫ x, h x * 𝓕 φ x = 0)
    (hneg : ∀ φ : SchwartzMap ℝ ℂ, Function.support φ ⊆ Set.Iio 0 → ∫ x, h x * 𝓕 φ x = 0)
    (ψ : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (paperFourier ψ)) (hz : 0 ∉ tsupport (paperFourier ψ)) :
    ∫ x, h x * ψ x = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isClosed_tsupport (paperFourier ψ)).isOpen_compl 0 hz
  have hzero : ∀ η : ℝ, |η| < r → paperFourier ψ η = 0 := by
    intro η hη
    by_contra hne
    exact hball (by simpa [Real.dist_eq] using hη) (subset_tsupport _ (Function.mem_support.mpr hne))
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hφfun : ((𝓕⁻ ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
      (paperFourier ψ) ∘ (fun x => x * (-(2 * Real.pi))) := by
    funext x
    exact fourierInv_eq_paper ψ x
  have hφc : HasCompactSupport ((𝓕⁻ ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    rw [hφfun]
    exact hc.comp_isClosedEmbedding
      (Homeomorph.mulRight₀ (-(2 * Real.pi)) (neg_ne_zero.mpr h2pi.ne')).isClosedEmbedding
  have hφ0 : ∀ x, |x| < r / (2 * Real.pi) → (𝓕⁻ ψ : SchwartzMap ℝ ℂ) x = 0 := by
    intro x hx
    rw [fourierInv_eq_paper]
    apply hzero
    rw [abs_mul, abs_neg, abs_of_pos h2pi]
    rwa [lt_div_iff₀ h2pi] at hx
  obtain ⟨φp, φm, hsp, hsm, hsplit⟩ := split_halflines (𝓕⁻ ψ) hφc (by positivity) hφ0
  have hψ : ψ = 𝓕 φp + 𝓕 φm := by
    rw [← FourierTransform.fourier_add, ← hsplit, FourierTransform.fourier_fourierInv_eq]
  have hfun : ∀ x, h x * ψ x = h x * 𝓕 φp x + h x * 𝓕 φm x := fun x => by
    rw [hψ, SchwartzMap.add_apply, mul_add]
  simp_rw [hfun]
  rw [integral_add (integrable_mul_schwartz hp h _) (integrable_mul_schwartz hp h _), hpos φp hsp,
    hneg φm hsm, add_zero]

/-- (A) annihilation: an Lp function (1 < p) killed by every one-sided weak test is zero. -/
theorem eq_zero_of_halfline_tests (hp : 1 < p) (hN10 : N10Prop) (h : LpR p)
    (hpos : ∀ φ : SchwartzMap ℝ ℂ, Function.support φ ⊆ Set.Ioi 0 → ∫ x, h x * 𝓕 φ x = 0)
    (hneg : ∀ φ : SchwartzMap ℝ ℂ, Function.support φ ⊆ Set.Iio 0 → ∫ x, h x * 𝓕 φ x = 0) : h = 0 := by
  have hconjR : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have hq1 : 1 < p / (p - 1) := hconjR.symm.lt
  have : Fact (1 ≤ ENNReal.ofReal (p / (p - 1))) :=
    ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le⟩
  have : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal (p / (p - 1))) :=
    ⟨by rw [inv_one]; exact hconjR.inv_add_inv_ennreal⟩
  let Λ : LpR (p / (p - 1)) →L[ℂ] ℂ :=
    (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume (ENNReal.ofReal p) (ENNReal.ofReal (p / (p - 1))) h
  have hΛ : ∀ g : LpR (p / (p - 1)), Λ g = ∫ x, h x * g x := fun g =>
    (ContinuousLinearMap.mul ℂ ℂ).lpPairing_eq_integral h g
  have htest : ∀ ψ : SchwartzMap ℝ ℂ, HasCompactSupport (paperFourier ψ) → 0 ∉ tsupport (paperFourier ψ) →
      Λ (ψ.toLp (ENNReal.ofReal (p / (p - 1))) volume) = 0 := by
    intro ψ hc hz
    rw [hΛ, ← integral_mul_eq_zero_of_test hp h hpos hneg ψ hc hz]
    apply integral_congr_ae
    filter_upwards [ψ.coeFn_toLp (ENNReal.ofReal (p / (p - 1))) volume] with x hx
    rw [hx]
  have hzero : ∀ g : LpR (p / (p - 1)), Λ g = 0 := by
    intro g
    refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
    obtain ⟨ψ, hψ, hc, hz⟩ := hN10 (p / (p - 1)) hq1 g (ε / (‖Λ‖ + 1)) (by positivity)
    have hsplit : Λ g = -Λ (ψ.toLp (ENNReal.ofReal (p / (p - 1))) volume - g) := by
      rw [map_sub, htest ψ hc hz]; ring
    rw [hsplit, norm_neg, zero_add]
    calc ‖Λ (ψ.toLp (ENNReal.ofReal (p / (p - 1))) volume - g)‖
        ≤ ‖Λ‖ * ‖ψ.toLp (ENNReal.ofReal (p / (p - 1))) volume - g‖ := Λ.le_opNorm _
      _ ≤ (‖Λ‖ + 1) * (ε / (‖Λ‖ + 1)) := by
          gcongr
          linarith [norm_nonneg Λ]
      _ = ε := by field_simp
  have hset : ∀ S : Set ℝ, MeasurableSet S → volume S < ∞ → ∫ x in S, h x = 0 := by
    intro S hS hSfin
    have h0 := hzero (indicatorConstLp (ENNReal.ofReal (p / (p - 1))) hS hSfin.ne (1 : ℂ))
    rw [hΛ] at h0
    rw [← h0, ← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := ENNReal.ofReal (p / (p - 1))) (hs := hS)
      (hμs := hSfin.ne) (c := (1 : ℂ))] with x hx
    rw [hx]
    by_cases hxS : x ∈ S <;> simp [Set.indicator, hxS]
  have hint : ∀ S : Set ℝ, MeasurableSet S → volume S < ∞ → IntegrableOn (h : ℝ → ℂ) S volume := by
    intro S _ hSfin
    have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hSfin.ne
    exact ((Lp.memLp h).restrict S).integrable (Fact.out : 1 ≤ ENNReal.ofReal p)
  exact Lp.eq_zero_iff_ae_eq_zero.mpr (ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite hint hset)

variable {α β : ℂ}

theorem integral_sub_mul (hp : 1 < p) (a b : LpR p) (g : SchwartzMap ℝ ℂ) :
    ∫ x, (a - b) x * g x = (∫ x, a x * g x) - ∫ x, b x * g x := by
  rw [← integral_sub (integrable_mul_schwartz hp a g) (integrable_mul_schwartz hp b g)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub a b] with x hx
  rw [hx, Pi.sub_apply, sub_mul]

/-- (B) identification: an Lp function that passes the weak tests of T for the input f is T.map f. -/
theorem map_eq_of_tests (hp : 1 < p) (hN10 : N10Prop) (T : RealLinePencil p α β) (f u : LpR p)
    (hpos : ∀ φ : SchwartzMap ℝ ℂ, Function.support φ ⊆ Set.Ioi 0 →
      ∫ x, u x * 𝓕 φ x = α * ∫ x, f x * 𝓕 φ x)
    (hneg : ∀ φ : SchwartzMap ℝ ℂ, Function.support φ ⊆ Set.Iio 0 →
      ∫ x, u x * 𝓕 φ x = β * ∫ x, f x * 𝓕 φ x) : T.map f = u := by
  refine sub_eq_zero.mp (eq_zero_of_halfline_tests hp hN10 _ (fun φ hφ => ?_) (fun φ hφ => ?_))
  · rw [integral_sub_mul hp, T.positive_test f φ hφ, hpos φ hφ, sub_self]
  · rw [integral_sub_mul hp, T.negative_test f φ hφ, hneg φ hφ, sub_self]

/-- N01_unique, with N10 (density, the row) as the explicit input. -/
theorem slice_N01_unique_of_N10 (hN10 : N10Prop) (hp : 1 < p) (α β : ℂ) (T S : RealLinePencil p α β) :
    T = S := by
  have hmap : T.map = S.map := ContinuousLinearMap.ext fun f =>
    map_eq_of_tests hp hN10 T f (S.map f) (S.positive_test f) (S.negative_test f)
  cases T
  cases S
  cases hmap
  rfl

/-- Schwartz duality: if 𝓕u and φ have disjoint supports, then ∫ u·𝓕φ = 0. -/
theorem integral_mul_fourier_eq_zero (u φ : SchwartzMap ℝ ℂ) (hdisj : ∀ x, 𝓕 u x = 0 ∨ φ x = 0) :
    ∫ x, u x * 𝓕 φ x = 0 := by
  rw [← SchwartzMap.integral_fourier_mul_eq]
  have hz : ∀ ξ, 𝓕 u ξ * φ ξ = 0 := fun ξ => by
    rcases hdisj ξ with h0 | h0 <;> simp [h0]
  simp [hz]

theorem integral_toLp_mul (u : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) :
    ∫ x, (u.toLp (ENNReal.ofReal p) volume) x * g x = ∫ x, u x * g x := by
  apply integral_congr_ae
  filter_upwards [u.coeFn_toLp (ENNReal.ofReal p) volume] with x hx
  rw [hx]

theorem integral_smul_toLp_mul (c : ℂ) (u : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) :
    ∫ x, (c • u.toLp (ENNReal.ofReal p) volume) x * g x = c * ∫ x, u x * g x := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c (u.toLp (ENNReal.ofReal p) volume),
    u.coeFn_toLp (ENNReal.ofReal p) volume] with x hx hu
  rw [hx, Pi.smul_apply, hu, smul_eq_mul, mul_assoc]

/-- (C+) a Schwartz input whose Fourier transform vanishes on (-∞, 0] is multiplied by α. -/
theorem map_toLp_of_fourier_pos (hp : 1 < p) (hN10 : N10Prop) (T : RealLinePencil p α β)
    (u : SchwartzMap ℝ ℂ) (hu : ∀ ξ, ξ ≤ 0 → 𝓕 u ξ = 0) :
    T.map (u.toLp (ENNReal.ofReal p) volume) = α • u.toLp (ENNReal.ofReal p) volume := by
  refine map_eq_of_tests hp hN10 T _ _ (fun φ _ => ?_) (fun φ hφ => ?_)
  · rw [integral_smul_toLp_mul, integral_toLp_mul]
  · have h0 : ∫ x, u x * 𝓕 φ x = 0 := integral_mul_fourier_eq_zero u φ fun x => by
      by_cases hx : x ≤ 0
      · exact Or.inl (hu x hx)
      · exact Or.inr (Function.notMem_support.mp fun hmem => hx (le_of_lt (hφ hmem)))
    rw [integral_smul_toLp_mul, integral_toLp_mul, h0, mul_zero, mul_zero]

/-- (C-) a Schwartz input whose Fourier transform vanishes on [0, ∞) is multiplied by β. -/
theorem map_toLp_of_fourier_neg (hp : 1 < p) (hN10 : N10Prop) (T : RealLinePencil p α β)
    (u : SchwartzMap ℝ ℂ) (hu : ∀ ξ, 0 ≤ ξ → 𝓕 u ξ = 0) :
    T.map (u.toLp (ENNReal.ofReal p) volume) = β • u.toLp (ENNReal.ofReal p) volume := by
  refine map_eq_of_tests hp hN10 T _ _ (fun φ hφ => ?_) (fun φ _ => ?_)
  · have h0 : ∫ x, u x * 𝓕 φ x = 0 := integral_mul_fourier_eq_zero u φ fun x => by
      by_cases hx : 0 ≤ x
      · exact Or.inl (hu x hx)
      · exact Or.inr (Function.notMem_support.mp fun hmem => hx (le_of_lt (hφ hmem)))
    rw [integral_smul_toLp_mul, integral_toLp_mul, h0, mul_zero, mul_zero]
  · rw [integral_smul_toLp_mul, integral_toLp_mul]

end GKSharp.Proofs.RealLineUnique
