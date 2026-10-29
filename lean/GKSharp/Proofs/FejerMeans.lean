/- O23 part 2(a): the Fejér mean of slice (a)'s `fejerMean` is the kernel average
fejerMean u N t = (2π)⁻¹ ∫_0^{2π} u(s) F_N(t - s) ds, and |u| ≤ Y gives |fejerMean u N t| ≤ Y. No cited input.
Copyright (C) Dave Goel 2026--now.

  Each term: Re[w_n (2π)⁻¹ (∫ u(s) e^{-ins} ds) e^{int}] = w_n (2π)⁻¹ ∫ u(s) cos(n(t - s)) ds; summing gives the
  kernel average. F_N ≥ 0 and ∫_0^{2π} F_N(t - s) ds = ∫_{-π}^{π} F_N = 2π (shift + periodicity), so
  |fejerMean| ≤ (2π)⁻¹ ∫ |u(s)| F_N(t - s) ds ≤ Y. -/
import GKSharp.Proofs.FejerKernel
import GKSharp.Defs.Potential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace GKSharp

namespace Fejer

open Real MeasureTheory Finset

/-- `fejerMean` of slice (a) Potential v0.40, the same body (the coverage file's definition unfolds to it). -/
noncomputable def fejerMean (u : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    ((1 - (n.natAbs : ℝ) / (N + 1) : ℝ) : ℂ) *
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      (∫ s in (0 : ℝ)..(2 * Real.pi), (u s : ℂ) * unitPoint (-(n : ℝ) * s)) *
      unitPoint ((n : ℝ) * t)).re

lemma intervalIntegrable_of_norm_le {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : AEStronglyMeasurable g volume) {Y : ℝ} (hY : ∀ t, ‖g t‖ ≤ Y) (a b : ℝ) :
    IntervalIntegrable g volume a b := by
  constructor <;> exact Measure.integrableOn_of_bounded (by simp) hg (M := Y) (ae_of_all _ hY)

lemma intervalIntegrable_of_bdd {u : ℝ → ℝ} (hu : Measurable u) {Y : ℝ} (hY : ∀ t, |u t| ≤ Y) (a b : ℝ) :
    IntervalIntegrable u volume a b :=
  intervalIntegrable_of_norm_le hu.aestronglyMeasurable (fun t => by simpa [Real.norm_eq_abs] using hY t) a b

lemma unitPoint_mul_unitPoint (n : ℤ) (s t : ℝ) :
    unitPoint (-(n : ℝ) * s) * unitPoint ((n : ℝ) * t) = Complex.exp (((n * (t - s) : ℝ) : ℂ) * Complex.I) := by
  simp only [unitPoint, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- One term of `fejerMean`: `Re[c (2π)⁻¹ (∫ u e^{-ins}) e^{int}] = c (2π)⁻¹ ∫ u(s) cos(n(t - s)) ds`. -/
lemma term_re {u : ℝ → ℝ} (hu : Measurable u) {Y : ℝ} (hY : ∀ t, |u t| ≤ Y) (c : ℝ) (n : ℤ) (t : ℝ) :
    ((c : ℂ) * (((2 * π)⁻¹ : ℝ) : ℂ) * (∫ s in (0 : ℝ)..(2 * π), (u s : ℂ) * unitPoint (-(n : ℝ) * s)) *
      unitPoint ((n : ℝ) * t)).re = c * (2 * π)⁻¹ * ∫ s in (0 : ℝ)..(2 * π), u s * cos (n * (t - s)) := by
  have hcont : Continuous fun s : ℝ => Complex.exp (((n * (t - s) : ℝ) : ℂ) * Complex.I) := by fun_prop
  have hF : IntervalIntegrable (fun s => (u s : ℂ) * Complex.exp (((n * (t - s) : ℝ) : ℂ) * Complex.I))
      volume 0 (2 * π) :=
    intervalIntegrable_of_norm_le (g := fun s => (u s : ℂ) * Complex.exp (((n * (t - s) : ℝ) : ℂ) * Complex.I))
      ((Complex.measurable_ofReal.comp hu).mul hcont.measurable).aestronglyMeasurable
      (fun s => by rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs]; exact hY s)
      0 (2 * π)
  have hint : (∫ s in (0 : ℝ)..(2 * π), (u s : ℂ) * unitPoint (-(n : ℝ) * s)) * unitPoint ((n : ℝ) * t) =
      ∫ s in (0 : ℝ)..(2 * π), (u s : ℂ) * Complex.exp (((n * (t - s) : ℝ) : ℂ) * Complex.I) := by
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [mul_assoc, unitPoint_mul_unitPoint]
  have hre : (∫ s in (0 : ℝ)..(2 * π), (u s : ℂ) * Complex.exp (((n * (t - s) : ℝ) : ℂ) * Complex.I)).re =
      ∫ s in (0 : ℝ)..(2 * π), u s * cos (n * (t - s)) := by
    rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hF]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [Complex.reCLM_apply, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [mul_assoc, hint, ← Complex.ofReal_mul, Complex.re_ofReal_mul, hre]

/-- `fejerMean` is the Fejér-kernel average. -/
lemma fejerMean_eq {u : ℝ → ℝ} (hu : Measurable u) {Y : ℝ} (hY : ∀ t, |u t| ≤ Y) (N : ℕ) (t : ℝ) :
    fejerMean u N t = (2 * π)⁻¹ * ∫ s in (0 : ℝ)..(2 * π), u s * kerF N (t - s) := by
  have hcos : ∀ n : ℤ, IntervalIntegrable (fun s => u s * cos (n * (t - s))) volume 0 (2 * π) := fun n =>
    (intervalIntegrable_of_bdd hu hY 0 (2 * π)).mul_continuousOn (by fun_prop : Continuous fun s : ℝ =>
      cos (n * (t - s))).continuousOn
  have hR : ∫ s in (0 : ℝ)..(2 * π), u s * kerF N (t - s) =
      ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), (1 - (n.natAbs : ℝ) / (N + 1)) *
        ∫ s in (0 : ℝ)..(2 * π), u s * cos (n * (t - s)) := by
    have h1 : ∀ s, u s * kerF N (t - s) =
        ∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), (1 - (n.natAbs : ℝ) / (N + 1)) * (u s * cos (n * (t - s))) := fun s => by
      simp only [kerF, mul_sum]
      exact sum_congr rfl fun n _ => by ring
    simp_rw [h1]
    rw [intervalIntegral.integral_finsetSum fun n _ => (hcos n).const_mul _]
    exact sum_congr rfl fun n _ => intervalIntegral.integral_const_mul _ _
  simp only [fejerMean, Complex.re_sum]
  simp_rw [term_re hu hY]
  rw [hR, mul_sum]
  exact sum_congr rfl fun n _ => by ring

end Fejer

end GKSharp
