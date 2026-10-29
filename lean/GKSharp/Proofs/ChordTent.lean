/- the actual sine tent and its weak second derivative.
Source: frozen short_v0.70/sec2_obstacle.tex:104-108. Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential

open Real MeasureTheory Set Filter Topology
open scoped ContDiff

namespace GKSharp.Proofs.ChordTent

theorem tent_clamp (q c s t : ℝ) :
    chordTent q c s t = sin (q * max 0 (s - |t - c|)) := by
  unfold chordTent
  split_ifs with ht
  · rw [max_eq_right (by linarith)]
  · rw [max_eq_left (by linarith)]
    simp

theorem tent_lipschitz (q c s : ℝ) (hq : 0 < q) :
    LipschitzWith (Real.toNNReal q) (chordTent q c s) := by
  have hdist : LipschitzWith 1 (fun t : ℝ => s - |t - c|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rw [show (s - |x - c|) - (s - |y - c|) = -(|x - c| - |y - c|) by ring, abs_neg]
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (LipschitzWith.dist_left c).dist_le_mul x y
  have hmax := hdist.const_max 0
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [tent_clamp, tent_clamp]
  calc
    dist (sin (q * max 0 (s - |x - c|))) (sin (q * max 0 (s - |y - c|)))
        ≤ dist (q * max 0 (s - |x - c|)) (q * max 0 (s - |y - c|)) := by
      simpa using Real.lipschitzWith_sin.dist_le_mul
        (q * max 0 (s - |x - c|)) (q * max 0 (s - |y - c|))
    _ = q * dist (max 0 (s - |x - c|)) (max 0 (s - |y - c|)) := by
      simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hq]
    _ ≤ q * dist x y := mul_le_mul_of_nonneg_left (by simpa using hmax.dist_le_mul x y) hq.le
    _ = (Real.toNNReal q : ℝ) * dist x y := by rw [Real.toNNReal_of_nonneg hq.le]; rfl

theorem tent_support (q c s : ℝ) : HasCompactSupport (chordTent q c s) := by
  apply HasCompactSupport.intro' (isCompact_Icc (a := c - s) (b := c + s)) isClosed_Icc
  intro t ht
  have hn : ¬ |t - c| ≤ s := by
    intro hh
    have hab := abs_le.mp hh
    apply ht
    constructor <;> linarith
  simp [chordTent, hn]

theorem tent_nonneg (q c s : ℝ) (hq : 0 < q) (hs : 0 < s ∧ s ≤ Real.pi / q) :
    ∀ t, 0 ≤ chordTent q c s t := by
  intro t
  unfold chordTent
  split_ifs with ht
  · apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · have hqs : q * s ≤ Real.pi := by
        have := (le_div_iff₀ hq).mp hs.2
        nlinarith
      nlinarith [abs_nonneg (t - c)]
  · exact le_rfl

/-- A Wronskian primitive avoids differentiating the tent across its three corners. -/
theorem sine_integral (a b l r : ℝ) (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) :
    (∫ t in l..r, sin (a * t + b) * (deriv (deriv η) t + a ^ 2 * η t)) =
      (sin (a * r + b) * deriv η r - a * cos (a * r + b) * η r) -
      (sin (a * l + b) * deriv η l - a * cos (a * l + b) * η l) := by
  have hd : Differentiable ℝ η := hη.differentiable (by simp)
  have hηd : ContDiff ℝ ∞ (deriv η) := (contDiff_infty_iff_deriv.mp hη).2
  have hdd : Differentiable ℝ (deriv η) := hηd.differentiable (by simp)
  have hηdd : Continuous (deriv (deriv η)) :=
    (contDiff_infty_iff_deriv.mp hηd).2.continuous
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    have ha : HasDerivAt (fun t : ℝ => a * t + b) a t := by
      convert ((hasDerivAt_id t).const_mul a).add_const b using 1 <;> simp
    have hh := (((ha.sin).mul (hdd t).hasDerivAt).sub
      (((ha.cos).const_mul a).mul (hd t).hasDerivAt))
    convert hh using 1 <;> ring
  · exact ((by fun_prop : Continuous (fun t : ℝ => sin (a * t + b))).mul
      (hηdd.add (hη.continuous.const_mul (a ^ 2)))).intervalIntegrable l r

theorem tent_distribution (q c s : ℝ) (hq : 0 < q) (hs : 0 < s)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) :
    (∫ t : ℝ, chordTent q c s t * (deriv (deriv η) t + q ^ 2 * η t)) =
      q * (η (c - s) + η (c + s)) - 2 * q * cos (q * s) * η c := by
  have hleft (t : ℝ) (ht : t ∈ Icc (c - s) c) :
      chordTent q c s t = sin (q * t + q * (s - c)) := by
    have hat : |t - c| = c - t := by rw [abs_of_nonpos (by linarith [ht.2])]; ring
    have hts : |t - c| ≤ s := by rw [hat]; linarith [ht.1]
    unfold chordTent
    rw [if_pos hts, hat]
    congr 1 <;> ring
  have hright (t : ℝ) (ht : t ∈ Icc c (c + s)) :
      chordTent q c s t = sin (-q * t + q * (s + c)) := by
    have hat : |t - c| = t - c := abs_of_nonneg (by linarith [ht.1])
    have hts : |t - c| ≤ s := by rw [hat]; linarith [ht.2]
    unfold chordTent
    rw [if_pos hts, hat]
    congr 1 <;> ring
  have hzero : chordTent q c s (c - s) = 0 := by
    rw [hleft (c - s) ⟨le_rfl, by linarith⟩]
    have hz : q * (c - s) + q * (s - c) = 0 := by ring
    simp [hz]
  have hsupport : Function.support
      (fun t => chordTent q c s t * (deriv (deriv η) t + q ^ 2 * η t)) ⊆ Ioc (c - s) (c + s) := by
    intro t ht
    have hne : chordTent q c s t ≠ 0 := (mul_ne_zero_iff.mp ht).1
    have hab : |t - c| ≤ s := by
      by_contra hh
      exact hne (by simp [chordTent, hh])
    have hab' := abs_le.mp hab
    refine ⟨lt_of_le_of_ne (by linarith) ?_, by linarith⟩
    intro heq
    subst t
    exact hne hzero
  have hcont : Continuous (fun t => chordTent q c s t * (deriv (deriv η) t + q ^ 2 * η t)) :=
    (tent_lipschitz q c s hq).continuous.mul
      (((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hη).2).2.continuous).add
        (hη.continuous.const_mul (q ^ 2)))
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupport,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (c - s) c) (hcont.intervalIntegrable c (c + s))]
  have hl : (∫ t in (c - s)..c, chordTent q c s t * (deriv (deriv η) t + q ^ 2 * η t)) =
      (∫ t in (c - s)..c, sin (q * t + q * (s - c)) * (deriv (deriv η) t + q ^ 2 * η t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [hleft t (by simpa [uIcc_of_le (show c - s ≤ c by linarith)] using ht)]
  have hr : (∫ t in c..(c + s), chordTent q c s t * (deriv (deriv η) t + q ^ 2 * η t)) =
      (∫ t in c..(c + s), sin (-q * t + q * (s + c)) * (deriv (deriv η) t + (-q) ^ 2 * η t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [hright t (by simpa [uIcc_of_le (show c ≤ c + s by linarith)] using ht)]
    simp
  rw [hl, hr, sine_integral q (q * (s - c)) (c - s) c η hη,
    sine_integral (-q) (q * (s + c)) c (c + s) η hη]
  have h1 : q * c + q * (s - c) = q * s := by ring
  have h2 : q * (c - s) + q * (s - c) = 0 := by ring
  have h3 : -q * (c + s) + q * (s + c) = 0 := by ring
  have h4 : -q * c + q * (s + c) = q * s := by ring
  rw [h1, h2, h3, h4]
  simp only [sin_zero, cos_zero, zero_mul, mul_one]
  ring

theorem slice_O31_proved (q : ℝ) (hq : 0 < q) (c s : ℝ) (hs : 0 < s ∧ s ≤ Real.pi / q) :
    (∀ t, 0 ≤ chordTent q c s t) ∧ HasCompactSupport (chordTent q c s) ∧
    LipschitzWith (Real.toNNReal q) (chordTent q c s) ∧
    (∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      (∫ t : ℝ, chordTent q c s t * (deriv (deriv η) t + q ^ 2 * η t)) =
        q * (η (c - s) + η (c + s)) - 2 * q * cos (q * s) * η c) :=
  ⟨tent_nonneg q c s hq hs, tent_support q c s, tent_lipschitz q c s hq,
    fun η hη _ => tent_distribution q c s hq hs.1 η hη⟩

end GKSharp.Proofs.ChordTent

#print axioms GKSharp.Proofs.ChordTent.slice_O31_proved
