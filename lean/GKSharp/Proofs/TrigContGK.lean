/- trigonometrically q-convex functions (sec2_obstacle.tex l.58-60, "trigonometrically q-convex", Levin
Lecture 8) are continuous and have one-sided derivatives (port of the 018 tool TrigCont into the 019 tree; no cited input).
Copyright (C) Dave Goel 2026--now.

  Route: with A = arctan, sin(A a - A b) = cos(A a) cos(A b) (a - b), so the chord inequality of `TrigConvex q φ` at the
  points c + A(u)/q, divided by the three cosines, is the three-point convexity of g(u) = φ(c + A(u)/q)/cos(A u) on ℝ.
  Convex on ℝ ⇒ continuous; and φ(t) = g(tan(q(t-c))) cos(q(t-c)) near t = c. -/
import GKSharp.Defs.Potential

open Real Set Filter Topology

namespace GKSharp

/-- Trigonometric `q`-convexity, chord form: on every arc `x < t < y` with `q(y - x) < π`, `φ` lies below the
`q`-sinusoid through its end values (multiplied out by `sin(q(y - x)) > 0`). -/
def TrigConvex (q : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ x t y : ℝ, x < t → t < y → q * (y - x) < π →
    φ t * sin (q * (y - x)) ≤ φ x * sin (q * (y - t)) + φ y * sin (q * (t - x))

namespace TrigCont

/-- `sin(arctan a) = a cos(arctan a)`. -/
theorem sin_arctan_eq (a : ℝ) : sin (arctan a) = a * cos (arctan a) := by
  have h := tan_arctan a
  rw [tan_eq_sin_div_cos, div_eq_iff (cos_arctan_pos a).ne'] at h
  exact h

/-- `sin(arctan a - arctan b) = cos(arctan a) cos(arctan b) (a - b)`. -/
theorem sin_arctan_sub (a b : ℝ) : sin (arctan a - arctan b) = cos (arctan a) * cos (arctan b) * (a - b) := by
  rw [sin_sub, sin_arctan_eq a, sin_arctan_eq b]; ring

/-- The projective transform of a trigonometrically convex function is convex. -/
theorem convexOn_transform {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (htc : TrigConvex q φ) (c : ℝ) :
    ConvexOn ℝ univ (fun u => φ (c + arctan u / q) / cos (arctan u)) := by
  apply convexOn_of_slope_mono_adjacent convex_univ
  intro x y z _ _ hxy hyz
  have hX : c + arctan x / q < c + arctan y / q := by
    have := arctan_strictMono hxy; have : arctan x / q < arctan y / q := div_lt_div_of_pos_right this hq; linarith
  have hY : c + arctan y / q < c + arctan z / q := by
    have := arctan_strictMono hyz; have : arctan y / q < arctan z / q := div_lt_div_of_pos_right this hq; linarith
  have e1 : q * (c + arctan z / q - (c + arctan x / q)) = arctan z - arctan x := by field_simp; ring
  have e2 : q * (c + arctan z / q - (c + arctan y / q)) = arctan z - arctan y := by field_simp; ring
  have e3 : q * (c + arctan y / q - (c + arctan x / q)) = arctan y - arctan x := by field_simp; ring
  have hlen : q * (c + arctan z / q - (c + arctan x / q)) < π := by
    rw [e1]; linarith [arctan_lt_pi_div_two z, neg_pi_div_two_lt_arctan x]
  have h := htc _ _ _ hX hY hlen
  rw [e1, e2, e3, sin_arctan_sub, sin_arctan_sub, sin_arctan_sub] at h
  set PX := φ (c + arctan x / q)
  set PT := φ (c + arctan y / q)
  set PY := φ (c + arctan z / q)
  have hcx := cos_arctan_pos x
  have hcy := cos_arctan_pos y
  have hcz := cos_arctan_pos z
  have key : PT / cos (arctan y) * (z - x) ≤ PX / cos (arctan x) * (z - y) + PY / cos (arctan z) * (y - x) := by
    have hnum : PT * (cos (arctan z) * cos (arctan x) * (z - x))
        - (PX * (cos (arctan z) * cos (arctan y) * (z - y)) + PY * (cos (arctan y) * cos (arctan x) * (y - x))) ≤ 0 := by
      linarith
    have hden : 0 < cos (arctan x) * cos (arctan y) * cos (arctan z) := by positivity
    have hiden : PT / cos (arctan y) * (z - x) - (PX / cos (arctan x) * (z - y) + PY / cos (arctan z) * (y - x))
        = (PT * (cos (arctan z) * cos (arctan x) * (z - x))
          - (PX * (cos (arctan z) * cos (arctan y) * (z - y)) + PY * (cos (arctan y) * cos (arctan x) * (y - x))))
          / (cos (arctan x) * cos (arctan y) * cos (arctan z)) := by
      field_simp
    have : PT / cos (arctan y) * (z - x) - (PX / cos (arctan x) * (z - y) + PY / cos (arctan z) * (y - x)) ≤ 0 := by
      rw [hiden]; exact div_nonpos_of_nonpos_of_nonneg hnum hden.le
    linarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [key]

/-- **A trigonometrically convex function is continuous.** -/
theorem trigConvex_continuous {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (htc : TrigConvex q φ) : Continuous φ := by
  rw [continuous_iff_continuousAt]
  intro t0
  set g : ℝ → ℝ := fun u => φ (t0 + arctan u / q) / cos (arctan u) with hg
  have hgc : Continuous g := by
    have := (convexOn_transform hq htc t0).continuousOn_interior
    rw [interior_univ] at this
    exact continuousOn_univ.mp this
  have hcont : ContinuousAt (fun t => g (tan (q * (t - t0))) * cos (q * (t - t0))) t0 := by
    have htan : ContinuousAt (fun t => tan (q * (t - t0))) t0 := by
      apply ContinuousAt.comp (g := tan) _ (by fun_prop)
      rw [continuousAt_tan]; simp
    exact (hgc.continuousAt.comp htan).mul (by fun_prop)
  refine hcont.congr ?_
  have hδ : (0:ℝ) < π / (2 * q) := by positivity
  filter_upwards [Metric.ball_mem_nhds t0 hδ] with t ht
  rw [Metric.mem_ball, Real.dist_eq] at ht
  have hθ : |q * (t - t0)| < π / 2 := by
    rw [abs_mul, abs_of_pos hq]
    have := mul_lt_mul_of_pos_left ht hq
    rwa [show q * (π / (2 * q)) = π / 2 by field_simp] at this
  have h1 : -(π / 2) < q * (t - t0) := by linarith [neg_abs_le (q * (t - t0))]
  have h2 : q * (t - t0) < π / 2 := lt_of_le_of_lt (le_abs_self _) hθ
  have hcos : 0 < cos (q * (t - t0)) := cos_pos_of_mem_Ioo ⟨h1, h2⟩
  simp only [hg, arctan_tan h1 h2]
  rw [show t0 + q * (t - t0) / q = t by field_simp; ring, div_mul_cancel₀ _ hcos.ne']

/-- Near `x`, `φ(t) = g(tan(q(t-x))) cos(q(t-x))` with `g` the projective transform at `x`. -/
theorem eventually_eq_transform {q : ℝ} (hq : 0 < q) (φ : ℝ → ℝ) (x : ℝ) :
    φ =ᶠ[𝓝 x] fun t => φ (x + arctan (tan (q * (t - x))) / q) / cos (arctan (tan (q * (t - x))))
      * cos (q * (t - x)) := by
  have hδ : (0:ℝ) < π / (2 * q) := by positivity
  filter_upwards [Metric.ball_mem_nhds x hδ] with t ht
  rw [Metric.mem_ball, Real.dist_eq] at ht
  have hθ : |q * (t - x)| < π / 2 := by
    rw [abs_mul, abs_of_pos hq]
    have := mul_lt_mul_of_pos_left ht hq
    rwa [show q * (π / (2 * q)) = π / 2 by field_simp] at this
  have h1 : -(π / 2) < q * (t - x) := by linarith [neg_abs_le (q * (t - x))]
  have h2 : q * (t - x) < π / 2 := lt_of_le_of_lt (le_abs_self _) hθ
  have hcos : 0 < cos (q * (t - x)) := cos_pos_of_mem_Ioo ⟨h1, h2⟩
  rw [arctan_tan h1 h2, show x + q * (t - x) / q = t by field_simp; ring, div_mul_cancel₀ _ hcos.ne']

/-- `t ↦ tan(q(t-x))` has derivative `q` at `x`. -/
theorem hasDerivAt_tan_lin {q : ℝ} (x : ℝ) : HasDerivAt (fun t => tan (q * (t - x))) q x := by
  have hlin : HasDerivAt (fun t : ℝ => q * (t - x)) q x := by
    simpa using ((hasDerivAt_id x).sub_const x).const_mul q
  have htan := (Real.hasDerivAt_tan (x := q * (x - x)) (by simp)).comp x hlin
  refine (htan.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  · simp
  · rfl

/-- **A trigonometrically convex function has finite one-sided derivatives everywhere.** -/
theorem trigConvex_one_sided {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (htc : TrigConvex q φ) (x : ℝ) :
    ∃ dl dr : ℝ, HasDerivWithinAt φ dl (Iic x) x ∧ HasDerivWithinAt φ dr (Ici x) x := by
  set g : ℝ → ℝ := fun u => φ (x + arctan u / q) / cos (arctan u) with hg
  have hconv := convexOn_transform hq htc x
  have hint : (0:ℝ) ∈ interior univ := by simp
  have hgr := (hconv.hasDerivWithinAt_rightDeriv_of_mem_interior hint).Ici_of_Ioi
  have hgl := (hconv.hasDerivWithinAt_leftDeriv_of_mem_interior hint).Iic_of_Iio
  have hh := hasDerivAt_tan_lin (q := q) x
  have hcos : HasDerivAt (fun t => cos (q * (t - x))) (-sin (q * (x - x)) * q) x := by
    have hlin : HasDerivAt (fun t : ℝ => q * (t - x)) q x := by
      simpa using ((hasDerivAt_id x).sub_const x).const_mul q
    exact (Real.hasDerivAt_cos _).comp x hlin
  have heq := eventually_eq_transform hq φ x
  have hx0 : (0:ℝ) = tan (q * (x - x)) := by simp
  have hδ : (0:ℝ) < π / (2 * q) := by positivity
  have hqδ : q * (π / (2 * q)) = π / 2 := by field_simp
  -- left: on `Ioc (x - δ) x` the map lands in `Iic 0`; right: on `Ico x (x + δ)` it lands in `Ici 0`
  have hmapsL : MapsTo (fun t => tan (q * (t - x))) (Ioc (x - π / (2 * q)) x) (Iic 0) := by
    intro t ht
    have h1 : -(π / 2) ≤ q * (t - x) := by nlinarith [ht.1]
    exact tan_nonpos_of_nonpos_of_neg_pi_div_two_le (by nlinarith [ht.2]) h1
  have hmapsR : MapsTo (fun t => tan (q * (t - x))) (Ico x (x + π / (2 * q))) (Ici 0) := by
    intro t ht
    have h1 : q * (t - x) ≤ π / 2 := by nlinarith [ht.2]
    exact tan_nonneg_of_nonneg_of_le_pi_div_two (by nlinarith [ht.1]) h1
  have hcL := (hgl.comp_of_eq x hh.hasDerivWithinAt hmapsL hx0).mul hcos.hasDerivWithinAt
  have hcR := (hgr.comp_of_eq x hh.hasDerivWithinAt hmapsR hx0).mul hcos.hasDerivWithinAt
  have hleft := (hcL.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds).mono_of_mem_nhdsWithin
    (s := Iic x) (Ioc_mem_nhdsLE (by linarith : x - π / (2 * q) < x))
  have hright := (hcR.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds).mono_of_mem_nhdsWithin
    (s := Ici x) (Ico_mem_nhdsGE (by linarith : x < x + π / (2 * q)))
  exact ⟨_, _, hleft, hright⟩


end TrigCont

end GKSharp
