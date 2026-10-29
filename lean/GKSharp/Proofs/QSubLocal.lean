/- q-subtrigonometric continuity and local chords for every q>0.
Adapted from the SectorGK/TrigContGK proofs. Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.SectorLocal

open Real Metric Set Filter Topology MeasureTheory
namespace GKSharp.AngularLocal
open GKSharp SectorGK TrigCont

/-- Chord comparison restricted only by the trigonometric and geometric sector openings. -/
def LocalTrigConvex (q : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ x t y : ℝ, x < t → t < y → q * (y - x) < π → y - x < 2 * π →
    φ t * sin (q * (y - x)) ≤
      φ x * sin (q * (y - t)) + φ y * sin (q * (t - x))

theorem qsub_local_trigConvex {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ}
    (hφ : QSubtrig q φ) : LocalTrigConvex q φ := by
  set V : ℂ → EReal := fun ζ => ((angularPotential q φ ζ : ℝ) : EReal) with hVdef
  have hV : IsSubharmonicOn ({0}ᶜ : Set ℂ) V := hφ.2
  have hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → z ≠ 0 →
      V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z := by
    intro r z hr _
    simp only [hVdef, angularPotential]
    rw [← EReal.coe_mul, Complex.arg_real_mul z hr, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, mul_rpow hr.le (norm_nonneg z)]
    congr 1; ring
  have hval : ∀ θ : ℝ, V (Complex.exp ((θ : ℂ) * Complex.I)) = ((φ θ : ℝ) : EReal) := by
    intro θ
    simp only [hVdef, angularPotential, Complex.norm_exp_ofReal_mul_I,
      one_rpow, one_mul, Complex.arg_exp_mul_I]
    rw [toIocMod, hφ.1.sub_zsmul_eq]
  intro x t y hxt hty hlen hangle
  have hh := sector_comparison_punct_local hq hV hhom (hxt.trans hty) hlen hangle
    (le_of_eq (hval x)) (le_of_eq (hval y)) t hxt hty
  rw [hval t, EReal.coe_le_coe_iff] at hh
  exact (le_div_iff₀ (sin_len_pos hq (hxt.trans hty) hlen)).mp hh

theorem qsub_centered_small {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) :
    ∃ L : ℝ, 0 < L ∧ ∀ t d : ℝ, 0 < d → d < L →
      2 * cos (q * d) * φ t ≤ φ (t - d) + φ (t + d) := by
  refine ⟨min (π / 2) (π / (4 * q)), by positivity, ?_⟩
  intro t d hd hsmall
  have hdπ : d < π := lt_trans (lt_of_lt_of_le hsmall (min_le_left _ _)) (by linarith [pi_pos])
  have hqd : q * (2 * d) < π := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 4 * q)).mp
      (lt_of_lt_of_le hsmall (min_le_right _ _))
    nlinarith [pi_pos]
  have hh := qsub_local_trigConvex hq hφ (t - d) t (t + d)
    (by linarith) (by linarith)
    (by rw [show t + d - (t - d) = 2 * d by ring]; exact hqd)
    (by linarith)
  rw [show t + d - (t - d) = 2 * d by ring,
    show t + d - t = d by ring, show t - (t - d) = d by ring,
    show q * (2 * d) = 2 * (q * d) by ring, sin_two_mul] at hh
  have hsin : 0 < sin (q * d) :=
    sin_pos_of_pos_of_lt_pi (mul_pos hq hd) (by nlinarith [mul_pos hq hd])
  have hh' : (2 * cos (q * d) * φ t) * sin (q * d) ≤
      (φ (t - d) + φ (t + d)) * sin (q * d) := by linear_combination hh
  exact le_of_mul_le_mul_right hh' hsin

theorem convexOn_transform_local {q : ℝ} (hq : 0 < q) (hqp : q < π / 2)
    {φ : ℝ → ℝ} (htc : LocalTrigConvex q φ) (c : ℝ) :
    ConvexOn ℝ (Ioo (tan (-q)) (tan q)) (fun u => φ (c + arctan u / q) / cos (arctan u)) := by
  apply convexOn_of_slope_mono_adjacent (convex_Ioo _ _)
  intro x y z hx hz hxy hyz
  have hX : c + arctan x / q < c + arctan y / q := by
    have := arctan_strictMono hxy; have : arctan x / q < arctan y / q := div_lt_div_of_pos_right this hq; linarith
  have hY : c + arctan y / q < c + arctan z / q := by
    have := arctan_strictMono hyz; have : arctan y / q < arctan z / q := div_lt_div_of_pos_right this hq; linarith
  have e1 : q * (c + arctan z / q - (c + arctan x / q)) = arctan z - arctan x := by field_simp; ring
  have e2 : q * (c + arctan z / q - (c + arctan y / q)) = arctan z - arctan y := by field_simp; ring
  have e3 : q * (c + arctan y / q - (c + arctan x / q)) = arctan y - arctan x := by field_simp; ring
  have hlen : q * (c + arctan z / q - (c + arctan x / q)) < π := by
    rw [e1]; linarith [arctan_lt_pi_div_two z, neg_pi_div_two_lt_arctan x]
  have hx' : -q < arctan x := by
    have hh := arctan_strictMono hx.1
    rwa [arctan_tan (by linarith) (by linarith [pi_pos])] at hh
  have hz' : arctan z < q := by
    have hh := arctan_strictMono hz.2
    rwa [arctan_tan (by linarith [pi_pos]) hqp] at hh
  have hangle : (c + arctan z / q) - (c + arctan x / q) < 2 * π := by
    have hxq : -1 < arctan x / q := (lt_div_iff₀ hq).2 (by nlinarith)
    have hzq : arctan z / q < 1 := (div_lt_iff₀ hq).2 (by nlinarith)
    linarith [pi_gt_three]
  have h := htc _ _ _ hX hY hlen hangle
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

/-- The projective transform need only be convex in a neighborhood of zero to prove continuity at c. -/
theorem local_trigConvex_continuous {q : ℝ} (hq : 0 < q) (hqp : q < π / 2)
    {φ : ℝ → ℝ} (htc : LocalTrigConvex q φ) : Continuous φ := by
  rw [continuous_iff_continuousAt]
  intro t0
  set g : ℝ → ℝ := fun u => φ (t0 + arctan u / q) / cos (arctan u) with hg
  have hgc : ContinuousAt g 0 := by
    have hh := (convexOn_transform_local hq hqp htc t0).continuousOn_interior
    rw [interior_Ioo] at hh
    have hp : 0 < tan q := tan_pos_of_pos_of_lt_pi_div_two hq hqp
    have hzero : (0 : ℝ) ∈ Ioo (tan (-q)) (tan q) := by
      rw [tan_neg]
      exact ⟨by linarith, hp⟩
    exact hh.continuousAt (isOpen_Ioo.mem_nhds hzero)
  have hcont : ContinuousAt (fun t => g (tan (q * (t - t0))) * cos (q * (t - t0))) t0 := by
    have htan : ContinuousAt (fun t => tan (q * (t - t0))) t0 := by
      apply ContinuousAt.comp (g := tan) _ (by fun_prop)
      rw [continuousAt_tan]; simp
    have hgc' : ContinuousAt g (tan (q * (t0 - t0))) := by simpa using hgc
    have hcompose := ContinuousAt.comp (f := fun t : ℝ => tan (q * (t - t0)))
      (g := g) hgc' htan
    exact hcompose.mul (by fun_prop)
  refine hcont.congr ?_
  have hδ : (0 : ℝ) < π / (2 * q) := by positivity
  filter_upwards [Metric.ball_mem_nhds t0 hδ] with t ht
  rw [Metric.mem_ball, Real.dist_eq] at ht
  have hθ : |q * (t - t0)| < π / 2 := by
    rw [abs_mul, abs_of_pos hq]
    have hh := mul_lt_mul_of_pos_left ht hq
    rwa [show q * (π / (2 * q)) = π / 2 by field_simp] at hh
  have h1 : -(π / 2) < q * (t - t0) := by linarith [neg_abs_le (q * (t - t0))]
  have h2 : q * (t - t0) < π / 2 := lt_of_le_of_lt (le_abs_self _) hθ
  have hcos : 0 < cos (q * (t - t0)) := cos_pos_of_mem_Ioo ⟨h1, h2⟩
  simp only [hg, arctan_tan h1 h2]
  rw [show t0 + q * (t - t0) / q = t by field_simp; ring,
    div_mul_cancel₀ _ hcos.ne']

/-- Continuity for the entire frozen O17 range, with no small-q gap. -/
theorem qsub_continuous {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) :
    Continuous φ := by
  by_cases hlarge : 1 / 2 < q
  · exact SectorGK.qsubtrig_continuous hlarge hφ
  · exact local_trigConvex_continuous hq (by linarith [pi_gt_three])
      (qsub_local_trigConvex hq hφ)

end GKSharp.AngularLocal
#print axioms GKSharp.AngularLocal.qsub_continuous
#print axioms GKSharp.AngularLocal.qsub_centered_small

