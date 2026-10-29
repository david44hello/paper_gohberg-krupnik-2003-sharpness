/- homogeneous functions subharmonic OFF the origin — sector comparison, trig convexity, continuity of a
q-subtrigonometric profile, for every q > 1/2 (sec2_obstacle.tex l.54-60, Definition 2.1 as printed: punctured plane).
Copyright (C) Dave Goel 2026--now.

  The 018 tool (Sector.sector_comparison) assumed V subharmonic on all of ℂ and 1/2 < q < 1. Definition 2.1 only gives
  subharmonicity on ℂ \ {0}. Change: the maximum principle runs on the closed ANNULAR sector r₀ ≤ |z| ≤ R, which avoids
  the origin, and the comparison function gets a third term ε Re((z e^{-iμ})^{-q}) = ε r^{-q} cos qθ ≥ 0, harmonic, which
  beats the bound r₀^q sup V on the inner arc for small r₀. q < 1 was never needed; q > 1/2 keeps the arc shorter than 2π.
  Maximum principle (part A): for v upper semicontinuous on a compact K, sub-mean on discs in K ∩ U, and w mean-value on
  discs in U, a maximum of v - w + δ‖z‖² at an interior point contradicts circleAverage ‖·‖² c ρ = ‖c‖² + ρ² > ‖c‖². -/
import GKSharp.Proofs.LocGlobGK
import GKSharp.Proofs.TrigContGK
import GKSharp.Proofs.SubharmonicBasic

open Real Metric Set Filter Topology MeasureTheory

namespace GKSharp

namespace SectorGK

open SubharmonicBasic

/-! ## Part A: truncations on a domain; maximum principle on a compact set -/

/-- The truncation of a function subharmonic on `Ω` is upper semicontinuous on `Ω`. -/
theorem trunc_uscOn {Ω : Set ℂ} {V : ℂ → EReal} (hV : IsSubharmonicOn Ω V) (n : ℕ) :
    UpperSemicontinuousOn (fun z => potentialTrunc n (V z)) Ω := by
  intro z hz y hy
  have hne : max (V z) (-(n : EReal)) ≠ ⊤ := max_ne_top (hV.1 z hz) (by simp)
  have hnb : max (V z) (-(n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (le_max_right _ _)
  have hy' : max (V z) (-(n : EReal)) < (y : EReal) := by
    have : ((potentialTrunc n (V z) : ℝ) : EReal) < (y : EReal) := EReal.coe_lt_coe_iff.mpr hy
    unfold potentialTrunc at this; rwa [EReal.coe_toReal hne hnb] at this
  have h1 : V z < (y : EReal) := lt_of_le_of_lt (le_max_left _ _) hy'
  have h2 : -(n : EReal) < (y : EReal) := lt_of_le_of_lt (le_max_right _ _) hy'
  filter_upwards [hV.2.1 z hz y h1] with z' hz'
  have hm : max (V z') (-(n : EReal)) < (y : EReal) := max_lt hz' h2
  have hne' : max (V z') (-(n : EReal)) ≠ ⊤ := ne_top_of_lt hm
  have hnb' : max (V z') (-(n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (le_max_right _ _)
  unfold potentialTrunc
  rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal hne' hnb']
  exact hm

/-- The truncation of a function subharmonic on `Ω` is integrable on every circle lying in `Ω`. -/
theorem trunc_circleIntegrable_on {Ω : Set ℂ} {V : ℂ → EReal} (hV : IsSubharmonicOn Ω V) (n : ℕ) {c : ℂ} {r : ℝ}
    (hs : sphere c |r| ⊆ Ω) : CircleIntegrable (fun z => potentialTrunc n (V z)) c r := by
  have husc := trunc_uscOn hV n
  have hcomp : UpperSemicontinuous (fun θ : ℝ => potentialTrunc n (V (circleMap c r θ))) := by
    intro θ y hy
    have hmem : circleMap c r θ ∈ Ω := hs (circleMap_mem_sphere' c r θ)
    have htend : Tendsto (circleMap c r) (𝓝 θ) (𝓝[Ω] (circleMap c r θ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨(continuous_circleMap c r).continuousAt,
        Eventually.of_forall fun θ' => hs (circleMap_mem_sphere' c r θ')⟩
    exact htend.eventually (husc _ hmem y hy)
  obtain ⟨B, hB⟩ := (hcomp.upperSemicontinuousOn (Icc 0 (2 * π))).bddAbove_of_isCompact isCompact_Icc
  have hmeas : Measurable (fun θ : ℝ => potentialTrunc n (V (circleMap c r θ))) := hcomp.measurable
  unfold CircleIntegrable
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le two_pi_pos.le]
  refine Measure.integrableOn_of_bounded (M := max B n) measure_Icc_lt_top.ne hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Eventually.of_forall (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have hup : potentialTrunc n (V (circleMap c r θ)) ≤ B := hB ⟨θ, hθ, rfl⟩
  have hlo := trunc_ge (hV.1 _ (hs (circleMap_mem_sphere' c r θ))) n
  constructor
  · have : -(max B (n : ℝ)) ≤ -(n : ℝ) := neg_le_neg (le_max_right _ _)
    linarith
  · exact le_trans hup (le_max_left _ _)

/-- The unit circle avoids the origin. -/
theorem sphere_one_subset_compl : sphere (0 : ℂ) 1 ⊆ ({0}ᶜ : Set ℂ) := by
  intro z hz h0
  rw [Set.mem_singleton_iff.mp h0, mem_sphere_zero_iff_norm, norm_zero] at hz
  exact zero_ne_one hz

/-- A real upper bound on the unit circle for a function subharmonic off the origin. -/
theorem exists_bound_sphere_on {V : ℂ → EReal} (hV : IsSubharmonicOn ({0}ᶜ : Set ℂ) V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ sphere (0:ℂ) 1, V z ≤ B := by
  obtain ⟨z0, hz0, hmax⟩ := (hV.2.1.mono sphere_one_subset_compl).exists_isMaxOn ⟨1, by simp⟩ (isCompact_sphere 0 1)
  refine ⟨max (V z0).toReal 0, le_max_right _ _, fun z hz => ?_⟩
  refine le_trans (hmax hz) ?_
  induction h : V z0 using EReal.rec with
  | bot => exact bot_le
  | coe v => simp
  | top => exact absurd h (hV.1 z0 (sphere_one_subset_compl hz0))

/-- **Maximum principle on a compact set** (perturbed). `v` real, upper semicontinuous on `K` and sub-mean-value on the
discs inside `K ∩ U`; `w` continuous on `K` and mean-value on discs inside `U`. If every point of `K` where `v - w > 0`
has a closed disc around it inside `K ∩ U`, then `v - w ≤ 0` on `K`. -/
theorem max_principle_on {v w : ℂ → ℝ} {K U : Set ℂ} {R : ℝ}
    (hK : IsCompact K) (hKR : K ⊆ closedBall 0 R) (hv : UpperSemicontinuousOn v K)
    (hsub : ∀ c r, 0 < r → closedBall c r ⊆ K ∩ U → v c ≤ circleAverage v c r ∧ CircleIntegrable v c r)
    (hwc : ContinuousOn w K)
    (hw : ∀ c ρ, 0 < ρ → closedBall c ρ ⊆ U → circleAverage w c ρ = w c ∧ CircleIntegrable w c ρ)
    (hint : ∀ z ∈ K, 0 < v z - w z → ∃ ρ > 0, closedBall z ρ ⊆ K ∩ U) :
    ∀ z ∈ K, v z - w z ≤ 0 := by
  intro z0 hz0
  by_contra hneg
  push Not at hneg
  set m0 := v z0 - w z0 with hm0
  have hR0 : 0 ≤ R := by
    have := hKR hz0; rw [mem_closedBall, dist_zero_right] at this; linarith [norm_nonneg z0]
  set δ := m0 / (2 * (R ^ 2 + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδR : δ * R ^ 2 < m0 := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  set u : ℂ → ℝ := fun z => v z + (-w z + δ * ‖z‖ ^ 2) with hu
  have husc : UpperSemicontinuousOn u K :=
    hv.add (ContinuousOn.upperSemicontinuousOn
      (hwc.neg.add (continuousOn_const.mul (continuous_norm.pow 2).continuousOn)))
  obtain ⟨c, hcK, hmax⟩ := husc.exists_isMaxOn ⟨z0, hz0⟩ hK
  have hnorm : ∀ z ∈ K, ‖z‖ ^ 2 ≤ R ^ 2 := by
    intro z hz
    have := hKR hz; rw [mem_closedBall, dist_zero_right] at this
    exact pow_le_pow_left₀ (norm_nonneg z) this 2
  have huz0 : m0 ≤ u z0 := by simp only [hu]; nlinarith [sq_nonneg ‖z0‖]
  have hc_pos : 0 < v c - w c := by
    have h1 : u z0 ≤ u c := hmax hz0
    have h2 : δ * ‖c‖ ^ 2 ≤ δ * R ^ 2 := mul_le_mul_of_nonneg_left (hnorm c hcK) hδ0.le
    simp only [hu] at h1 h2 huz0 ⊢; linarith
  obtain ⟨ρ, hρ, hball⟩ := hint c hcK hc_pos
  obtain ⟨hwmean, hwint⟩ := hw c ρ hρ (hball.trans inter_subset_right)
  obtain ⟨hvc, hvint⟩ := hsub c ρ hρ hball
  have hsph : ∀ z ∈ sphere c |ρ|, z ∈ K := by
    intro z hz
    rw [abs_of_pos hρ] at hz
    exact (hball (sphere_subset_closedBall hz)).1
  have hnint : CircleIntegrable (fun z => ‖z‖ ^ 2) c ρ :=
    (continuous_norm.pow 2).continuousOn.circleIntegrable'
  have hnint' : CircleIntegrable (δ • fun z => ‖z‖ ^ 2) c ρ := hnint.const_smul
  have huint : CircleIntegrable u c ρ :=
    hvint.add ((hwint.neg).add hnint')
  have hle : circleAverage u c ρ ≤ u c :=
    circleAverage_mono_on_of_le_circle huint (fun z hz => hmax (hsph z hz))
  have hsplit : circleAverage u c ρ = circleAverage v c ρ - circleAverage w c ρ + δ * (‖c‖ ^ 2 + ρ ^ 2) := by
    have e1 : u = (v + δ • (fun z => ‖z‖ ^ 2)) - w := by
      funext z; simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, circleAverage_sub (hvint.add hnint') hwint, circleAverage_add hvint hnint',
      circleAverage_smul, LocGlob.circleAverage_normSq, smul_eq_mul]
    ring
  rw [hsplit, hwmean] at hle
  simp only [hu] at hle
  nlinarith [sq_pos_of_pos hρ]

/-! ## Part B: rotations, principal powers, the cone -/

/-- Rotation by `-μ`. -/
noncomputable def rot (μ : ℝ) (z : ℂ) : ℂ := Complex.exp (-(μ : ℂ) * Complex.I) * z

theorem norm_rot (μ : ℝ) (z : ℂ) : ‖rot μ z‖ = ‖z‖ := by
  have : -(μ : ℂ) * Complex.I = ((-μ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [rot, norm_mul, this, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem rot_exp (μ θ : ℝ) : rot μ (Complex.exp ((θ : ℂ) * Complex.I)) = Complex.exp (((θ - μ : ℝ) : ℂ) * Complex.I) := by
  rw [rot, ← Complex.exp_add]; congr 1; push_cast; ring

theorem eq_of_rot (μ : ℝ) (z : ℂ) : z = Complex.exp ((μ : ℂ) * Complex.I) * rot μ z := by
  rw [rot, ← mul_assoc, ← Complex.exp_add]; simp

theorem rot_ne_zero {μ : ℝ} {z : ℂ} (hz : z ≠ 0) : rot μ z ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) hz

/-- `Re(ζ^r) = ‖ζ‖^r cos(r arg ζ)`. -/
theorem cpow_re_eq {ζ : ℂ} (hζ : ζ ≠ 0) (r : ℝ) : (ζ ^ (r : ℂ)).re = ‖ζ‖ ^ r * cos (r * Complex.arg ζ) := by
  rw [Complex.cpow_def_of_ne_zero hζ, Complex.exp_re]
  have h1 : (Complex.log ζ * (r : ℂ)).re = Real.log ‖ζ‖ * r := by
    simp [Complex.mul_re, Complex.log_re, Complex.log_im]
  have h2 : (Complex.log ζ * (r : ℂ)).im = r * Complex.arg ζ := by
    simp [Complex.mul_im, Complex.log_re, Complex.log_im]; ring
  rw [h1, h2, Real.rpow_def_of_pos (norm_pos_iff.mpr hζ)]

/-- `Im(ζ^r) = ‖ζ‖^r sin(r arg ζ)`. -/
theorem cpow_im_eq {ζ : ℂ} (hζ : ζ ≠ 0) (r : ℝ) : (ζ ^ (r : ℂ)).im = ‖ζ‖ ^ r * sin (r * Complex.arg ζ) := by
  rw [Complex.cpow_def_of_ne_zero hζ, Complex.exp_im]
  have h1 : (Complex.log ζ * (r : ℂ)).re = Real.log ‖ζ‖ * r := by
    simp [Complex.mul_re, Complex.log_re, Complex.log_im]
  have h2 : (Complex.log ζ * (r : ℂ)).im = r * Complex.arg ζ := by
    simp [Complex.mul_im, Complex.log_re, Complex.log_im]; ring
  rw [h1, h2, Real.rpow_def_of_pos (norm_pos_iff.mpr hζ)]

/-- `Re((A - iB) ζ^r) = ‖ζ‖^r (A cos(r arg ζ) + B sin(r arg ζ))`. -/
theorem re_coef_cpow {ζ : ℂ} (hζ : ζ ≠ 0) (A B r : ℝ) :
    (((A : ℂ) - (B : ℂ) * Complex.I) * ζ ^ (r : ℂ)).re
      = ‖ζ‖ ^ r * (A * cos (r * Complex.arg ζ) + B * sin (r * Complex.arg ζ)) := by
  rw [Complex.mul_re, cpow_re_eq hζ, cpow_im_eq hζ]
  simp; ring

/-- The closed cone `{z : ‖z‖ cos α ≤ Re(rot μ z)}`: for `z ≠ 0` in it, `|arg(rot μ z)| ≤ α` (`0 < α < π`). -/
theorem abs_arg_le_of_cone {μ α : ℝ} (hα0 : 0 < α) (_hαπ : α < π) {z : ℂ} (hz : z ≠ 0)
    (hc : ‖z‖ * cos α ≤ (rot μ z).re) : |Complex.arg (rot μ z)| ≤ α := by
  have hζ := rot_ne_zero (μ := μ) hz
  have hcos : cos α ≤ cos |Complex.arg (rot μ z)| := by
    rw [Real.cos_abs, Complex.cos_arg hζ, norm_rot, le_div_iff₀ (norm_pos_iff.mpr hz)]; linarith
  by_contra h
  push Not at h
  have := cos_lt_cos_of_nonneg_of_le_pi hα0.le (Complex.abs_arg_le_pi _) h
  linarith

/-- On the boundary of the cone (`z ≠ 0`, equality), `arg(rot μ z) = ±α`. -/
theorem arg_eq_of_cone_bdry {μ α : ℝ} (hα0 : 0 < α) (hαπ : α < π) {z : ℂ} (hz : z ≠ 0)
    (hc : ‖z‖ * cos α = (rot μ z).re) : Complex.arg (rot μ z) = α ∨ Complex.arg (rot μ z) = -α := by
  have hζ := rot_ne_zero (μ := μ) hz
  have hcos : cos |Complex.arg (rot μ z)| = cos α := by
    rw [Real.cos_abs, Complex.cos_arg hζ, norm_rot, div_eq_iff (norm_pos_iff.mpr hz).ne']; linarith
  have habs : |Complex.arg (rot μ z)| = α :=
    injOn_cos ⟨abs_nonneg _, Complex.abs_arg_le_pi _⟩ ⟨hα0.le, hαπ.le⟩ hcos
  rcases abs_eq hα0.le |>.mp habs with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Points of the closed cone other than `0` are in the domain of the principal power. -/
theorem rot_mem_slitPlane {μ α : ℝ} (hα0 : 0 < α) (hαπ : α < π) {z : ℂ} (hz : z ≠ 0)
    (hc : ‖z‖ * cos α ≤ (rot μ z).re) : rot μ z ∈ Complex.slitPlane := by
  have harg := abs_arg_le_of_cone hα0 hαπ hz hc
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  have hre : (rot μ z).re < 0 := by
    rcases lt_or_eq_of_le h.1 with h1 | h1
    · exact h1
    · exact absurd (Complex.ext h1 h.2) (rot_ne_zero hz)
  have := Complex.arg_eq_pi_iff.mpr ⟨hre, h.2⟩
  rw [this, abs_of_pos pi_pos] at harg
  linarith



theorem analyticAt_rot (μ : ℝ) (z : ℂ) : AnalyticAt ℂ (rot μ) z := by
  unfold rot; exact analyticAt_const.mul analyticAt_id


/-- The interpolation identity: `A cos(q s) + B sin(q s)` equals the trig-convex chord at `t = μ + s`. -/
theorem chord_identity {q α s a b : ℝ} (hc : cos (q * α) ≠ 0) (hs : sin (q * α) ≠ 0) :
    (a + b) / (2 * cos (q * α)) * cos (q * s) + (b - a) / (2 * sin (q * α)) * sin (q * s)
      = (a * sin (q * (α - s)) + b * sin (q * (α + s))) / sin (q * (2 * α)) := by
  have e1 : q * (α - s) = q * α - q * s := by ring
  have e2 : q * (α + s) = q * α + q * s := by ring
  have e3 : q * (2 * α) = 2 * (q * α) := by ring
  rw [e1, e2, e3, sin_sub, sin_add, sin_two_mul]
  field_simp
  ring


theorem exp_mem_sphere (θ : ℝ) : Complex.exp ((θ : ℂ) * Complex.I) ∈ sphere (0:ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]

/-- `sin(q(y-x)) > 0` for `0 < q(y-x) < π`. -/
theorem sin_len_pos {q x y : ℝ} (hq : 0 < q) (hxy : x < y) (hlen : q * (y - x) < π) : 0 < sin (q * (y - x)) :=
  sin_pos_of_pos_of_lt_pi (mul_pos hq (by linarith)) hlen

/-- From the sector comparison with exact end values to the multiplied-out trig convexity inequality. -/
theorem trigConvex_of_comparison {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ}
    (hcmp : ∀ x t y : ℝ, x < t → t < y → q * (y - x) < π →
      φ t ≤ (φ x * sin (q * (y - t)) + φ y * sin (q * (t - x))) / sin (q * (y - x))) : TrigConvex q φ := by
  intro x t y hxt hty hlen
  have hs := sin_len_pos hq (hxt.trans hty) hlen
  have := hcmp x t y hxt hty hlen
  rwa [le_div_iff₀ hs] at this


/-- `V z = ‖z‖^q V(z/‖z‖)` for a `q`-homogeneous `V`, `z ≠ 0`. -/
theorem homog_split {q : ℝ} {V : ℂ → EReal}
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → z ≠ 0 → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z) {z : ℂ} (hz : z ≠ 0) :
    V z = ((‖z‖ ^ q : ℝ) : EReal) * V ((‖z‖⁻¹ : ℝ) * z) ∧ (‖z‖⁻¹ : ℝ) * z ∈ sphere (0:ℂ) 1 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hz' : ((‖z‖⁻¹ : ℝ) : ℂ) * z ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_pos.mpr hn).ne') hz
  refine ⟨?_, ?_⟩
  · rw [← hhom ‖z‖ _ hn hz', ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_mul]
  · rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hn,
      inv_mul_cancel₀ hn.ne']

/-- `cos(qθ) > 0` when `|θ| ≤ α` and `qα < π/2`. -/
theorem cos_pos_of_abs_le {q α θ : ℝ} (hq : 0 < q) (hθ : |θ| ≤ α) (hqα : q * α < π / 2) : 0 < cos (q * θ) := by
  have h := abs_le.mp hθ
  apply cos_pos_of_mem_Ioo
  constructor <;> nlinarith

/-- `cos(qα) ≤ cos(qθ)` when `|θ| ≤ α` and `qα ≤ π`. -/
theorem cos_le_cos_of_abs_le {q α θ : ℝ} (hq : 0 < q) (hθ : |θ| ≤ α) (hqα : q * α ≤ π) :
    cos (q * α) ≤ cos (q * θ) := by
  rw [← cos_abs (q * θ), abs_mul, abs_of_pos hq]
  exact cos_le_cos_of_nonneg_of_le_pi (by positivity) hqα (mul_le_mul_of_nonneg_left hθ hq.le)

/-- The comparison function of the punctured sector:
`w = Re((A - iB)(rot z)^q + ε (rot z)^{q'} + ε (rot z)^{-q})` (the last term controls the inner arc). -/
noncomputable def wfun2 (μ A B q q' ε : ℝ) (z : ℂ) : ℝ :=
  (((A : ℂ) - (B : ℂ) * Complex.I) * rot μ z ^ (q : ℂ) + (ε : ℂ) * rot μ z ^ (q' : ℂ) +
    (ε : ℂ) * rot μ z ^ ((-q : ℝ) : ℂ)).re

/-- Polar form of `wfun2`. -/
theorem wfun2_polar (μ A B q q' ε : ℝ) {z : ℂ} (hz : z ≠ 0) :
    wfun2 μ A B q q' ε z = ‖z‖ ^ q * (A * cos (q * Complex.arg (rot μ z)) + B * sin (q * Complex.arg (rot μ z)))
      + ε * (‖z‖ ^ q' * cos (q' * Complex.arg (rot μ z)))
      + ε * (‖z‖ ^ (-q) * cos (q * Complex.arg (rot μ z))) := by
  have hζ := rot_ne_zero (μ := μ) hz
  rw [wfun2, Complex.add_re, Complex.add_re, re_coef_cpow hζ, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    cpow_re_eq hζ q', cpow_re_eq hζ (-q), norm_rot, neg_mul, cos_neg]

theorem wfun2_analytic (μ A B q q' ε : ℝ) {z : ℂ} (hz : rot μ z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun z => ((A : ℂ) - (B : ℂ) * Complex.I) * rot μ z ^ (q : ℂ) + (ε : ℂ) * rot μ z ^ (q' : ℂ) +
      (ε : ℂ) * rot μ z ^ ((-q : ℝ) : ℂ)) z :=
  ((analyticAt_const.mul ((analyticAt_rot μ z).cpow analyticAt_const hz)).add
    (analyticAt_const.mul ((analyticAt_rot μ z).cpow analyticAt_const hz))).add
    (analyticAt_const.mul ((analyticAt_rot μ z).cpow analyticAt_const hz))

theorem wfun2_continuousAt (μ A B q q' ε : ℝ) {z : ℂ} (hz : rot μ z ∈ Complex.slitPlane) :
    ContinuousAt (wfun2 μ A B q q' ε) z :=
  Complex.continuous_re.continuousAt.comp (wfun2_analytic μ A B q q' ε hz).continuousAt

/-- Mean value property of `wfun2` on discs inside `{z : rot μ z ∈ slitPlane}`. -/
theorem wfun2_mean (μ A B q q' ε : ℝ) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall c ρ ⊆ {z | rot μ z ∈ Complex.slitPlane}) :
    circleAverage (wfun2 μ A B q q' ε) c ρ = wfun2 μ A B q q' ε c ∧ CircleIntegrable (wfun2 μ A B q q' ε) c ρ := by
  have hh : InnerProductSpace.HarmonicOnNhd (wfun2 μ A B q q' ε) (closedBall c |ρ|) := by
    intro z hz
    rw [abs_of_pos hρ] at hz
    exact (wfun2_analytic μ A B q q' ε (hball hz)).harmonicAt_re
  exact ⟨hh.circleAverage_eq, (hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable'⟩

/-! ## Part C: the sector comparison off the origin and its consequences -/

set_option maxHeartbeats 2000000 in
/-- **Sector comparison off the origin.** A `q`-homogeneous `V` (`q > 1/2`), subharmonic on `ℂ \ {0}` only, lies below
the `q`-sinusoid through its values at the ends of any arc of length `< π/q`. The maximum principle runs on the closed
annular sector `r₀ ≤ |z| ≤ R`, `|arg(z e^{-iμ})| ≤ α`, which avoids the origin; the comparison function carries
`ε r^{q'} cos q'θ` (`q < q'`, outer arc) and `ε r^{-q} cos qθ` (inner arc), both `≥ 0` on the sector. -/
theorem sector_comparison_punct {q : ℝ} (hq0 : 1 / 2 < q) {V : ℂ → EReal}
    (hV : IsSubharmonicOn ({0}ᶜ : Set ℂ) V)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → z ≠ 0 → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z)
    {x y a b : ℝ} (hxy : x < y) (hlen : q * (y - x) < π)
    (ha : V (Complex.exp ((x : ℂ) * Complex.I)) ≤ (a : EReal)) (hb : V (Complex.exp ((y : ℂ) * Complex.I)) ≤ (b : EReal))
    (t : ℝ) (ht : x < t) (ht' : t < y) :
    V (Complex.exp ((t : ℂ) * Complex.I)) ≤ (((a * sin (q * (y - t)) + b * sin (q * (t - x))) / sin (q * (y - x)) : ℝ) : EReal) := by
  have hq : 0 < q := by linarith
  set μ := (x + y) / 2 with hμ
  set α := (y - x) / 2 with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  have hqα : q * α < π / 2 := by rw [hα]; linarith
  have hαπ : α < π := by
    have h1 : α < π / (2 * q) := by rw [lt_div_iff₀ (by linarith)]; linarith
    have h2 : π / (2 * q) < π := by rw [div_lt_iff₀ (by linarith)]; nlinarith [pi_pos]
    linarith
  have hcqα : 0 < cos (q * α) := cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], hqα⟩
  have hsqα : 0 < sin (q * α) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  set A := (a + b) / (2 * cos (q * α)) with hA
  set B := (b - a) / (2 * sin (q * α)) with hB
  set q' := (q + π / (2 * α)) / 2 with hq'
  have hqq' : q < q' := by
    have : q < π / (2 * α) := by rw [lt_div_iff₀ (by linarith)]; linarith
    rw [hq']; linarith
  have hq'α : q' * α < π / 2 := by
    have : π / (2 * α) * α = π / 2 := by field_simp
    rw [hq']; nlinarith
  have hq'0 : 0 < q' := by linarith
  have hcq' : 0 < cos (q' * α) := cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], hq'α⟩
  obtain ⟨Bv, hBv0, hBv⟩ := exists_bound_sphere_on hV
  -- the conclusion for every ε > 0
  have key : ∀ ε : ℝ, 0 < ε → V (Complex.exp ((t : ℂ) * Complex.I)) ≤
      (((A * cos (q * (t - μ)) + B * sin (q * (t - μ))) + 2 * ε : ℝ) : EReal) := by
    intro ε hε
    set d := q' - q with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    set M := Bv + |A| + |B| with hM
    have hM0 : 0 ≤ M := by positivity
    set L := M / (ε * cos (q' * α)) + 1 with hL
    have hL0 : 0 < L := by rw [hL]; positivity
    set R := max 2 (L ^ (1 / d)) with hR
    have hR1 : 1 ≤ R := le_trans (by norm_num) (le_max_left _ _)
    have hR0 : 0 < R := by linarith
    have hRd : L ≤ R ^ d := by
      have h1 : L ^ (1 / d) ≤ R := le_max_right _ _
      have h2 : (L ^ (1 / d)) ^ d ≤ R ^ d := rpow_le_rpow (by positivity) h1 hd0.le
      rwa [← rpow_mul hL0.le, one_div_mul_cancel hd0.ne', rpow_one] at h2
    -- the inner radius
    set s := ε * cos (q * α) / (M + 1) with hs
    have hs0 : 0 < s := by positivity
    set r0 := min 1 ((s / 2) ^ (1 / (2 * q))) with hr0
    have hr00 : 0 < r0 := lt_min one_pos (rpow_pos_of_pos (by positivity) _)
    have hr01 : r0 ≤ 1 := min_le_left _ _
    have hr0s : r0 ^ (2 * q) ≤ s / 2 := by
      have h1 : r0 ≤ (s / 2) ^ (1 / (2 * q)) := min_le_right _ _
      have h2 : r0 ^ (2 * q) ≤ ((s / 2) ^ (1 / (2 * q))) ^ (2 * q) := rpow_le_rpow hr00.le h1 (by positivity)
      rwa [← rpow_mul (by positivity), one_div_mul_cancel (by positivity), rpow_one] at h2
    have hinner_key : r0 ^ q * M ≤ ε * (r0 ^ (-q) * cos (q * α)) := by
      have e1 : r0 ^ q = r0 ^ (-q) * r0 ^ (2 * q) := by rw [← rpow_add hr00]; congr 1; ring
      have e2 : s * (M + 1) = ε * cos (q * α) := by rw [hs, div_mul_cancel₀ _ (by positivity)]
      have h3 : r0 ^ (2 * q) * M ≤ ε * cos (q * α) := by
        calc r0 ^ (2 * q) * M ≤ s / 2 * M := mul_le_mul_of_nonneg_right hr0s hM0
          _ ≤ s * (M + 1) := by nlinarith
          _ = _ := e2
      have hrq : 0 < r0 ^ (-q) := rpow_pos_of_pos hr00 _
      rw [e1]
      calc r0 ^ (-q) * r0 ^ (2 * q) * M = r0 ^ (-q) * (r0 ^ (2 * q) * M) := by ring
        _ ≤ r0 ^ (-q) * (ε * cos (q * α)) := mul_le_mul_of_nonneg_left h3 hrq.le
        _ = ε * (r0 ^ (-q) * cos (q * α)) := by ring
    set n : ℕ := ⌈R ^ q * (|a| + |b|)⌉₊ with hn
    have hn' : R ^ q * (|a| + |b|) ≤ n := Nat.le_ceil _
    set v : ℂ → ℝ := fun z => potentialTrunc n (V z) with hv
    set w := wfun2 μ A B q q' ε with hw
    set K := {z : ℂ | ‖z‖ * cos α ≤ (rot μ z).re} ∩ closedBall 0 R ∩ {z : ℂ | r0 ≤ ‖z‖} with hK
    set U := {z : ℂ | rot μ z ∈ Complex.slitPlane} with hU
    have hrotc : Continuous (rot μ) := continuous_const.mul continuous_id
    have hKc : IsCompact K := ((isCompact_closedBall 0 R).inter_left
      (isClosed_le (continuous_norm.mul continuous_const) (Complex.continuous_re.comp hrotc))).inter_right
      (isClosed_le continuous_const continuous_norm)
    have hK0 : ∀ z ∈ K, z ≠ 0 := fun z hzK h0 => by
      have h2 : r0 ≤ ‖z‖ := hzK.2
      rw [h0, norm_zero] at h2; linarith
    have hKc0 : K ⊆ ({0}ᶜ : Set ℂ) := fun z hzK => Set.mem_compl_singleton_iff.mpr (hK0 z hzK)
    have hcqα' : cos (q * α) ≠ 0 := hcqα.ne'
    have hsqα' : sin (q * α) ≠ 0 := hsqα.ne'
    have hRq0 : 0 < R ^ q := rpow_pos_of_pos hR0 q
    have hn'' : R ^ q * |a| + R ^ q * |b| ≤ n := by rw [← mul_add]; exact hn'
    -- boundary estimates: the two rays
    have hray : ∀ z ∈ K, ‖z‖ * cos α = (rot μ z).re → v z - w z ≤ 0 := by
      intro z hzK heq
      have hz := hK0 z hzK
      have hzR : ‖z‖ ≤ R := by have := hzK.1.2; rwa [mem_closedBall, dist_zero_right] at this
      have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hRq : ‖z‖ ^ q ≤ R ^ q := rpow_le_rpow (norm_nonneg z) hzR hq.le
      have hzq : 0 < ‖z‖ ^ q := rpow_pos_of_pos hzn q
      have hexp : Complex.exp (((μ + Complex.arg (rot μ z) : ℝ) : ℂ) * Complex.I)
          = Complex.exp ((μ : ℂ) * Complex.I) * Complex.exp ((Complex.arg (rot μ z) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]; push_cast; ring_nf
      have hrep : z = ((‖z‖ : ℝ) : ℂ) * Complex.exp (((μ + Complex.arg (rot μ z) : ℝ) : ℂ) * Complex.I) := by
        calc z = Complex.exp ((μ : ℂ) * Complex.I) * rot μ z := eq_of_rot μ z
          _ = Complex.exp ((μ : ℂ) * Complex.I) * (((‖z‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg (rot μ z) : ℂ) * Complex.I)) := by
              rw [← norm_rot μ z, Complex.norm_mul_exp_arg_mul_I]
          _ = _ := by rw [hexp]; ring
      have hVrep : V z = ((‖z‖ ^ q : ℝ) : EReal) * V (Complex.exp (((μ + Complex.arg (rot μ z) : ℝ) : ℂ) * Complex.I)) := by
        rw [← hhom _ _ hzn (Complex.exp_ne_zero _), ← hrep]
      have hneg0 : 0 ≤ ε * (‖z‖ ^ (-q) * cos (q * α)) :=
        mul_nonneg hε.le (mul_nonneg (rpow_nonneg (norm_nonneg _) _) hcqα.le)
      have hpos0 : 0 ≤ ε * (‖z‖ ^ q' * cos (q' * α)) :=
        mul_nonneg hε.le (mul_nonneg (rpow_nonneg (norm_nonneg _) _) hcq'.le)
      rw [hw, wfun2_polar μ A B q q' ε hz]
      rcases arg_eq_of_cone_bdry hα0 hαπ hz heq with h | h
      · -- the ray through e^{iy}
        have hy : μ + Complex.arg (rot μ z) = y := by rw [h, hμ, hα]; ring
        rw [hy] at hVrep
        have hVz : V z ≤ ((‖z‖ ^ q * b : ℝ) : EReal) := by rw [hVrep]; exact ereal_mul_le hzq hb
        have h1 : ‖z‖ ^ q * (-|b|) ≤ ‖z‖ ^ q * b := mul_le_mul_of_nonneg_left (neg_abs_le b) hzq.le
        have h2 : ‖z‖ ^ q * |b| ≤ R ^ q * |b| := mul_le_mul_of_nonneg_right hRq (abs_nonneg b)
        have h3 : 0 ≤ R ^ q * |a| := mul_nonneg hRq0.le (abs_nonneg a)
        have hvz : v z ≤ ‖z‖ ^ q * b := trunc_le (hV.1 z hz) hVz n (by linarith)
        have hAB : A * cos (q * α) + B * sin (q * α) = b := by rw [hA, hB]; field_simp; ring
        rw [h, hAB]
        linarith
      · -- the ray through e^{ix}
        have hx : μ + Complex.arg (rot μ z) = x := by rw [h, hμ, hα]; ring
        rw [hx] at hVrep
        have hVz : V z ≤ ((‖z‖ ^ q * a : ℝ) : EReal) := by rw [hVrep]; exact ereal_mul_le hzq ha
        have h1 : ‖z‖ ^ q * (-|a|) ≤ ‖z‖ ^ q * a := mul_le_mul_of_nonneg_left (neg_abs_le a) hzq.le
        have h2 : ‖z‖ ^ q * |a| ≤ R ^ q * |a| := mul_le_mul_of_nonneg_right hRq (abs_nonneg a)
        have h3 : 0 ≤ R ^ q * |b| := mul_nonneg hRq0.le (abs_nonneg b)
        have hvz : v z ≤ ‖z‖ ^ q * a := trunc_le (hV.1 z hz) hVz n (by linarith)
        have hAB : A * cos (q * -α) + B * sin (q * -α) = a := by
          rw [mul_neg, cos_neg, sin_neg, hA, hB]; field_simp; ring
        rw [h, hAB]
        simp only [mul_neg, cos_neg]
        linarith
    -- the outer arc
    have houter : ∀ z ∈ K, ‖z‖ = R → v z - w z ≤ 0 := by
      intro z hzK hzR
      have hz := hK0 z hzK
      obtain ⟨hsplit, hsph⟩ := homog_split hhom hz
      have hzq : 0 < ‖z‖ ^ q := rpow_pos_of_pos (norm_pos_iff.mpr hz) q
      have hVz : V z ≤ ((‖z‖ ^ q * Bv : ℝ) : EReal) := by rw [hsplit]; exact ereal_mul_le hzq (hBv _ hsph)
      have hvz : v z ≤ ‖z‖ ^ q * Bv := trunc_le (hV.1 z hz) hVz n (by have := mul_nonneg hzq.le hBv0; linarith)
      set θ := Complex.arg (rot μ z) with hθdef
      have hθ : |θ| ≤ α := abs_arg_le_of_cone hα0 hαπ hz hzK.1.1
      have hcos : cos (q' * α) ≤ cos (q' * θ) := cos_le_cos_of_abs_le hq'0 hθ (by linarith [pi_pos])
      have hcosq : 0 < cos (q * θ) := cos_pos_of_abs_le hq hθ hqα
      have hA1 : -|A| ≤ A * cos (q * θ) := by
        have : |A * cos (q * θ)| ≤ |A| := by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg A) (abs_cos_le_one _)
        linarith [neg_abs_le (A * cos (q * θ))]
      have hB1 : -|B| ≤ B * sin (q * θ) := by
        have : |B * sin (q * θ)| ≤ |B| := by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg B) (abs_sin_le_one _)
        linarith [neg_abs_le (B * sin (q * θ))]
      have hRsplit : R ^ q' = R ^ q * R ^ d := by rw [← rpow_add hR0]; congr 1; rw [hd]; ring
      have hεL' : ε * cos (q' * α) * L = M + ε * cos (q' * α) := by rw [hL]; field_simp
      have hεL : M < ε * cos (q' * α) * L := by rw [hεL']; linarith [mul_pos hε hcq']
      rw [hw, wfun2_polar μ A B q q' ε hz, hzR]
      rw [hzR] at hvz
      have h3 : ε * (R ^ q' * cos (q' * α)) ≤ ε * (R ^ q' * cos (q' * θ)) := by
        apply mul_le_mul_of_nonneg_left _ hε.le
        exact mul_le_mul_of_nonneg_left hcos (by positivity)
      have h4 : R ^ q * (ε * cos (q' * α) * L) ≤ ε * (R ^ q' * cos (q' * α)) := by
        rw [hRsplit]
        have : ε * cos (q' * α) * L ≤ ε * cos (q' * α) * R ^ d := mul_le_mul_of_nonneg_left hRd (by positivity)
        calc R ^ q * (ε * cos (q' * α) * L) ≤ R ^ q * (ε * cos (q' * α) * R ^ d) :=
              mul_le_mul_of_nonneg_left this hRq0.le
          _ = ε * (R ^ q * R ^ d * cos (q' * α)) := by ring
      have h5 := mul_le_mul_of_nonneg_left (show -(|A| + |B|) ≤ A * cos (q * θ) + B * sin (q * θ) by linarith) hRq0.le
      have h6 := mul_lt_mul_of_pos_left hεL hRq0
      have h7 : 0 ≤ ε * (R ^ (-q) * cos (q * θ)) :=
        mul_nonneg hε.le (mul_nonneg (rpow_nonneg hR0.le _) hcosq.le)
      have hMe : R ^ q * M = R ^ q * Bv + R ^ q * (|A| + |B|) := by rw [hM]; ring
      linarith
    -- the inner arc
    have hinner : ∀ z ∈ K, ‖z‖ = r0 → v z - w z ≤ 0 := by
      intro z hzK hzr
      have hz := hK0 z hzK
      obtain ⟨hsplit, hsph⟩ := homog_split hhom hz
      have hzq : 0 < ‖z‖ ^ q := rpow_pos_of_pos (norm_pos_iff.mpr hz) q
      have hVz : V z ≤ ((‖z‖ ^ q * Bv : ℝ) : EReal) := by rw [hsplit]; exact ereal_mul_le hzq (hBv _ hsph)
      have hvz : v z ≤ ‖z‖ ^ q * Bv := trunc_le (hV.1 z hz) hVz n (by have := mul_nonneg hzq.le hBv0; linarith)
      set θ := Complex.arg (rot μ z) with hθdef
      have hθ : |θ| ≤ α := abs_arg_le_of_cone hα0 hαπ hz hzK.1.1
      have hA1 : -|A| ≤ A * cos (q * θ) := by
        have : |A * cos (q * θ)| ≤ |A| := by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg A) (abs_cos_le_one _)
        linarith [neg_abs_le (A * cos (q * θ))]
      have hB1 : -|B| ≤ B * sin (q * θ) := by
        have : |B * sin (q * θ)| ≤ |B| := by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg B) (abs_sin_le_one _)
        linarith [neg_abs_le (B * sin (q * θ))]
      have hc1 : 0 < cos (q' * θ) := cos_pos_of_abs_le hq'0 hθ hq'α
      have hc2 : cos (q * α) ≤ cos (q * θ) := cos_le_cos_of_abs_le hq hθ (by linarith [pi_pos])
      rw [hw, wfun2_polar μ A B q q' ε hz, hzr]
      rw [hzr] at hvz
      have hr0q : 0 < r0 ^ q := rpow_pos_of_pos hr00 q
      have hr0nq : 0 < r0 ^ (-q) := rpow_pos_of_pos hr00 _
      have h5 := mul_le_mul_of_nonneg_left (show -(|A| + |B|) ≤ A * cos (q * θ) + B * sin (q * θ) by linarith) hr0q.le
      have h6 : 0 ≤ ε * (r0 ^ q' * cos (q' * θ)) :=
        mul_nonneg hε.le (mul_nonneg (rpow_pos_of_pos hr00 _).le hc1.le)
      have h7 : ε * (r0 ^ (-q) * cos (q * α)) ≤ ε * (r0 ^ (-q) * cos (q * θ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc2 hr0nq.le) hε.le
      have hMe : r0 ^ q * M = r0 ^ q * Bv + r0 ^ q * (|A| + |B|) := by rw [hM]; ring
      linarith [hinner_key]
    -- points with v > w are interior
    have hint : ∀ z ∈ K, 0 < v z - w z → ∃ ρ > 0, closedBall z ρ ⊆ K ∩ U := by
      intro z hzK hpos
      have hstrict : ‖z‖ * cos α < (rot μ z).re := by
        rcases lt_or_eq_of_le (show ‖z‖ * cos α ≤ (rot μ z).re from hzK.1.1) with h | h
        · exact h
        · linarith [hray z hzK h]
      have hzR : ‖z‖ < R := by
        have : ‖z‖ ≤ R := by have := hzK.1.2; rwa [mem_closedBall, dist_zero_right] at this
        rcases lt_or_eq_of_le this with h | h
        · exact h
        · linarith [houter z hzK h]
      have hzr0 : r0 < ‖z‖ := by
        rcases lt_or_eq_of_le (show r0 ≤ ‖z‖ from hzK.2) with h | h
        · exact h
        · linarith [hinner z hzK h.symm]
      set O := {z : ℂ | ‖z‖ * cos α < (rot μ z).re} ∩ ball 0 R ∩ {z : ℂ | r0 < ‖z‖} with hO
      have hOo : IsOpen O :=
        ((isOpen_lt (continuous_norm.mul continuous_const) (Complex.continuous_re.comp hrotc)).inter
          isOpen_ball).inter (isOpen_lt continuous_const continuous_norm)
      have hzO : z ∈ O := ⟨⟨hstrict, by rw [mem_ball, dist_zero_right]; exact hzR⟩, hzr0⟩
      obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hOo z hzO
      refine ⟨r / 2, by positivity, fun z' hz' => ?_⟩
      have hz'O : z' ∈ O := hrO (closedBall_subset_ball (by linarith) hz')
      have hz'0 : z' ≠ 0 := fun h0 => by
        have h2 : r0 < ‖z'‖ := hz'O.2
        rw [h0, norm_zero] at h2; linarith
      have hz'c : ‖z'‖ * cos α < (rot μ z').re := hz'O.1.1
      exact ⟨⟨⟨hz'c.le, ball_subset_closedBall hz'O.1.2⟩, (show r0 < ‖z'‖ from hz'O.2).le⟩, rot_mem_slitPlane hα0 hαπ hz'0 hz'c.le⟩
    have hwc : ContinuousOn w K := fun z hzK =>
      (wfun2_continuousAt μ A B q q' ε (rot_mem_slitPlane hα0 hαπ (hK0 z hzK) hzK.1.1)).continuousWithinAt
    have hsubv : ∀ c r, 0 < r → closedBall c r ⊆ K ∩ U →
        v c ≤ circleAverage v c r ∧ CircleIntegrable v c r := by
      intro c r hr hball
      have hb0 : closedBall c r ⊆ ({0}ᶜ : Set ℂ) := (hball.trans inter_subset_left).trans hKc0
      refine ⟨hV.2.2 n c r hr hb0, trunc_circleIntegrable_on hV n ?_⟩
      rw [abs_of_pos hr]; exact sphere_subset_closedBall.trans hb0
    have hmp := max_principle_on hKc (fun z hz => hz.1.2) ((trunc_uscOn hV n).mono hKc0) hsubv hwc
      (fun c ρ hρ hball => wfun2_mean μ A B q q' ε hρ hball) hint
    -- the target point
    set zt := Complex.exp ((t : ℂ) * Complex.I) with hzt
    have hzt1 : ‖zt‖ = 1 := Complex.norm_exp_ofReal_mul_I t
    have hzt0 : zt ≠ 0 := Complex.exp_ne_zero _
    have hrotzt : rot μ zt = Complex.exp (((t - μ : ℝ) : ℂ) * Complex.I) := rot_exp μ t
    have htμ : |t - μ| < α := by rw [abs_lt, hμ, hα]; constructor <;> linarith
    have harg : Complex.arg (rot μ zt) = t - μ := by
      rw [hrotzt, Complex.arg_exp_mul_I, toIocMod_eq_self]
      constructor <;> linarith [(abs_lt.mp htμ).1, (abs_lt.mp htμ).2]
    have hztK : zt ∈ K := by
      refine ⟨⟨?_, by rw [mem_closedBall, dist_zero_right, hzt1]; exact hR1⟩, by
        show r0 ≤ ‖zt‖; rw [hzt1]; exact hr01⟩
      show ‖zt‖ * cos α ≤ (rot μ zt).re
      rw [hzt1, one_mul, hrotzt, Complex.exp_ofReal_mul_I_re, ← cos_abs (t - μ)]
      exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hαπ.le htμ.le
    have hle := hmp zt hztK
    rw [hw, wfun2_polar μ A B q q' ε hzt0, hzt1, harg] at hle
    simp only [one_rpow, one_mul] at hle
    have hc1 : ε * cos (q' * (t - μ)) ≤ ε := mul_le_of_le_one_right hε.le (cos_le_one _)
    have hc2 : ε * cos (q * (t - μ)) ≤ ε := mul_le_of_le_one_right hε.le (cos_le_one _)
    have hvt : v zt ≤ A * cos (q * (t - μ)) + B * sin (q * (t - μ)) + 2 * ε := by linarith
    calc V zt ≤ ((v zt : ℝ) : EReal) := le_trunc (hV.1 zt (Set.mem_compl_singleton_iff.mpr hzt0)) n
      _ ≤ _ := EReal.coe_le_coe_iff.mpr hvt
  -- ε → 0 and the chord identity
  have hchord : A * cos (q * (t - μ)) + B * sin (q * (t - μ))
      = (a * sin (q * (y - t)) + b * sin (q * (t - x))) / sin (q * (y - x)) := by
    have e1 : y - t = α - (t - μ) := by rw [hμ, hα]; ring
    have e2 : t - x = α + (t - μ) := by rw [hμ, hα]; ring
    have e3 : y - x = 2 * α := by rw [hα]; ring
    rw [e1, e2, e3, hA, hB]
    exact chord_identity hcqα.ne' hsqα.ne'
  rw [← hchord]
  induction hVt : V (Complex.exp ((t : ℂ) * Complex.I)) using EReal.rec with
  | bot => exact bot_le
  | coe vt =>
    rw [EReal.coe_le_coe_iff]
    apply le_of_forall_pos_le_add
    intro ε hε
    have := key (ε / 2) (by positivity)
    rw [hVt, EReal.coe_le_coe_iff] at this
    linarith
  | top => exact absurd hVt (hV.1 _ (Set.mem_compl_singleton_iff.mpr (Complex.exp_ne_zero _)))

/-- **q-subtrigonometric ⇒ trigonometrically q-convex** (`q > 1/2`), for the paper's Definition 2.1: `φ` finite and
`|ζ|^q φ(arg ζ)` subharmonic on `ℂ \ {0}` (sec2_obstacle.tex l.54-60). -/
theorem qsubtrig_trigConvex {q : ℝ} (hq0 : 1 / 2 < q) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) : TrigConvex q φ := by
  have hq : 0 < q := by linarith
  set V : ℂ → EReal := fun ζ => ((angularPotential q φ ζ : ℝ) : EReal) with hVdef
  have hV : IsSubharmonicOn ({0}ᶜ : Set ℂ) V := hφ.2
  have hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → z ≠ 0 → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z := by
    intro r z hr _
    simp only [hVdef, angularPotential]
    rw [← EReal.coe_mul, Complex.arg_real_mul z hr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      mul_rpow hr.le (norm_nonneg z)]
    congr 1; ring
  have hval : ∀ θ : ℝ, V (Complex.exp ((θ : ℂ) * Complex.I)) = ((φ θ : ℝ) : EReal) := by
    intro θ
    simp only [hVdef, angularPotential, Complex.norm_exp_ofReal_mul_I, one_rpow, one_mul, Complex.arg_exp_mul_I]
    rw [toIocMod, hφ.1.sub_zsmul_eq]
  apply trigConvex_of_comparison hq
  intro x t y hxt hty hlen
  have h := sector_comparison_punct hq0 hV hhom (hxt.trans hty) hlen (le_of_eq (hval x)) (le_of_eq (hval y)) t hxt hty
  rwa [hval t, EReal.coe_le_coe_iff] at h

/-- A q-subtrigonometric `φ` (Definition 2.1, `q > 1/2`) is continuous (sec2_obstacle.tex l.58-60). -/
theorem qsubtrig_continuous {q : ℝ} (hq0 : 1 / 2 < q) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) : Continuous φ :=
  TrigCont.trigConvex_continuous (by linarith) (qsubtrig_trigConvex hq0 hφ)

/-- A q-subtrigonometric `φ` (Definition 2.1, `q > 1/2`) has finite one-sided derivatives everywhere. -/
theorem qsubtrig_one_sided {q : ℝ} (hq0 : 1 / 2 < q) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) (x : ℝ) :
    ∃ dl dr : ℝ, HasDerivWithinAt φ dl (Iic x) x ∧ HasDerivWithinAt φ dr (Ici x) x :=
  TrigCont.trigConvex_one_sided (by linarith) (qsubtrig_trigConvex hq0 hφ) x

end SectorGK

end GKSharp
