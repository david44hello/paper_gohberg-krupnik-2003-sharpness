/- V_φ∘h is sub-mean on every circle for entire h and q-subtrigonometric φ, every q > 1/2
(Definition 2.1 as printed, punctured plane), and the bridge to IsSubharmonic (sec2_obstacle.tex l.58-60, l.67-71).
Copyright (C) Dave Goel 2026--now.

  V_φ(ζ) = angularPotential q φ ζ = |ζ|^q φ(arg ζ).
  (1) Supporting sinusoid (`trig_support`, 018): φ(t) ≥ φ(c) cos q(t-c) + m sin q(t-c) for |q(t-c)| < π/2.
  (2) h(a) ≠ 0 (`local_ne_V`): k = Re((φ(c) - i m)(h e^{-ic})^q) is harmonic near a, k ≤ V_φ∘h on small circles,
      k(a) = V_φ(h(a)). CHANGE from 018: the neighbourhood keeps |arg(h e^{-ic})| < π/(2(q+1)), so every q > 0 works
      (018 used Re > 0, i.e. q ≤ 1).
  (3) h(a) = 0 (`local_zero_V`, 018): needs a STRICTLY positive circle mean of V_ψ.
  (4) CHANGE from 018: the circle mean ∫₀^{2π} φ ≥ 0 comes from trig convexity (`integral_nonneg_of_trigConvex`), not
      from subharmonicity at 0 (Definition 2.1 gives none there).
  (5) ψ = φ + ε: trig convex, mean > 0; V_ψ∘h locally sub-mean everywhere; LocGlob.submean_of_local; ε → 0. -/
import GKSharp.Proofs.SectorGK
import GKSharp.Proofs.PotentialCoordinates

open Real Metric Set Filter Topology MeasureTheory

namespace GKSharp

namespace CompSubmeanGK

open PotentialCoordinates SubharmonicBasic

/-- For a `2π`-periodic `φ`: `φ(arg ζ) = φ(c + arg(ζ e^{-ic}))` (`ζ ≠ 0`). -/
theorem phi_arg_rot {φ : ℝ → ℝ} (hper : Function.Periodic φ (2 * π)) {ζ : ℂ} (hζ : ζ ≠ 0) (c : ℝ) :
    φ (Complex.arg ζ) = φ (c + Complex.arg (ζ * Complex.exp (((-c : ℝ) : ℂ) * Complex.I))) := by
  have h := Complex.arg_mul_coe_angle hζ (Complex.exp_ne_zero (((-c : ℝ) : ℂ) * Complex.I))
  rw [Complex.arg_exp_mul_I, Real.Angle.coe_toIocMod] at h
  have h2 : ((c + Complex.arg (ζ * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)) : ℝ) : Real.Angle)
      = (Complex.arg ζ : Real.Angle) := by
    rw [Real.Angle.coe_add, h, Real.Angle.coe_neg]; abel
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h2
  rw [show c + Complex.arg (ζ * Complex.exp (((-c : ℝ) : ℂ) * Complex.I)) = Complex.arg ζ + k * (2 * π) by
    linear_combination hk]
  exact (hper.int_mul k (Complex.arg ζ)).symm

/-- A harmonic minorant on the circle, touching at the centre, gives the sub-mean inequality. -/
theorem submean_of_minorant {v k : ℂ → ℝ} (hv : Continuous v) {a : ℂ} {r : ℝ}
    (hk : InnerProductSpace.HarmonicOnNhd k (closedBall a |r|)) (hle : ∀ z ∈ sphere a |r|, k z ≤ v z)
    (heq : k a = v a) : v a ≤ circleAverage v a r := by
  rw [← heq, ← hk.circleAverage_eq]
  exact circleAverage_mono ((hk.continuousOn.mono sphere_subset_closedBall).circleIntegrable')
    hv.continuousOn.circleIntegrable' hle


/-! ### (1) Supporting q-sinusoids -/

/-- **Supporting sinusoid**: a trigonometrically convex `φ` lies above `φ(c) cos q(t-c) + m sin q(t-c)` for
`|q(t-c)| < π/2`. -/
theorem trig_support {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (htc : TrigConvex q φ) (c : ℝ) :
    ∃ m : ℝ, ∀ t : ℝ, |q * (t - c)| < π / 2 → φ c * cos (q * (t - c)) + m * sin (q * (t - c)) ≤ φ t := by
  set g : ℝ → ℝ := fun u => φ (c + arctan u / q) / cos (arctan u) with hg
  have hconv : ConvexOn ℝ univ g := TrigCont.convexOn_transform hq htc c
  have hint : (0 : ℝ) ∈ interior (univ : Set ℝ) := by simp
  set m := derivWithin g (Ioi 0) 0 with hm
  have hg0 : g 0 = φ c := by simp [hg]
  have hline : ∀ u : ℝ, g 0 + m * u ≤ g u := by
    intro u
    rcases lt_trichotomy u 0 with hu | hu | hu
    · have h1 := hconv.slope_le_leftDeriv_of_mem_interior (mem_univ u) hint hu
      have h2 := hconv.leftDeriv_le_rightDeriv_of_mem_interior hint
      have h3 : slope g u 0 ≤ m := h1.trans h2
      rw [slope_def_field, div_le_iff₀ (by linarith)] at h3
      nlinarith
    · rw [hu]; simp
    · have h1 := hconv.rightDeriv_le_slope_of_mem_interior hint (mem_univ u) hu
      rw [slope_def_field, le_div_iff₀ (by linarith)] at h1
      nlinarith
  refine ⟨m, fun t ht => ?_⟩
  have h1 : -(π / 2) < q * (t - c) := by linarith [neg_abs_le (q * (t - c))]
  have h2 : q * (t - c) < π / 2 := lt_of_le_of_lt (le_abs_self _) ht
  have hcos : 0 < cos (q * (t - c)) := cos_pos_of_mem_Ioo ⟨h1, h2⟩
  have hgt : g (tan (q * (t - c))) = φ t / cos (q * (t - c)) := by
    simp only [hg]
    rw [arctan_tan h1 h2, show c + q * (t - c) / q = t by field_simp; ring]
  have key := hline (tan (q * (t - c)))
  rw [hgt, hg0, le_div_iff₀ hcos, add_mul, mul_assoc, tan_mul_cos hcos.ne'] at key
  linarith

/-- `φ + ε` (`ε ≥ 0`) is trigonometrically convex with `φ`. -/
theorem trigConvex_add_const {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (htc : TrigConvex q φ) {ε : ℝ} (hε : 0 ≤ ε) :
    TrigConvex q (fun t => φ t + ε) := by
  intro x t y hxt hty hlt
  have h := htc x t y hxt hty hlt
  have e1 : q * (y - t) < q * (y - x) := by nlinarith
  have e2 : q * (t - x) < q * (y - x) := by nlinarith
  have hB : 0 ≤ sin (q * (y - t)) := sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by linarith)
  have hC : 0 ≤ sin (q * (t - x)) := sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by linarith)
  have hsum : sin (q * (y - x)) ≤ sin (q * (y - t)) + sin (q * (t - x)) := by
    rw [show q * (y - x) = q * (y - t) + q * (t - x) by ring, sin_add]
    nlinarith [mul_nonneg hB (sub_nonneg.mpr (cos_le_one (q * (t - x)))),
      mul_nonneg hC (sub_nonneg.mpr (cos_le_one (q * (y - t))))]
  show (φ t + ε) * sin (q * (y - x)) ≤ (φ x + ε) * sin (q * (y - t)) + (φ y + ε) * sin (q * (t - x))
  nlinarith [mul_le_mul_of_nonneg_left hsum hε]

/-! ### (2) The case `h(a) ≠ 0` -/


/-! ### (2) The case `h(a) ≠ 0` -/

/-- **Case `h(a) ≠ 0`** (every `q > 0`): `V_φ∘h` is sub-mean on small circles around `a`. The harmonic minorant
`Re((φ(c) - i m)(h e^{-ic})^q)` comes from the supporting sinusoid at `c = arg h(a)`; near `a`, `|arg(h e^{-ic})| < π/(2(q+1))`
keeps `q·|arg| < π/2`, where the sinusoid supports `φ`. Critical points of `h` play no role. -/
theorem local_ne_V {q : ℝ} (hq0 : 0 < q) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hper : Function.Periodic φ (2 * π)) (htc : TrigConvex q φ) {h : ℂ → ℂ} (hh : Differentiable ℂ h) {a : ℂ}
    (ha : h a ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ →
      angularPotential q φ (h a) ≤ circleAverage (fun z => angularPotential q φ (h z)) a r := by
  set c := Complex.arg (h a) with hcdef
  obtain ⟨m, hm⟩ := trig_support hq0 htc c
  set e : ℂ := Complex.exp (((-c : ℝ) : ℂ) * Complex.I) with he
  have hnorm_e : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  set w : ℂ → ℂ := fun z => h z * e with hw
  have hwa : w a = ((‖h a‖ : ℝ) : ℂ) := by
    show h a * e = _
    rw [he]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (h a)]
    rw [mul_assoc, ← Complex.exp_add,
      show (Complex.arg (h a) : ℂ) * Complex.I + ((-c : ℝ) : ℂ) * Complex.I = 0 by rw [hcdef]; push_cast; ring,
      Complex.exp_zero, mul_one]
  have hwc : Continuous w := hh.continuous.mul continuous_const
  have hre0 : 0 < (w a).re := by rw [hwa, Complex.ofReal_re]; exact norm_pos_iff.mpr ha
  have hsla : w a ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hre0)
  have harg0 : Complex.arg (w a) = 0 := by rw [hwa]; exact Complex.arg_ofReal_of_nonneg (norm_nonneg _)
  set ε0 : ℝ := π / (2 * (q + 1)) with hε0
  have hε0p : 0 < ε0 := by positivity
  have hqε : q * ε0 < π / 2 := by
    rw [hε0, ← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pi_pos]
  have hev : ∀ᶠ z in 𝓝 a, 0 < (w z).re ∧ |Complex.arg (w z)| < ε0 := by
    have h1 : ∀ᶠ z in 𝓝 a, 0 < (w z).re :=
      ((Complex.continuous_re.comp hwc).continuousAt.tendsto).eventually (lt_mem_nhds hre0)
    have h2 : ∀ᶠ z in 𝓝 a, dist (Complex.arg (w z)) (Complex.arg (w a)) < ε0 :=
      Metric.tendsto_nhds.mp ((Complex.continuousAt_arg hsla).comp hwc.continuousAt) ε0 hε0p
    filter_upwards [h1, h2] with z hz1 hz2
    rw [harg0, Real.dist_eq, sub_zero] at hz2
    exact ⟨hz1, hz2⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ρ, hρ, fun r hr hrρ => ?_⟩
  have hVc : Continuous (fun z => angularPotential q φ (h z)) :=
    (angularPotential_continuous hq0 hc hper).comp hh.continuous
  set k : ℂ → ℝ := fun z => (((φ c : ℂ) - (m : ℂ) * Complex.I) * (w z) ^ ((q : ℝ) : ℂ)).re with hk
  have hin : ∀ z ∈ closedBall a |r|, 0 < (w z).re ∧ |Complex.arg (w z)| < ε0 := fun z hz => by
    rw [abs_of_pos hr] at hz; exact hball (lt_of_le_of_lt hz hrρ)
  have hharm : InnerProductSpace.HarmonicOnNhd k (closedBall a |r|) := by
    intro z hz
    have hs : w z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (hin z hz).1)
    exact (analyticAt_const.mul (((hh.analyticAt z).mul analyticAt_const).cpow analyticAt_const hs)).harmonicAt_re
  have hpolar : ∀ z, w z ≠ 0 →
      k z = ‖h z‖ ^ q * (φ c * cos (q * Complex.arg (w z)) + m * sin (q * Complex.arg (w z))) := by
    intro z hz
    simp only [hk]
    rw [SectorGK.re_coef_cpow hz]
    simp only [hw, norm_mul, hnorm_e, mul_one]
  refine submean_of_minorant hVc hharm (fun z hz => ?_) ?_
  · obtain ⟨hpos, harg⟩ := hin z (sphere_subset_closedBall hz)
    have hwz : w z ≠ 0 := fun h0 => by rw [h0] at hpos; simp at hpos
    have hhz : h z ≠ 0 := fun h0 => hwz (by simp [hw, h0])
    have hqarg : |q * (c + Complex.arg (w z) - c)| < π / 2 := by
      rw [show c + Complex.arg (w z) - c = Complex.arg (w z) by ring, abs_mul, abs_of_pos hq0]
      calc q * |Complex.arg (w z)| < q * ε0 := mul_lt_mul_of_pos_left harg hq0
        _ < π / 2 := hqε
    have hsup := hm (c + Complex.arg (w z)) hqarg
    rw [show c + Complex.arg (w z) - c = Complex.arg (w z) by ring] at hsup
    rw [hpolar z hwz]
    show _ ≤ ‖h z‖ ^ q * φ (Complex.arg (h z))
    rw [phi_arg_rot hper hhz c]
    exact mul_le_mul_of_nonneg_left hsup (rpow_nonneg (norm_nonneg _) _)
  · have hwa0 : w a ≠ 0 := by rw [hwa]; exact_mod_cast (norm_pos_iff.mpr ha).ne'
    rw [hpolar a hwa0, hwa, Complex.arg_ofReal_of_nonneg (norm_nonneg _)]
    simp [angularPotential, hcdef]

/-! ### (3) The case `h(a) = 0` -/

/-- `E_ψ(x) = V_ψ(e^{ix})`. -/
noncomputable def Ecirc (q : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ := angularPotential q ψ (Complex.exp ((x : ℂ) * Complex.I))

theorem Ecirc_periodic (q : ℝ) (ψ : ℝ → ℝ) : Function.Periodic (Ecirc q ψ) (2 * π) := by
  intro x
  unfold Ecirc
  congr 1
  rw [show (((x + 2 * π : ℝ) : ℂ)) * Complex.I = (x : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem Ecirc_continuous {q : ℝ} (hq : 0 < q) {ψ : ℝ → ℝ} (hc : Continuous ψ) (hper : Function.Periodic ψ (2 * π)) :
    Continuous (Ecirc q ψ) :=
  (angularPotential_continuous hq hc hper).comp (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))

/-- `∫₀^{2π} E(mθ+β) dθ = ∫₀^{2π} E` for `m ≥ 1`. -/
theorem integral_Ecirc_comp {q : ℝ} (hq : 0 < q) {ψ : ℝ → ℝ} (hc : Continuous ψ)
    (hper : Function.Periodic ψ (2 * π)) {m : ℕ} (hm : m ≠ 0) (β : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), Ecirc q ψ (m * θ + β) = ∫ x in (0 : ℝ)..(2 * π), Ecirc q ψ x := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hint : ∀ t₁ t₂ : ℝ, IntervalIntegrable (Ecirc q ψ) volume t₁ t₂ :=
    fun _ _ => (Ecirc_continuous hq hc hper).intervalIntegrable _ _
  rw [intervalIntegral.integral_comp_mul_add (fun x => Ecirc q ψ x) hm' β, mul_zero, zero_add,
    show (m : ℝ) * (2 * π) + β = β + (m : ℤ) • (2 * π) by rw [zsmul_eq_mul]; push_cast; ring,
    (Ecirc_periodic q ψ).intervalIntegral_add_zsmul_eq (m : ℤ) β hint, zsmul_eq_mul,
    (Ecirc_periodic q ψ).intervalIntegral_add_eq β 0, zero_add, smul_eq_mul]
  push_cast
  field_simp

/-- **Zero case**: at a zero of `h`, `V_ψ∘h` is sub-mean on small circles when `ψ` has positive circle mean. -/
theorem local_zero_V {q : ℝ} (hq : 0 < q) {ψ : ℝ → ℝ} (hc : Continuous ψ) (hper : Function.Periodic ψ (2 * π))
    (hpos : 0 < ∫ x in (0 : ℝ)..(2 * π), Ecirc q ψ x) {h : ℂ → ℂ} (hh : Differentiable ℂ h) {a : ℂ} (ha : h a = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ → angularPotential q ψ (h a) ≤ circleAverage (fun z => angularPotential q ψ (h z)) a r := by
  have hU0 : angularPotential q ψ 0 = 0 := angularPotential_zero hq ψ
  rw [ha, hU0]
  by_cases hz : ∀ᶠ z in 𝓝 a, h z = 0
  · obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hz
    refine ⟨ρ, hρ, fun r hr hrρ => ?_⟩
    have heq : Set.EqOn (fun z => angularPotential q ψ (h z)) (fun _ => (0 : ℝ)) (sphere a |r|) := by
      intro z hzs
      rw [abs_of_pos hr, mem_sphere] at hzs
      show angularPotential q ψ (h z) = 0
      rw [hball (show dist z a < ρ by rw [hzs]; exact hrρ), hU0]
    rw [circleAverage_congr_sphere heq, circleAverage_const]
  obtain ⟨m, g, hg, hga, hfac⟩ := ((hh.analyticAt a).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hz
  have hm : m ≠ 0 := by
    rintro rfl
    have := hfac.self_of_nhds
    rw [ha, pow_zero, one_smul] at this
    exact hga this.symm
  -- a global continuous cofactor g̃ with h = (z-a)^m g̃
  set gt : ℂ → ℂ := fun z => if z = a then g a else h z / (z - a) ^ m with hgt
  have hgt_eq : ∀ᶠ z in 𝓝 a, g z = gt z := by
    filter_upwards [hfac] with z hz
    by_cases hza : z = a
    · subst hza; simp [hgt]
    · have hne : (z - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
      simp only [hgt, hza, ↓reduceIte, hz, smul_eq_mul]
      field_simp
  have hgt_cont : Continuous gt := by
    rw [continuous_iff_continuousAt]
    intro z0
    by_cases hz0 : z0 = a
    · subst hz0; exact hg.continuousAt.congr hgt_eq
    · have hne : (z0 - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz0)
      have hc : ContinuousAt (fun z => h z / (z - a) ^ m) z0 :=
        hh.continuous.continuousAt.div ((continuous_id.sub continuous_const).pow m).continuousAt hne
      refine hc.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hz0] with z hz
      simp only [hgt, hz, ↓reduceIte]
  have hfac_all : ∀ z, h z = (z - a) ^ m * gt z := by
    intro z
    by_cases hza : z = a
    · subst hza; rw [ha, sub_self, zero_pow hm, zero_mul]
    · have hne : (z - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
      simp only [hgt, hza, ↓reduceIte]
      field_simp
  have hgta : gt a ≠ 0 := by simpa [hgt] using hga
  -- the parametric integral I(r)
  set Φ : ℝ → ℝ → ℝ := fun r θ => angularPotential q ψ (Complex.exp ((θ : ℂ) * Complex.I) ^ m * gt (circleMap a r θ)) with hΦ
  have hcm : Continuous (fun x : ℝ × ℝ => circleMap a x.1 x.2) := by
    unfold circleMap; fun_prop
  have hΦc : Continuous (Function.uncurry Φ) := by
    have h1 : Continuous (fun x : ℝ × ℝ => Complex.exp ((x.2 : ℂ) * Complex.I) ^ m) := by fun_prop
    exact (angularPotential_continuous hq hc hper).comp (h1.mul (hgt_cont.comp hcm))
  set I : ℝ → ℝ := fun r => ∫ θ in (0 : ℝ)..(2 * π), Φ r θ with hI
  have hIc : Continuous I := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hΦc 0 (2 * π)
  have hI0 : 0 < I 0 := by
    have hpt : ∀ θ : ℝ, Φ 0 θ = ‖gt a‖ ^ q * Ecirc q ψ (m * θ + Complex.arg (gt a)) := by
      intro θ
      have hw : Complex.exp ((θ : ℂ) * Complex.I) ^ m * gt a =
          ((‖gt a‖ : ℝ) : ℂ) * Complex.exp (((m * θ + Complex.arg (gt a) : ℝ) : ℂ) * Complex.I) := by
        conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (gt a), ← Complex.exp_nat_mul]
        rw [show (((m * θ + Complex.arg (gt a) : ℝ) : ℂ)) * Complex.I
            = (m : ℂ) * ((θ : ℂ) * Complex.I) + (Complex.arg (gt a) : ℂ) * Complex.I by push_cast; ring,
          Complex.exp_add]
        ring
      simp only [hΦ, circleMap_zero_radius, Function.const_apply, Ecirc]
      rw [hw, angularPotential_homog _ (norm_pos_iff.mpr hgta)]
    simp only [hI, hpt, intervalIntegral.integral_const_mul, integral_Ecirc_comp hq hc hper hm]
    exact mul_pos (rpow_pos_of_pos (norm_pos_iff.mpr hgta) _) hpos
  obtain ⟨δ, hδ, hδI⟩ := Metric.eventually_nhds_iff.mp ((hIc.tendsto 0).eventually (lt_mem_nhds hI0))
  refine ⟨δ, hδ, fun r hr hrδ => ?_⟩
  have hIr : 0 < I r := hδI (by rw [Real.dist_eq, sub_zero, abs_of_pos hr]; exact hrδ)
  have hpt : ∀ θ : ℝ, angularPotential q ψ (h (circleMap a r θ)) = (r ^ m) ^ q * Φ r θ := by
    intro θ
    rw [hfac_all, circleMap_sub_center, circleMap_zero, mul_pow, ← Complex.ofReal_pow, mul_assoc,
      angularPotential_homog _ (pow_pos hr m)]
  rw [circleAverage_def, smul_eq_mul]
  simp only [hpt, intervalIntegral.integral_const_mul]
  have : 0 < (2 * π)⁻¹ * ((r ^ m) ^ q * I r) :=
    mul_pos (inv_pos.mpr two_pi_pos) (mul_pos (rpow_pos_of_pos (pow_pos hr m) _) hIr)
  exact this.le


/-! ### (4) The circle mean of a trigonometrically convex profile is `≥ 0` -/

/-- `q(π/(4q)) = π/4`. -/
theorem mul_pi_div_four_mul {q : ℝ} (hq : 0 < q) : q * (π / (4 * q)) = π / 4 := by
  rw [mul_div_assoc', mul_comm q π, mul_div_mul_right _ _ hq.ne']

/-- **Circle mean `≥ 0`.** For a continuous, `2π`-periodic, trigonometrically `q`-convex `φ`: `∫₀^{2π} φ ≥ 0`.
The chord inequality on `[t - δ, t + δ]` (`δ = π/(4q)`) is `2 sin(qδ) cos(qδ) φ(t) ≤ sin(qδ) (φ(t-δ) + φ(t+δ))`;
integrate over a period (shift invariance) and use `cos(qδ) < 1`. (The 018 tool used subharmonicity AT 0 instead,
which Definition 2.1 does not give.) -/
theorem integral_nonneg_of_trigConvex {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (htc : TrigConvex q φ) (hc : Continuous φ)
    (hper : Function.Periodic φ (2 * π)) : 0 ≤ ∫ x in (0 : ℝ)..(2 * π), φ x := by
  set δ : ℝ := π / (4 * q) with hδ
  have hqδ : q * δ = π / 4 := mul_pi_div_four_mul hq
  have hδ0 : 0 < δ := by positivity
  have hs : 0 < sin (q * δ) := by
    rw [hqδ]; exact sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hc1 : cos (q * δ) < 1 := by
    rw [hqδ]
    have := cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith [pi_pos]) (by positivity : (0:ℝ) < π / 4)
    rwa [cos_zero] at this
  have hpt : ∀ t : ℝ, φ t * (2 * sin (q * δ) * cos (q * δ)) ≤ φ (t - δ) * sin (q * δ) + φ (t + δ) * sin (q * δ) := by
    intro t
    have h := htc (t - δ) t (t + δ) (by linarith) (by linarith)
      (by rw [show t + δ - (t - δ) = 2 * δ by ring]; nlinarith [pi_pos])
    rwa [show t + δ - (t - δ) = 2 * δ by ring, show t + δ - t = δ by ring, show t - (t - δ) = δ by ring,
      show q * (2 * δ) = 2 * (q * δ) by ring, sin_two_mul] at h
  have hshift1 : ∫ t in (0:ℝ)..(2 * π), φ (t - δ) = ∫ t in (0:ℝ)..(2 * π), φ t := by
    rw [intervalIntegral.integral_comp_sub_right (fun t => φ t) δ, show (2 * π - δ) = (0 - δ) + 2 * π by ring,
      hper.intervalIntegral_add_eq (0 - δ) 0, zero_add]
  have hshift2 : ∫ t in (0:ℝ)..(2 * π), φ (t + δ) = ∫ t in (0:ℝ)..(2 * π), φ t := by
    rw [intervalIntegral.integral_comp_add_right (fun t => φ t) δ, show (2 * π + δ) = (0 + δ) + 2 * π by ring,
      hper.intervalIntegral_add_eq (0 + δ) 0, zero_add]
  have hi1 : IntervalIntegrable (fun t => φ (t - δ) * sin (q * δ)) volume 0 (2 * π) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hi2 : IntervalIntegrable (fun t => φ (t + δ) * sin (q * δ)) volume 0 (2 * π) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hmono : ∫ t in (0:ℝ)..(2 * π), φ t * (2 * sin (q * δ) * cos (q * δ)) ≤
      ∫ t in (0:ℝ)..(2 * π), (φ (t - δ) * sin (q * δ) + φ (t + δ) * sin (q * δ)) :=
    intervalIntegral.integral_mono_on two_pi_pos.le (Continuous.intervalIntegrable (by fun_prop) _ _)
      (hi1.add hi2) (fun t _ => hpt t)
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, hshift1, hshift2] at hmono
  by_contra hneg
  push Not at hneg
  have h3 : (∫ x in (0 : ℝ)..(2 * π), φ x) * (sin (q * δ) * (1 - cos (q * δ))) < 0 :=
    mul_neg_of_neg_of_pos hneg (mul_pos hs (sub_pos.mpr hc1))
  nlinarith [h3, hmono]

/-- On the unit circle, `V_φ(e^{ix}) = φ(x)` for a `2π`-periodic `φ`. -/
theorem Ecirc_eq {q : ℝ} {φ : ℝ → ℝ} (hper : Function.Periodic φ (2 * π)) (x : ℝ) : Ecirc q φ x = φ x := by
  simp only [Ecirc, angularPotential, Complex.norm_exp_ofReal_mul_I, one_rpow, one_mul, Complex.arg_exp_mul_I]
  rw [toIocMod, hper.sub_zsmul_eq]

/-! ### (5) Assembly: `φ + ε`, local ⇒ global, `ε → 0` -/

/-- **`V_φ∘h` is sub-mean on every circle**, for entire `h` and continuous, periodic, trigonometrically `q`-convex `φ`
(every `q > 0`). -/
theorem comp_submean_of_trigConvex {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hper : Function.Periodic φ (2 * π)) (htc : TrigConvex q φ)
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    angularPotential q φ (h c) ≤ circleAverage (fun z => angularPotential q φ (h z)) c R := by
  have hmean : 0 ≤ ∫ x in (0 : ℝ)..(2 * π), Ecirc q φ x := by
    simp only [Ecirc_eq hper]; exact integral_nonneg_of_trigConvex hq htc hc hper
  have hNc : Continuous (fun z => ‖h z‖ ^ q) :=
    (continuous_norm.rpow_const (fun _ => Or.inr hq.le)).comp hh.continuous
  have hVc : Continuous (fun z => angularPotential q φ (h z)) :=
    (angularPotential_continuous hq hc hper).comp hh.continuous
  have hpert : ∀ ε : ℝ, 0 < ε → angularPotential q φ (h c) + ε * ‖h c‖ ^ q ≤
      circleAverage (fun z => angularPotential q φ (h z)) c R + ε * circleAverage (fun z => ‖h z‖ ^ q) c R := by
    intro ε hε
    set ψ : ℝ → ℝ := fun t => φ t + ε with hψ
    have hVψ : ∀ ζ, angularPotential q ψ ζ = angularPotential q φ ζ + ε * ‖ζ‖ ^ q := fun ζ => by
      simp only [angularPotential, hψ]; ring
    have hψc : Continuous ψ := hc.add continuous_const
    have hψper : Function.Periodic ψ (2 * π) := fun t => by simp only [hψ, hper t]
    have hψtc : TrigConvex q ψ := trigConvex_add_const hq htc hε.le
    have hψpos : 0 < ∫ x in (0 : ℝ)..(2 * π), Ecirc q ψ x := by
      have hE : ∀ x, Ecirc q ψ x = Ecirc q φ x + ε := fun x => by
        simp only [Ecirc, hVψ, Complex.norm_exp_ofReal_mul_I, one_rpow, mul_one]
      simp only [hE]
      rw [intervalIntegral.integral_add ((Ecirc_continuous hq hc hper).intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      nlinarith [pi_pos]
    have hW : Continuous (fun z => angularPotential q ψ (h z)) :=
      (angularPotential_continuous hq hψc hψper).comp hh.continuous
    have hloc : ∀ a, ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ →
        angularPotential q ψ (h a) ≤ circleAverage (fun z => angularPotential q ψ (h z)) a r := by
      intro a
      by_cases ha : h a = 0
      · exact local_zero_V hq hψc hψper hψpos hh ha
      · exact local_ne_V hq hψc hψper hψtc hh ha
    have hsub := LocGlob.submean_of_local hW hloc (c0 := c) hR
    simp only [hVψ] at hsub
    have hsm : circleAverage (fun z => ε * ‖h z‖ ^ q) c R = ε * circleAverage (fun z => ‖h z‖ ^ q) c R := by
      simp only [← smul_eq_mul]; exact circleAverage_fun_smul
    rwa [circleAverage_fun_add hVc.continuousOn.circleIntegrable'
      (show Continuous (fun z => ε * ‖h z‖ ^ q) from continuous_const.mul hNc).continuousOn.circleIntegrable',
      hsm] at hsub
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set A := circleAverage (fun z => ‖h z‖ ^ q) c R with hA
  set ε := δ / (|A - ‖h c‖ ^ q| + 1) with hεdef
  have hε : 0 < ε := div_pos hδ (by positivity)
  have h1 := hpert ε hε
  have h2 : ε * (A - ‖h c‖ ^ q) ≤ δ := by
    calc ε * (A - ‖h c‖ ^ q) ≤ ε * |A - ‖h c‖ ^ q| := mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
      _ ≤ ε * (|A - ‖h c‖ ^ q| + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = δ := by rw [hεdef]; field_simp
  have h3 : ε * (A - ‖h c‖ ^ q) = ε * A - ε * ‖h c‖ ^ q := mul_sub _ _ _
  linarith

/-- **`V_φ∘h` is sub-mean on every circle** for entire `h` and q-subtrigonometric `φ` (Definition 2.1, `q > 1/2`). -/
theorem comp_submean {q : ℝ} (hq0 : 1 / 2 < q) {φ : ℝ → ℝ} (hφ : QSubtrig q φ)
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    angularPotential q φ (h c) ≤ circleAverage (fun z => angularPotential q φ (h z)) c R :=
  comp_submean_of_trigConvex (by linarith) (SectorGK.qsubtrig_continuous hq0 hφ) hφ.1
    (SectorGK.qsubtrig_trigConvex hq0 hφ) hh c hR

/-! ### (6) From the real sub-mean inequality to `IsSubharmonic` -/

/-- A continuous real `v` with the sub-mean inequality on every circle is subharmonic (`IsSubharmonic`, truncated form). -/
theorem isSubharmonic_of_submean {v : ℂ → ℝ} (hv : Continuous v)
    (hsub : ∀ (c : ℂ) (r : ℝ), 0 < r → v c ≤ circleAverage v c r) : IsSubharmonic (fun z => ((v z : ℝ) : EReal)) := by
  refine ⟨fun z => EReal.coe_ne_top _, (continuous_coe_real_ereal.comp hv).upperSemicontinuous, fun n c r hr => ?_⟩
  simp only [trunc_coe]
  have hmax : Continuous (fun z => max (v z) (-(n : ℝ))) := hv.max continuous_const
  have hle : circleAverage v c r ≤ circleAverage (fun z => max (v z) (-(n : ℝ))) c r :=
    circleAverage_mono hv.continuousOn.circleIntegrable' hmax.continuousOn.circleIntegrable'
      (fun z _ => le_max_left _ _)
  have hle' : circleAverage (fun _ => -(n : ℝ)) c r ≤ circleAverage (fun z => max (v z) (-(n : ℝ))) c r :=
    circleAverage_mono continuousOn_const.circleIntegrable' hmax.continuousOn.circleIntegrable'
      (fun z _ => le_max_right _ _)
  rw [circleAverage_const] at hle'
  exact max_le ((hsub c r hr).trans hle) hle'

end CompSubmeanGK

end GKSharp
