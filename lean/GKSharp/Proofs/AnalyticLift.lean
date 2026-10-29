/- GKSharp/Proofs/AnalyticLift.lean - slice (a): O22 and eq:lift (sec2_obstacle.tex l.75-80, short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
The analytic lift Z = H exp(Y/2), W = z^k B H exp(-Y/2) of a polynomial g with g(0) = 0: its exact product and
boundary moduli, the pair-integral inequality for it, and the printed lift integral.

  The factorization g = z^k B h, H² = h is the PROVED row slice_O21 (BlaschkeLift). On the circle |B| = 1, so
  |H|² = |h| = |g|. The pair inequality is given for polynomial pairs only (PolynomialPairBound, the actual norm by
  norm_iff_polynomial_pairs); it passes to (Z, W) in two limits: for r < 1, z ↦ Z(rz) is holomorphic on a disk of
  radius > 1, so its Taylor partial sums converge uniformly on the closed unit disk (cauchyPowerSeries), and
  dominated convergence gives the bound for (Z(r·), W(r·)); then r -> 1- by continuity on the closed disk.
  eq:lift: pairObstacle(Z, W) = |g|^(p/2) Γ(Re Y, arg g) (pair_gamma_factor; both sides are 0 where g = 0). -/
import GKSharp.Proofs.BlaschkeLift
import GKSharp.Proofs.PencilPairs
import GKSharp.Proofs.ExponentialLift

open Real Set MeasureTheory Filter Topology Metric

namespace GKSharp

namespace AnalyticLift

/-! ### Finite Blaschke products: holomorphic near the closed disk, modulus one on the circle -/

lemma blaschke_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) : 1 - star a * z ≠ 0 := by
  intro h
  have hlt : ‖star a * z‖ < 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_right (norm_nonneg a) hz).trans_lt ha
  rw [← sub_eq_zero.mp h, norm_one] at hlt
  exact lt_irrefl _ hlt

lemma blaschke_differentiableOn (roots : List ℂ) (hroots : ∀ a ∈ roots, ‖a‖ < 1) :
    DifferentiableOn ℂ (fun z => (roots.map fun a => (z - a) / (1 - star a * z)).prod)
      (closedBall 0 1) := by
  induction roots with
  | nil => simp
  | cons a rs ih =>
    simp only [List.map_cons, List.prod_cons]
    refine DifferentiableOn.mul ?_ (ih fun b hb => hroots b (List.mem_cons_of_mem a hb))
    refine DifferentiableOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
    exact blaschke_den_ne_zero (hroots a List.mem_cons_self) (mem_closedBall_zero_iff.mp hz)

lemma blaschke_factor_norm {a e : ℂ} (ha : ‖a‖ < 1) (he : ‖e‖ = 1) :
    ‖(e - a) / (1 - star a * e)‖ = 1 := by
  have hee : e * star e = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, he]
    norm_num
  have hden : 1 - star a * e = star (e - a) * e := by
    rw [star_sub]
    linear_combination -hee
  have hne : e - a ≠ 0 := by
    intro h0
    rw [sub_eq_zero.mp h0] at he
    linarith
  rw [hden, norm_div, norm_mul, norm_star, he, mul_one, div_self (norm_ne_zero_iff.mpr hne)]

lemma blaschke_norm_circle (roots : List ℂ) (hroots : ∀ a ∈ roots, ‖a‖ < 1) {e : ℂ} (he : ‖e‖ = 1) :
    ‖(roots.map fun a => (e - a) / (1 - star a * e)).prod‖ = 1 := by
  induction roots with
  | nil => simp
  | cons a rs ih =>
    rw [List.map_cons, List.prod_cons, norm_mul, blaschke_factor_norm (hroots a List.mem_cons_self) he,
      ih fun b hb => hroots b (List.mem_cons_of_mem a hb), one_mul]

/-! ### From polynomial pairs to pairs continuous on the closed disk and holomorphic inside -/

/-- A function holomorphic on the closed disk of radius `R > 1` is a uniform limit of polynomials on the closed
unit disk (its Taylor partial sums). -/
theorem exists_poly_tendstoUniformlyOn {f : ℂ → ℂ} {R : NNReal} (hR : 1 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n z => (q n).eval z) f atTop (closedBall 0 1) := by
  have hps := hf.hasFPowerSeriesOnBall (zero_lt_one.trans hR)
  set ps := cauchyPowerSeries f 0 R with hps_def
  set r' : NNReal := (1 + R) / 2 with hr'
  have h1 : (1 : ℝ) < r' := by
    rw [hr', NNReal.coe_div, NNReal.coe_add, NNReal.coe_one, NNReal.coe_two]
    have : (1 : ℝ) < R := by exact_mod_cast hR
    linarith
  have h2 : (r' : ENNReal) < R := by
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hr', NNReal.coe_div, NNReal.coe_add, NNReal.coe_one,
      NNReal.coe_two]
    have : (1 : ℝ) < R := by exact_mod_cast hR
    linarith
  have hu := (hps.tendstoUniformlyOn h2).mono (closedBall_subset_ball h1)
  simp only [zero_add] at hu
  refine ⟨fun n => ∑ k ∈ Finset.range n, Polynomial.C (ps.coeff k) * Polynomial.X ^ k, ?_⟩
  have heval : ∀ n z, (∑ k ∈ Finset.range n, Polynomial.C (ps.coeff k) * Polynomial.X ^ k).eval z =
      ps.partialSum n z := by
    intro n z
    rw [Polynomial.eval_finsetSum, FormalMultilinearSeries.partialSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, smul_eq_mul, mul_comm]
  simpa only [heval] using hu

/-- Dominated convergence for the pair integral along any countably generated filter. -/
theorem integral_nonneg_of_tendsto {p C : ℝ} (hp : 0 < p) (ρ : ℂ) {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [l.NeBot] {zf wf : ι → ℝ → ℂ} {z w : ℝ → ℂ} {M : ℝ}
    (hzc : ∀ᶠ n in l, Continuous (zf n)) (hwc : ∀ᶠ n in l, Continuous (wf n))
    (hbd : ∀ᶠ n in l, ∀ t, ‖zf n t‖ ≤ M ∧ ‖wf n t‖ ≤ M)
    (hz : ∀ t, Tendsto (fun n => zf n t) l (𝓝 (z t)))
    (hw : ∀ t, Tendsto (fun n => wf n t) l (𝓝 (w t)))
    (hnn : ∀ᶠ n in l, 0 ≤ ∫ t in (0 : ℝ)..(2 * π), pairObstacle p C ρ (zf n t) (wf n t)) :
    0 ≤ ∫ t in (0 : ℝ)..(2 * π), pairObstacle p C ρ (z t) (w t) := by
  have hG := Lift.continuous_pairObstacle hp C ρ
  obtain ⟨Bd, hBd⟩ := ((isCompact_closedBall (0 : ℂ) M).prod
    (isCompact_closedBall (0 : ℂ) M)).exists_bound_of_continuousOn hG.continuousOn
  have htend : Tendsto (fun n => ∫ t in (0 : ℝ)..(2 * π), pairObstacle p C ρ (zf n t) (wf n t)) l
      (𝓝 (∫ t in (0 : ℝ)..(2 * π), pairObstacle p C ρ (z t) (w t))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => Bd) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [hzc, hwc] with n hzn hwn
      exact (hG.comp (hzn.prodMk hwn)).aestronglyMeasurable
    · filter_upwards [hbd] with n hn
      exact Eventually.of_forall fun t _ => hBd (zf n t, wf n t)
        ⟨mem_closedBall_zero_iff.mpr (hn t).1, mem_closedBall_zero_iff.mpr (hn t).2⟩
    · refine Eventually.of_forall fun t _ => ?_
      have hzw := (hG.tendsto (z t, w t)).comp ((hz t).prodMk_nhds (hw t))
      simpa only [Function.comp_def] using hzw
  exact ge_of_tendsto htend hnn

lemma norm_le_of_dist_lt {a b : ℂ} (h : dist a b < 1) : ‖b‖ ≤ ‖a‖ + 1 := by
  have h1 := norm_sub_norm_le b a
  rw [← dist_eq_norm, dist_comm] at h1
  linarith

lemma unitPoint_mem_closedBall (t : ℝ) : unitPoint t ∈ closedBall (0 : ℂ) 1 :=
  mem_closedBall_zero_iff.mpr (norm_unitPoint t).le

/-- The pair inequality for two functions holomorphic on a closed disk of radius `R > 1`, `W 0 = 0`. -/
theorem pair_bound_of_large_disk {p C : ℝ} (hp : 0 < p) (ρ : ℂ) (hPair : PolynomialPairBound p C ρ)
    {Z W : ℂ → ℂ} {R : NNReal} (hR : 1 < R) (hZ : DifferentiableOn ℂ Z (closedBall 0 R))
    (hW : DifferentiableOn ℂ W (closedBall 0 R)) (hW0 : W 0 = 0) :
    0 ≤ ∫ t in (0 : ℝ)..(2 * π), pairObstacle p C ρ (Z (unitPoint t)) (W (unitPoint t)) := by
  have hsub : closedBall (0 : ℂ) 1 ⊆ closedBall 0 R :=
    closedBall_subset_closedBall (by exact_mod_cast hR.le)
  obtain ⟨qz, hqz⟩ := exists_poly_tendstoUniformlyOn hR hZ
  obtain ⟨qw, hqw⟩ := exists_poly_tendstoUniformlyOn hR hW
  obtain ⟨MZ, hMZ⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (hZ.continuousOn.mono hsub)
  obtain ⟨MW, hMW⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (hW.continuousOn.mono hsub)
  let wN : ℕ → Polynomial ℂ := fun n => qw n - Polynomial.C ((qw n).eval 0)
  have hwN : ∀ n z, (wN n).eval z = (qw n).eval z - (qw n).eval 0 := by
    intro n z
    simp only [wN, Polynomial.eval_sub, Polynomial.eval_C]
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := mem_closedBall_self zero_le_one
  refine integral_nonneg_of_tendsto (l := atTop) (M := |MZ| + 2 * |MW| + 2) hp ρ
    (zf := fun n t => (qz n).eval (unitPoint t)) (wf := fun n t => (wN n).eval (unitPoint t))
    (Eventually.of_forall fun n => (Polynomial.continuous _).comp DiscRescale.continuous_unitPoint')
    (Eventually.of_forall fun n => (Polynomial.continuous _).comp DiscRescale.continuous_unitPoint')
    ?_ (fun t => hqz.tendsto_at (unitPoint_mem_closedBall t)) (fun t => ?_)
    (Eventually.of_forall fun n => hPair (qz n) (wN n) (by rw [hwN, sub_self]))
  · filter_upwards [Metric.tendstoUniformlyOn_iff.mp hqz 1 one_pos,
      Metric.tendstoUniformlyOn_iff.mp hqw 1 one_pos] with n hn hn'
    intro t
    have e1 := norm_le_of_dist_lt (hn _ (unitPoint_mem_closedBall t))
    have e2 := norm_le_of_dist_lt (hn' _ (unitPoint_mem_closedBall t))
    have e3 := norm_le_of_dist_lt (hn' _ h0)
    have b1 := hMZ _ (unitPoint_mem_closedBall t)
    have b2 := hMW _ (unitPoint_mem_closedBall t)
    have b3 := hMW _ h0
    have a1 := le_abs_self MZ
    have a2 := le_abs_self MW
    have a3 := abs_nonneg MZ
    have a4 := abs_nonneg MW
    refine ⟨by linarith, ?_⟩
    simp only [hwN]
    have := norm_sub_le ((qw n).eval (unitPoint t)) ((qw n).eval 0)
    linarith
  · have h1 := hqw.tendsto_at (unitPoint_mem_closedBall t)
    have h2 := hqw.tendsto_at h0
    simp only [hwN]
    simpa [hW0] using h1.sub h2

/-- For `0 < r < 1`, the radius `R = (1 + 1/r)/2 > 1` has `r R < 1`, so `z ↦ r z` maps the closed disk of
radius `R` into the open unit disk. -/
lemma rescale_radius {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∃ R : NNReal, 1 < R ∧ ∀ z ∈ closedBall (0 : ℂ) R, (r : ℂ) * z ∈ ball (0 : ℂ) 1 := by
  have hinv : 1 < 1 / r := by rw [lt_div_iff₀ hr.1]; linarith [hr.2]
  have hR0 : 0 ≤ (1 + 1 / r) / 2 := by linarith
  obtain ⟨R, hRval⟩ : ∃ R : NNReal, (R : ℝ) = (1 + 1 / r) / 2 := ⟨⟨_, hR0⟩, rfl⟩
  have hR1 : 1 < R := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one, hRval]
    linarith
  have hrR : r * ((1 + 1 / r) / 2) < 1 := by
    have h1 : r * (1 / r) = 1 := by rw [mul_one_div, div_self hr.1.ne']
    have h2 : r * ((1 + 1 / r) / 2) = (r + r * (1 / r)) / 2 := by ring
    rw [h2, h1]
    linarith [hr.2]
  refine ⟨R, hR1, fun z hz => ?_⟩
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
  have hz' : ‖z‖ ≤ (1 + 1 / r) / 2 := by rw [← hRval]; exact mem_closedBall_zero_iff.mp hz
  calc r * ‖z‖ ≤ r * ((1 + 1 / r) / 2) := mul_le_mul_of_nonneg_left hz' hr.1.le
    _ < 1 := hrR

/-- For `0 < r < 1` the rescaled pair `(Z(r·), W(r·))` is holomorphic on a closed disk of radius `> 1`, so the
pair inequality holds for it. -/
theorem rescaled_pair_bound {p C : ℝ} (hp : 0 < p) (ρ : ℂ) (hPair : PolynomialPairBound p C ρ)
    {Z W : ℂ → ℂ} (hZd : DifferentiableOn ℂ Z (ball 0 1)) (hWd : DifferentiableOn ℂ W (ball 0 1))
    (hW0 : W 0 = 0) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 ≤ ∫ t in (0 : ℝ)..(2 * π),
      pairObstacle p C ρ (Z ((r : ℂ) * unitPoint t)) (W ((r : ℂ) * unitPoint t)) := by
  obtain ⟨R, hR1, hball⟩ := rescale_radius hr
  have hlin : DifferentiableOn ℂ (fun z : ℂ => (r : ℂ) * z) (closedBall 0 R) := by fun_prop
  have hZr : DifferentiableOn ℂ (fun z : ℂ => Z ((r : ℂ) * z)) (closedBall 0 R) :=
    hZd.comp hlin fun z hz => hball z hz
  have hWr : DifferentiableOn ℂ (fun z : ℂ => W ((r : ℂ) * z)) (closedBall 0 R) :=
    hWd.comp hlin fun z hz => hball z hz
  have hWr0 : (fun z : ℂ => W ((r : ℂ) * z)) 0 = 0 := by
    simp only [mul_zero, hW0]
  have key := pair_bound_of_large_disk hp ρ hPair hR1 hZr hWr hWr0
  simpa only using key

/-- The pair inequality passes from polynomial pairs to every pair holomorphic in the open unit disk and continuous
on the closed one, with `W 0 = 0` (the rescaled pairs, then `r → 1-`). -/
theorem disk_pair_bound {p C : ℝ} (hp : 0 < p) (ρ : ℂ) (hPair : PolynomialPairBound p C ρ)
    {Z W : ℂ → ℂ} (hZd : DifferentiableOn ℂ Z (ball 0 1)) (hWd : DifferentiableOn ℂ W (ball 0 1))
    (hZc : ContinuousOn Z (closedBall 0 1)) (hWc : ContinuousOn W (closedBall 0 1)) (hW0 : W 0 = 0) :
    0 ≤ ∫ t in (0 : ℝ)..(2 * π), pairObstacle p C ρ (Z (unitPoint t)) (W (unitPoint t)) := by
  obtain ⟨MZ, hMZ⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hZc
  obtain ⟨MW, hMW⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hWc
  have hI : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT zero_lt_one
  have hmem : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ z ∈ closedBall (0 : ℂ) 1, (r : ℂ) * z ∈ closedBall (0 : ℂ) 1 := by
    intro r hr z hz
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    calc r * ‖z‖ ≤ 1 * 1 :=
          mul_le_mul hr.2.le (mem_closedBall_zero_iff.mp hz) (norm_nonneg z) zero_le_one
      _ = 1 := one_mul 1
  have hcont : ∀ {F : ℂ → ℂ}, ContinuousOn F (closedBall 0 1) → ∀ r ∈ Ioo (0 : ℝ) 1,
      Continuous fun t => F ((r : ℂ) * unitPoint t) := by
    intro F hF r hr
    have hg : Continuous fun t : ℝ => (r : ℂ) * unitPoint t :=
      continuous_const.mul DiscRescale.continuous_unitPoint'
    exact hF.comp_continuous hg fun t => hmem r hr _ (unitPoint_mem_closedBall t)
  have hpath : ∀ t : ℝ, Tendsto (fun r : ℝ => (r : ℂ) * unitPoint t) (𝓝[<] 1)
      (𝓝[closedBall 0 1] (unitPoint t)) := by
    intro t
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h1 : Tendsto (fun r : ℝ => (r : ℂ) * unitPoint t) (𝓝 1)
          (𝓝 (((1 : ℝ) : ℂ) * unitPoint t)) :=
        (Complex.continuous_ofReal.tendsto 1).mul_const (unitPoint t)
      rw [Complex.ofReal_one, one_mul] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [hI] with r hr using hmem r hr _ (unitPoint_mem_closedBall t)
  have hlim : ∀ {F : ℂ → ℂ}, ContinuousOn F (closedBall 0 1) → ∀ t,
      Tendsto (fun r : ℝ => F ((r : ℂ) * unitPoint t)) (𝓝[<] 1) (𝓝 (F (unitPoint t))) := by
    intro F hF t
    exact (hF _ (unitPoint_mem_closedBall t)).tendsto.comp (hpath t)
  refine integral_nonneg_of_tendsto (l := 𝓝[<] (1 : ℝ)) (M := max MZ MW) hp ρ
    (zf := fun r t => Z ((r : ℂ) * unitPoint t)) (wf := fun r t => W ((r : ℂ) * unitPoint t))
    (z := fun t => Z (unitPoint t)) (w := fun t => W (unitPoint t))
    (by filter_upwards [hI] with r hr using hcont hZc r hr)
    (by filter_upwards [hI] with r hr using hcont hWc r hr)
    (by filter_upwards [hI] with r hr using fun t =>
      ⟨(hMZ _ (hmem r hr _ (unitPoint_mem_closedBall t))).trans (le_max_left _ _),
        (hMW _ (hmem r hr _ (unitPoint_mem_closedBall t))).trans (le_max_right _ _)⟩)
    (hlim hZc) (hlim hWc)
    (by filter_upwards [hI] with r hr using rescaled_pair_bound hp ρ hPair hZd hWd hW0 hr)

/-! ### The rows -/

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

lemma norm_exp_half_sq (x : ℂ) : ‖Complex.exp (x / 2)‖ ^ 2 = exp x.re := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp only [Complex.div_ofNat_re]
  push_cast
  ring

lemma norm_exp_neg_half_sq (x : ℂ) : ‖Complex.exp (-(x / 2))‖ ^ 2 = exp (-x.re) := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp only [Complex.neg_re, Complex.div_ofNat_re]
  push_cast
  ring

/-- O22. sec2_obstacle.tex:75–79. -/
theorem slice_O22_proved (hp : 1 < p) (P : RieszProjection p) (C : ℝ) (ρ : ℂ)
    (hC : pencilNorm P ρ ≤ C) (g : Polynomial ℂ) (hg0 : g.eval 0 = 0) (hg : g ≠ 0)
    (Y : Polynomial ℂ) :
    ∃ Z W : ℂ → ℂ, DifferentiableOn ℂ Z (Metric.ball 0 1) ∧
      DifferentiableOn ℂ W (Metric.ball 0 1) ∧ ContinuousOn Z (Metric.closedBall 0 1) ∧
      ContinuousOn W (Metric.closedBall 0 1) ∧ W 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, Z z * W z = g.eval z) ∧
      (∀ t : ℝ, ‖Z (unitPoint t)‖ ^ 2 = ‖g.eval (unitPoint t)‖ * exp (Y.eval (unitPoint t)).re ∧
        ‖W (unitPoint t)‖ ^ 2 = ‖g.eval (unitPoint t)‖ * exp (-(Y.eval (unitPoint t)).re)) ∧
      0 ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), pairObstacle p C ρ (Z (unitPoint t)) (W (unitPoint t)) := by
  obtain ⟨k, B, h, H, hk, ⟨phase, roots, hphase, hroots, hB⟩, -, hHd, -, hHc, -, hHsq, hgeq⟩ :=
    BlaschkeLift.slice_O21_proved g hg0 hg
  have hBfun : B = fun z => phase * (roots.map fun a => (z - a) / (1 - star a * z)).prod := funext hB
  have hBd : DifferentiableOn ℂ B (closedBall 0 1) := by
    rw [hBfun]
    exact (differentiableOn_const phase).mul (blaschke_differentiableOn roots hroots)
  have hBn : ∀ t : ℝ, ‖B (unitPoint t)‖ = 1 := by
    intro t
    rw [hB, norm_mul, hphase, blaschke_norm_circle roots hroots (norm_unitPoint t), one_mul]
  have hE : Differentiable ℂ fun z => Complex.exp (Y.eval z / 2) :=
    (Y.differentiable.div_const 2).cexp
  have hE' : Differentiable ℂ fun z => Complex.exp (-(Y.eval z / 2)) :=
    (Y.differentiable.div_const 2).neg.cexp
  have hp0 : 0 < p := by linarith
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  have hPair : PolynomialPairBound p C ρ := (norm_iff_polynomial_pairs hp P ρ C hC0).mp hC
  set Z : ℂ → ℂ := fun z => H z * Complex.exp (Y.eval z / 2) with hZdef
  set W : ℂ → ℂ := fun z => z ^ k * B z * H z * Complex.exp (-(Y.eval z / 2)) with hWdef
  have hZd : DifferentiableOn ℂ Z (ball 0 1) := hHd.mul hE.differentiableOn
  have hWd : DifferentiableOn ℂ W (ball 0 1) :=
    ((((differentiable_pow k).differentiableOn).mul (hBd.mono ball_subset_closedBall)).mul hHd).mul
      hE'.differentiableOn
  have hZc : ContinuousOn Z (closedBall 0 1) := hHc.mul hE.continuous.continuousOn
  have hWc : ContinuousOn W (closedBall 0 1) :=
    (((continuous_pow k).continuousOn.mul hBd.continuousOn).mul hHc).mul hE'.continuous.continuousOn
  have hW0 : W 0 = 0 := by
    simp only [hWdef, zero_pow (show k ≠ 0 by omega), zero_mul]
  have hgn : ∀ t : ℝ, ‖g.eval (unitPoint t)‖ = ‖H (unitPoint t)‖ ^ 2 := by
    intro t
    rw [hgeq _ (unitPoint_mem_closedBall t), norm_mul, norm_mul, norm_pow, norm_unitPoint, one_pow,
      one_mul, hBn, one_mul, ← hHsq _ (unitPoint_mem_closedBall t), norm_pow]
  refine ⟨Z, W, hZd, hWd, hZc, hWc, hW0, fun z hz => ?_, fun t => ⟨?_, ?_⟩,
    disk_pair_bound hp0 ρ hPair hZd hWd hZc hWc hW0⟩
  · have hexp : Complex.exp (Y.eval z / 2) * Complex.exp (-(Y.eval z / 2)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    calc Z z * W z = z ^ k * B z * H z ^ 2 *
          (Complex.exp (Y.eval z / 2) * Complex.exp (-(Y.eval z / 2))) := by
          simp only [hZdef, hWdef]
          ring
      _ = g.eval z := by rw [hexp, hHsq z hz, hgeq z hz, mul_one]
  · simp only [hZdef]
    rw [norm_mul, mul_pow, norm_exp_half_sq, hgn]
  · simp only [hWdef]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_unitPoint, one_pow, one_mul, hBn, one_mul, mul_pow,
      norm_exp_neg_half_sq, hgn]

/-- sec2_obstacle.tex:78–80, eq:lift. -/
theorem eq_lift_proved (hp : 1 < p) (P : RieszProjection p) (C : ℝ) (ρ : ℂ)
    (hC : pencilNorm P ρ ≤ C) (g : Polynomial ℂ) (hg0 : g.eval 0 = 0) (hg : g ≠ 0)
    (Y : Polynomial ℂ) :
    0 ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), ‖g.eval (unitPoint t)‖ ^ (p / 2) *
      gamma p C ρ (Y.eval (unitPoint t)).re (Complex.arg (g.eval (unitPoint t))) := by
  obtain ⟨Z, W, -, -, -, -, -, hZW, hmod, hint⟩ := slice_O22_proved hp P C ρ hC g hg0 hg Y
  have hp0 : 0 < p := by linarith
  have hpt : ∀ t : ℝ, pairObstacle p C ρ (Z (unitPoint t)) (W (unitPoint t)) =
      ‖g.eval (unitPoint t)‖ ^ (p / 2) *
        gamma p C ρ (Y.eval (unitPoint t)).re (Complex.arg (g.eval (unitPoint t))) := by
    intro t
    have hprod := hZW _ (unitPoint_mem_closedBall t)
    obtain ⟨hZn, hWn⟩ := hmod t
    set y := (Y.eval (unitPoint t)).re
    by_cases hg0t : g.eval (unitPoint t) = 0
    · rw [hg0t, norm_zero, zero_mul, sq_eq_zero_iff, norm_eq_zero] at hZn hWn
      rw [hZn, hWn, hg0t]
      simp [pairObstacle, Real.zero_rpow hp0.ne', Real.zero_rpow (by positivity : p / 2 ≠ 0)]
    · have hne : Z (unitPoint t) * W (unitPoint t) ≠ 0 := by rw [hprod]; exact hg0t
      have hZ0 : 0 < ‖Z (unitPoint t)‖ := norm_pos_iff.mpr (left_ne_zero_of_mul hne)
      have hW0 : 0 < ‖W (unitPoint t)‖ := norm_pos_iff.mpr (right_ne_zero_of_mul hne)
      have hG0 : 0 < ‖g.eval (unitPoint t)‖ := norm_pos_iff.mpr hg0t
      have hratio : ‖Z (unitPoint t)‖ / ‖W (unitPoint t)‖ = exp y := by
        rw [← pow_left_inj₀ (div_pos hZ0 hW0).le (exp_pos y).le two_ne_zero, div_pow, hZn, hWn,
          Real.exp_neg]
        field_simp
      rw [pair_gamma_factor p C ρ _ _ hne, hprod, hratio, Real.log_exp]
  rw [← intervalIntegral.integral_congr fun t _ => hpt t]
  exact hint

end AnalyticLift

end GKSharp
