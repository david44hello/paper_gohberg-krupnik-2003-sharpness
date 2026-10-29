/- local sector comparison for every positive homogeneity exponent.
Adapted from the checked SectorGK.sector_comparison_punct; proof unchanged after the opening bound.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.SectorGK

open Real Metric Set Filter Topology MeasureTheory
namespace GKSharp.SectorGK
open GKSharp.SubharmonicBasic

theorem sector_comparison_punct_local {q : ℝ} (hq : 0 < q) {V : ℂ → EReal}
    (hV : IsSubharmonicOn ({0}ᶜ : Set ℂ) V)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → z ≠ 0 → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z)
    {x y a b : ℝ} (hxy : x < y) (hlen : q * (y - x) < π) (hangle : y - x < 2 * π)
    (ha : V (Complex.exp ((x : ℂ) * Complex.I)) ≤ (a : EReal)) (hb : V (Complex.exp ((y : ℂ) * Complex.I)) ≤ (b : EReal))
    (t : ℝ) (ht : x < t) (ht' : t < y) :
    V (Complex.exp ((t : ℂ) * Complex.I)) ≤ (((a * sin (q * (y - t)) + b * sin (q * (t - x))) / sin (q * (y - x)) : ℝ) : EReal) := by
  set μ := (x + y) / 2 with hμ
  set α := (y - x) / 2 with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  have hqα : q * α < π / 2 := by rw [hα]; linarith
  have hαπ : α < π := by rw [hα]; linarith
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

end GKSharp.SectorGK

#print axioms GKSharp.SectorGK.sector_comparison_punct_local

