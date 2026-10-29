/- GKSharp/Proofs/Sec4Near.lean - slice (b): limits at the identity, eventual negativity of h, dF (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v0.90, each as `<row>_proved` with the row's exact type. On `δ ∈ [0, 1)` the
shared strip row cDelta_eq_gk (GKSharp.cDelta_eq_gk_proved) gives `GK_p(1 - δ) = C(δ)`, the continued root.
- near_identity_limits (A:46-47): `C` is continuous with `C(0) = 1` and `C'(0) = 1/(2 sn) - 1/2 = a`, so
  `(C^p - 1)/δ` is the slope of `C^p` at `0`, with limit `p a`; and `K(1 - δ) = δ κ(δ)` with `κ` continuous at `0`,
  `κ(0) = 2 · 2^{q-1} sn^{p-2} cs^{1-q} = κ₀`.
- omega_negative_eventual_h (A:48-50): `δ ↦ g(δ, s*)` is continuous at `0` (`powSlope p` is continuous at `1`: it is
  the slope of `x^p`), and `g(0, s*) = Ω < 0` (g_zero); so `g(δ, s*) < 0` for small `δ > 0`, and h_le_delta_g gives
  `h(1 - δ) ≤ δ g(δ, s*) < 0`. Direct witness `s = s*`, no limsup.
- localF_derivative (B:102-103): `(p p')' = p(p - 2)/(p - 1)²`, `(4 cos²(π/p))' = 8 cos(π/p) sin(π/p) π/p²`, and
  `π(p - 2)/(2p) = π/2 - π/p`.
-/
import GKSharp.Proofs.Sec4bAxis
import GKSharp.Proofs.Sec4aOmega
import GKSharp.Proofs.StripLeaves

namespace GKSharp

open Set Filter GKSharp.Threshold
open scoped Topology

/-- `powSlope p` is continuous at `1`: off `1` it is the slope of `x ↦ x^p` at `1`. -/
lemma sec4a_powSlope_continuousAt (p : ℝ) : ContinuousAt (powSlope p) 1 := by
  have hd := Real.hasDerivAt_rpow_const (x := 1) (p := p) (Or.inl one_ne_zero)
  rw [hasDerivAt_iff_tendsto_slope, Real.one_rpow, mul_one] at hd
  have h1 : powSlope p 1 = p := by simp [powSlope]
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, h1]
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 1 := hx
  simp only [slope_def_field, Real.one_rpow, powSlope, hx', ↓reduceIte]

/-- The continued root `C(δ) = cDelta p δ` is continuous in `δ`. -/
lemma sec4a_cDelta_continuous (p : ℝ) : Continuous (cDelta p) := by
  have : cDelta p = fun d => d / (2 * sn p) + Real.sqrt (d ^ 2 / (4 * sn p ^ 2) + 1 - d) := rfl
  rw [this]
  fun_prop

/-- `C'(0) = a = (1 - sn)/(2 sn)`. -/
lemma sec4a_cDelta_hasDerivAt {p : ℝ} (hp : 1 < p) : HasDerivAt (cDelta p) (aConst p) 0 := by
  have hsn := sec4a_sn_pos hp
  have hsn' : sn p ≠ 0 := hsn.ne'
  have hu : HasDerivAt (fun d : ℝ => d ^ 2 / (4 * sn p ^ 2) + 1 - d) (-1) 0 := by
    refine ((((hasDerivAt_pow 2 (0 : ℝ)).div_const (4 * sn p ^ 2)).add_const 1).sub
      (hasDerivAt_id' (x := (0 : ℝ)))).congr_deriv ?_
    norm_num
  have hs := hu.sqrt (by norm_num)
  have hl := (hasDerivAt_id' (x := (0 : ℝ))).div_const (2 * sn p)
  have hC : cDelta p = fun d => d / (2 * sn p) + Real.sqrt (d ^ 2 / (4 * sn p ^ 2) + 1 - d) := rfl
  rw [hC]
  refine (hl.add hs).congr_deriv ?_
  norm_num [aConst]
  field_simp
  ring

/-- `κ(δ) = kap p δ` is continuous at `0`. -/
lemma sec4a_kap_continuousAt {p : ℝ} : ContinuousAt (kap p) 0 := by
  have hc := (sec4a_cDelta_continuous p).continuousAt (x := 0)
  have h0 : cDelta p 0 ^ 2 + 1 - 0 ≠ 0 := by rw [GKSharp.Strip.cDelta_zero]; norm_num
  have hD : ContinuousAt (fun d => (cDelta p d ^ 2 + 1 - d) ^ (q p - 1)) 0 :=
    (((hc.pow 2).add continuousAt_const).sub continuousAt_id).rpow_const (Or.inl h0)
  have hk : kap p = fun d =>
      2 * cDelta p d * sn p ^ (p - 2) * cs p ^ (1 - q p) * (cDelta p d ^ 2 + 1 - d) ^ (q p - 1) := rfl
  rw [hk]
  exact (((continuousAt_const.mul hc).mul continuousAt_const).mul continuousAt_const).mul hD

/-- `T₁(δ) = tOne p δ` is continuous at `0`. -/
lemma sec4a_tOne_continuousAt {p : ℝ} (hp : 1 < p) : ContinuousAt (tOne p) 0 := by
  have hsn := sec4a_sn_pos hp
  have hc := (sec4a_cDelta_continuous p).continuousAt (x := 0)
  have hps : ContinuousAt (fun d => powSlope p (cDelta p d)) 0 :=
    (sec4a_powSlope_continuousAt p).comp_of_eq hc (GKSharp.Strip.cDelta_zero p)
  have hden : sn p * (cDelta p 0 + 1) ≠ 0 := by
    rw [GKSharp.Strip.cDelta_zero]
    exact mul_ne_zero hsn.ne' (by norm_num)
  have ht : tOne p = fun d => powSlope p (cDelta p d) * (cDelta p d - sn p) / (sn p * (cDelta p d + 1)) := rfl
  rw [ht]
  exact (hps.mul (hc.sub continuousAt_const)).div (continuousAt_const.mul (hc.add continuousAt_const)) hden

/-- For fixed `s`, `δ ↦ g p δ s` is continuous at `0`. -/
lemma sec4a_g_continuousAt {p : ℝ} (hp : 1 < p) (s : ℝ) : ContinuousAt (fun d => g p d s) 0 := by
  have hlin : ContinuousAt (fun d : ℝ => 1 - s * d) 0 := by fun_prop
  have hphi : ContinuousAt (fun d => phi p (s * d)) 0 :=
    (sec4a_powSlope_continuousAt p).comp_of_eq hlin (by simp)
  have hg : (fun d => g p d s) =
      fun d => (tOne p d + s * phi p (s * d)) / (s * (1 - s)) ^ q p - kap p d := rfl
  rw [hg]
  exact (((sec4a_tOne_continuousAt hp).add (continuousAt_const.mul hphi)).div_const _).sub
    sec4a_kap_continuousAt

/-- A:46-47, row `near_identity_limits`. -/
theorem near_identity_limits_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    Tendsto (fun delta : ℝ => gk p ((1 - delta : ℝ) : ℂ)) (nhdsWithin 0 (Ioi 0)) (𝓝 1) ∧
    Tendsto (fun delta : ℝ => (gk p ((1 - delta : ℝ) : ℂ) ^ p - 1) / delta)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (p * aConst p)) ∧
    Tendsto (fun delta : ℝ => kConst p (1 - delta) / delta)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (kappaZero p)) := by
  have hev : ∀ᶠ d in nhdsWithin (0 : ℝ) (Ioi 0), cDelta p d = gk p ((1 - d : ℝ) : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with d hd
    exact GKSharp.cDelta_eq_gk_proved p d hp hp2 ⟨hd.1.le, hd.2⟩
  have hc0 : Tendsto (cDelta p) (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
    have := ((sec4a_cDelta_continuous p).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [GKSharp.Strip.cDelta_zero] at this
  refine ⟨hc0.congr' hev, ?_, ?_⟩
  · have hF := (sec4a_cDelta_hasDerivAt hp).rpow_const (p := p)
      (Or.inl (by rw [GKSharp.Strip.cDelta_zero]; norm_num))
    rw [GKSharp.Strip.cDelta_zero, Real.one_rpow, mul_one, hasDerivAt_iff_tendsto_slope] at hF
    have hF' := hF.mono_left (nhdsWithin_mono _ fun x (hx : x ∈ Ioi (0 : ℝ)) => (show (0 : ℝ) < x from hx).ne')
    rw [mul_comm p (aConst p)]
    refine hF'.congr' ?_
    filter_upwards [hev] with d hd
    simp only [slope_def_field, GKSharp.Strip.cDelta_zero, Real.one_rpow, sub_zero, ← hd]
  · have hk0 : kap p 0 = kappaZero p := by
      have h2 : (2 : ℝ) * (2 : ℝ) ^ (q p - 1) = 2 ^ q p := by
        rw [Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      unfold kap kappaZero
      rw [GKSharp.Strip.cDelta_zero, show (1 : ℝ) ^ 2 + 1 - 0 = 2 by norm_num, ← h2]
      ring
    have hk : Tendsto (kap p) (nhdsWithin 0 (Ioi 0)) (𝓝 (kappaZero p)) := by
      rw [← hk0]
      exact sec4a_kap_continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine hk.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with d hd
    have hd0 : d ≠ 0 := hd.1.ne'
    have hC := GKSharp.cDelta_eq_gk_proved p d hp hp2 ⟨hd.1.le, hd.2⟩
    unfold kConst kap
    rw [← hC, show cDelta p d ^ 2 + (1 - d) = cDelta p d ^ 2 + 1 - d by ring, sub_sub_cancel]
    unfold sn cs q
    field_simp

/-- A:48-50, row `omega_negative_eventual_h`. -/
theorem omega_negative_eventual_h_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (homega : omega p < 0) :
    ∃ eps > 0, ∀ lam : ℝ, 1 - eps < lam → lam < 1 → Threshold.h p lam < 0 := by
  obtain ⟨⟨hs0, hs1⟩, -⟩ := sStar_spec_proved p hp hp2
  have hG0 : g p 0 (sStar p) < 0 := by
    rw [GKSharp.g_zero_proved p (sStar p) hp hp2]
    exact homega
  have hmem := (sec4a_g_continuousAt hp (sStar p)).preimage_mem_nhds (Iio_mem_nhds hG0)
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨min eps 1, lt_min heps one_pos, fun lam hlam1 hlam2 => ?_⟩
  have hd0 : 0 < 1 - lam := by linarith
  have hd1 : 1 - lam < 1 := by linarith [min_le_right eps 1]
  have hdeps : 1 - lam < eps := by linarith [min_le_left eps 1]
  have hneg : g p (1 - lam) (sStar p) < 0 := by
    have hb : 1 - lam ∈ Metric.ball (0 : ℝ) eps := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hd0]
      exact hdeps
    exact hball hb
  have hle := h_le_delta_g_proved GKSharp.cDelta_eq_gk_proved p (1 - lam) (sStar p) hp hp2
    ⟨hd0, hd1⟩ ⟨hs0, hs1⟩
  rw [sub_sub_cancel] at hle
  have := mul_neg_of_pos_of_neg hd0 hneg
  linarith

/-- B:102-103, row `localF_derivative`. -/
theorem localF_derivative_proved (p : ℝ) (hp : 1 < p) :
    deriv localF p = (p - 2) * p / (p - 1) ^ 2 -
      8 * Real.sin (Real.pi * (p - 2) / (2 * p)) *
        Real.cos (Real.pi * (p - 2) / (2 * p)) * Real.pi / p ^ 2 := by
  have hp0 : p ≠ 0 := (show (0 : ℝ) < p by linarith).ne'
  have hp1 : p - 1 ≠ 0 := (sub_pos.mpr hp).ne'
  have harg : Real.pi * (p - 2) / (2 * p) = Real.pi / 2 - Real.pi / p := by field_simp
  rw [harg, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  have hF : localF = fun x : ℝ => x * (x / (x - 1)) - 4 * (1 + Real.cos (Real.pi / x) ^ 2) := by
    funext x
    rfl
  have h1 := (hasDerivAt_id' (x := p)).mul ((hasDerivAt_id' (x := p)).div
    ((hasDerivAt_id' (x := p)).sub_const 1) hp1)
  have h2 := ((((hasDerivAt_const p Real.pi).div (hasDerivAt_id' (x := p)) hp0).cos.pow 2).const_add 1).const_mul 4
  have hD : HasDerivAt localF ((p - 2) * p / (p - 1) ^ 2 -
      8 * Real.cos (Real.pi / p) * Real.sin (Real.pi / p) * Real.pi / p ^ 2) p := by
    rw [hF]
    refine (h1.sub h2).congr_deriv ?_
    norm_num
    field_simp
    ring
  exact hD.deriv

end GKSharp
