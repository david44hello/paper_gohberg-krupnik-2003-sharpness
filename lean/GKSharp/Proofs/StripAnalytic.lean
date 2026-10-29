/-
GKSharp/Proofs/StripAnalytic.lean — analytic leaves of paper 019 (sec5f_strip.tex l. 20, 46-49): the removable
quotients `powSlope` and `exprel` are analytic, `g` is analytic in `δ` at `0`, `Ẽ` is analytic in `η`, and the order-four
Taylor formula of `Ẽ` at `η = 0`; exact types of the draft rows `g_analytic_zero` and `etilde_taylor`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.StripInvolution

namespace GKSharp.Strip

open Set GKSharp.Threshold Filter
open scoped Topology Nat

lemma analyticAt_rpow_const {x : ℝ} (hx : 0 < x) (p : ℝ) : AnalyticAt ℝ (fun y : ℝ => y ^ p) x := by
  have h : (fun y : ℝ => Real.exp (Real.log y * p)) =ᶠ[𝓝 x] fun y => y ^ p := by
    filter_upwards [lt_mem_nhds hx] with y hy
    rw [Real.rpow_def_of_pos hy]
  exact ((analyticAt_log hx).mul analyticAt_const).rexp.congr h

lemma analyticAt_sqrt {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.sqrt x := by
  have h : (fun y : ℝ => y ^ (1 / 2 : ℝ)) =ᶠ[𝓝 x] Real.sqrt := by
    filter_upwards [lt_mem_nhds hx] with y hy
    rw [Real.sqrt_eq_rpow]
  exact (analyticAt_rpow_const hx _).congr h

lemma powSlope_eq_dslope (p : ℝ) : powSlope p = dslope (fun y : ℝ => y ^ p) 1 := by
  funext x
  by_cases hx : x = 1
  · subst hx
    rw [dslope_same, Real.deriv_rpow_const 1 p]
    simp [powSlope]
  · rw [dslope_of_ne _ hx, slope_def_field]
    simp [powSlope, hx]

lemma analyticAt_powSlope (p : ℝ) {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ (powSlope p) x := by
  by_cases hx1 : x = 1
  · subst hx1
    rw [powSlope_eq_dslope]
    obtain ⟨P, hP⟩ := analyticAt_rpow_const one_pos p
    exact hP.has_fpower_series_dslope_fslope.analyticAt
  · have h : (fun y : ℝ => (y ^ p - 1) / (y - 1)) =ᶠ[𝓝 x] powSlope p := by
      filter_upwards [eventually_ne_nhds hx1] with y hy
      simp [powSlope, hy]
    exact (((analyticAt_rpow_const hx p).sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.2 hx1)).congr h

lemma exprel_eq_dslope : exprel = dslope (fun x : ℝ => 1 - Real.exp (-x)) 0 := by
  funext x
  by_cases hx : x = 0
  · subst hx
    have hd : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) 1 0 := by
      have := ((Real.hasDerivAt_exp (-0)).comp 0 (hasDerivAt_neg 0)).const_sub 1
      simpa using this
    rw [dslope_same, hd.deriv]
    simp [exprel]
  · rw [dslope_of_ne _ hx, slope_def_field]
    simp [exprel, hx]

lemma analyticAt_exprel (x : ℝ) : AnalyticAt ℝ exprel x := by
  have hf : ∀ z : ℝ, AnalyticAt ℝ (fun x : ℝ => 1 - Real.exp (-x)) z := fun z =>
    analyticAt_const.sub analyticAt_id.neg.rexp
  by_cases hx : x = 0
  · subst hx
    rw [exprel_eq_dslope]
    obtain ⟨P, hP⟩ := hf 0
    exact hP.has_fpower_series_dslope_fslope.analyticAt
  · have h : (fun y : ℝ => (1 - Real.exp (-y)) / y) =ᶠ[𝓝 x] exprel := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      simp [exprel, hy]
    exact ((hf x).div analyticAt_id hx).congr h

/-! Composition forms. -/

lemma an_sqrt {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) (h : 0 < f x) :
    AnalyticAt ℝ (fun y => Real.sqrt (f y)) x := (analyticAt_sqrt h).comp hf

lemma an_rpow {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) (h : 0 < f x) (p : ℝ) :
    AnalyticAt ℝ (fun y => f y ^ p) x := (analyticAt_rpow_const h p).comp hf

lemma an_powSlope {f : ℝ → ℝ} {x : ℝ} (p : ℝ) (hf : AnalyticAt ℝ f x) (h : 0 < f x) :
    AnalyticAt ℝ (fun y => powSlope p (f y)) x := (analyticAt_powSlope p h).comp hf

lemma an_exprel {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => exprel (f y)) x := (analyticAt_exprel (f x)).comp hf

/-! The pieces of `g` and `Ẽ`. -/

lemma analyticAt_cDelta {p d0 : ℝ} (hp : 1 < p) (hd : d0 < 1) : AnalyticAt ℝ (fun d => cDelta p d) d0 := by
  have hsn := sn_pos hp
  have hrad : 0 < d0 ^ 2 / (4 * sn p ^ 2) + 1 - d0 := by
    have : 0 ≤ d0 ^ 2 / (4 * sn p ^ 2) := by positivity
    linarith
  unfold cDelta
  exact (analyticAt_id.div_const).add
    (an_sqrt ((analyticAt_id.pow 2).div_const |>.add analyticAt_const |>.sub analyticAt_id) hrad)

lemma analyticAt_tOne {p d0 : ℝ} (hp : 1 < p) (hd : d0 < 1) : AnalyticAt ℝ (fun d => tOne p d) d0 := by
  have hsn := sn_pos hp
  obtain ⟨hC0, -⟩ := cDelta_props hp hd
  have hC := analyticAt_cDelta hp hd
  unfold tOne
  exact ((an_powSlope p hC hC0).mul (hC.sub analyticAt_const)).div
    (analyticAt_const.mul (hC.add analyticAt_const)) (mul_pos hsn (by linarith)).ne'

lemma analyticAt_kap {p d0 : ℝ} (hp : 1 < p) (hd : d0 < 1) : AnalyticAt ℝ (fun d => kap p d) d0 := by
  obtain ⟨hC0, -⟩ := cDelta_props hp hd
  have hC := analyticAt_cDelta hp hd
  have hb : 0 < cDelta p d0 ^ 2 + 1 - d0 := by nlinarith [sq_nonneg (cDelta p d0)]
  unfold kap
  exact (((analyticAt_const.mul hC).mul analyticAt_const).mul analyticAt_const).mul
    (an_rpow ((hC.pow 2).add analyticAt_const |>.sub analyticAt_id) hb _)

end GKSharp.Strip

namespace GKSharp

open Set GKSharp.Threshold GKSharp.Strip Filter
open scoped Topology Nat

theorem g_analytic_zero_proved (p s : ℝ) (hp : 1 < p) (_hp2 : p < 2) (_hs : s ∈ Ioo (0 : ℝ) 1) :
    AnalyticAt ℝ (fun delta => g p delta s) 0 := by
  have hphi : AnalyticAt ℝ (fun d => phi p (s * d)) 0 := by
    unfold phi
    exact an_powSlope p (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (by simp)
  unfold g
  exact (((analyticAt_tOne hp (by norm_num)).add (analyticAt_const.mul hphi)).div_const).sub
    (analyticAt_kap hp (by norm_num))

lemma etilde_analyticAt {p sigma : ℝ} (hp : 1 < p) (hs : sigma ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    AnalyticAt ℝ (fun eta => etilde p eta sigma) x := by
  have hdA : ∀ z : ℝ, AnalyticAt ℝ (fun eta : ℝ => deltaEta eta) z := fun z => by
    unfold deltaEta
    exact analyticAt_const.sub analyticAt_id.neg.rexp
  have hdl : ∀ z : ℝ, deltaEta z < 1 := fun z => by
    rw [deltaEta]
    linarith [Real.exp_pos (-z)]
  have hsA : AnalyticAt ℝ (fun eta => sEta eta sigma) x := by
    unfold sEta
    exact (analyticAt_const.mul (an_exprel (analyticAt_const.mul analyticAt_id))).div (an_exprel analyticAt_id)
      (exprel_pos x).ne'
  have hsm : sEta x sigma ∈ Ioo (0 : ℝ) 1 := by
    by_cases hx : x = 0
    · subst hx
      simpa [sEta, exprel] using hs
    · exact sEta_mem hx hs
  have hρ : 0 < 1 - sEta x sigma * deltaEta x := by
    nlinarith [hsm.1, hsm.2, hdl x, mul_lt_mul_of_pos_left (hdl x) hsm.1]
  have hss : 0 < sEta x sigma * (1 - sEta x sigma) := mul_pos hsm.1 (by linarith [hsm.2])
  obtain ⟨hC0, -⟩ := cDelta_props hp (hdl x)
  have hT := (analyticAt_tOne hp (hdl x)).comp (hdA x)
  have hK := (analyticAt_kap hp (hdl x)).comp (hdA x)
  have hphi : AnalyticAt ℝ (fun eta => phi p (sEta eta sigma * deltaEta eta)) x := by
    unfold phi
    exact an_powSlope p (analyticAt_const.sub (hsA.mul (hdA x))) hρ
  have hden : AnalyticAt ℝ (fun eta => (sEta eta sigma * (1 - sEta eta sigma)) ^ q p) x :=
    an_rpow (hsA.mul (analyticAt_const.sub hsA)) hss _
  have hg : AnalyticAt ℝ (fun eta => g p (deltaEta eta) (sEta eta sigma)) x := by
    unfold g
    exact ((hT.add (hsA.mul hphi)).div hden (Real.rpow_pos_of_pos hss _).ne').sub hK
  have hV : AnalyticAt ℝ (fun eta => vWeight p eta) x := by
    unfold vWeight
    exact ((analyticAt_const.mul analyticAt_id).div_const).rexp.mul
      (an_rpow ((analyticAt_cDelta hp (hdl x)).comp (hdA x)) hC0 _)
  have hV0 : vWeight p x ≠ 0 := by
    unfold vWeight
    exact (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hC0 _)).ne'
  unfold etilde
  exact hg.div hV hV0

theorem etilde_taylor_proved (p sigma eta : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hs : sigma ∈ Ioo (0 : ℝ) 1) (heta : eta ∈ Ioc (0 : ℝ) eta1) :
    ∃ xi ∈ Ioo (0 : ℝ) eta,
      etilde p eta sigma = etilde p 0 sigma + eTwo p sigma * eta ^ 2 + cFour p xi sigma * eta ^ 4 := by
  set f : ℝ → ℝ := fun e => etilde p e sigma with hf
  have hfA : ∀ z, AnalyticAt ℝ f z := etilde_analyticAt hp hs
  have hfC : ContDiff ℝ ⊤ f := by
    rw [contDiff_iff_contDiffAt]
    exact fun z => (hfA z).contDiffAt
  have hne : (0 : ℝ) ≠ eta := heta.1.ne
  obtain ⟨xi, hxi, hT⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (n := 3) hne
    (hfC.contDiffOn.of_le le_top)
  have hU : uIoo (0 : ℝ) eta = Ioo 0 eta := by simp [uIoo, heta.1.le]
  rw [hU] at hxi
  refine ⟨xi, hxi, ?_⟩
  have hu := uniqueDiffOn_uIcc hne
  have h0mem : (0 : ℝ) ∈ uIcc (0 : ℝ) eta := left_mem_uIcc
  have hW : ∀ k : ℕ, iteratedDerivWithin k f (uIcc 0 eta) 0 = deriv^[k] f 0 := fun k => by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu ((hfC.of_le le_top).contDiffAt) h0mem,
      iteratedDeriv_eq_iterate]
  obtain ⟨hd1, hd3⟩ := etilde_odd_derivatives_proved p sigma hp hp2 hs
  rw [taylor_within_apply] at hT
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hW, smul_eq_mul] at hT
  rw [iteratedDeriv_eq_iterate] at hT
  simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero, id] at hT
  rw [hd1, hd3] at hT
  unfold eTwo cFour
  rw [← hf]
  simp only [Nat.factorial] at hT
  push_cast at hT
  linarith [hT]

end GKSharp
