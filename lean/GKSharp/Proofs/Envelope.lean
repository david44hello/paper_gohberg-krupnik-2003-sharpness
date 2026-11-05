/-
  GKSharp/Proofs/Envelope.lean
  - Demailly (4.24) on ℂ, PROVED: the upper regularization of the upper envelope of a locally
  uniformly bounded above family of subharmonic functions is subharmonic
  Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.

  Route: u = sup u_i, u⋆ = uscRegC u. (1) u⋆ ≠ ⊤ (local uniform bound) and u⋆ is usc. (2) For a usc
  T : ℂ → ℝ bounded below, z ↦ circleAverage T z r is usc: Fatou's lemma over the filter 𝓝 c (lintegral_liminf_le) for
  ofReal(B - T(circleMap z r θ)), B a bound of T near the circle. (3) T = potentialTrunc n ∘ u⋆, F z = circleAverage T z r: every
  member has potentialTrunc n (u_i z) ≤ avg u_i ≤ F z, so u ≤ F, so u⋆ ≤ F⋆ = F (F usc), so potentialTrunc n (u⋆ c) ≤ F c.
-/
import GKSharp.Defs.Envelope
import GKSharp.Proofs.SubharmonicBasic

open Real Metric Set Filter Topology MeasureTheory

namespace GKSharp

namespace Envelope

/-! ### Truncation and integrability for usc functions -/

/-- The truncation of a usc function with no value `⊤` is usc (Sector.trunc_usc without the sub-mean part). -/
theorem trunc_usc' {V : ℂ → EReal} (hne : ∀ z, V z ≠ ⊤) (husc : UpperSemicontinuous V) (n : ℕ) :
    UpperSemicontinuous (fun z => potentialTrunc n (V z)) := by
  intro z y hy
  have hne0 : max (V z) (-(n : EReal)) ≠ ⊤ := max_ne_top (hne z) (by simp)
  have hnb : max (V z) (-(n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (le_max_right _ _)
  have hy' : max (V z) (-(n : EReal)) < (y : EReal) := by
    have : ((potentialTrunc n (V z) : ℝ) : EReal) < (y : EReal) := EReal.coe_lt_coe_iff.mpr hy
    unfold potentialTrunc at this; rwa [EReal.coe_toReal hne0 hnb] at this
  have h1 : V z < (y : EReal) := lt_of_le_of_lt (le_max_left _ _) hy'
  have h2 : -(n : EReal) < (y : EReal) := lt_of_le_of_lt (le_max_right _ _) hy'
  filter_upwards [husc z y h1] with z' hz'
  have hm : max (V z') (-(n : EReal)) < (y : EReal) := max_lt hz' h2
  have hne' : max (V z') (-(n : EReal)) ≠ ⊤ := ne_top_of_lt hm
  have hnb' : max (V z') (-(n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (le_max_right _ _)
  unfold potentialTrunc
  rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal hne' hnb']
  exact hm

/-- A usc function bounded below is integrable on every circle. -/
theorem usc_circleIntegrable {T : ℂ → ℝ} (hT : UpperSemicontinuous T) {L : ℝ} (hL : ∀ z, L ≤ T z) (c : ℂ) (r : ℝ) :
    CircleIntegrable T c r := by
  have hcomp : UpperSemicontinuous (fun θ : ℝ => T (circleMap c r θ)) :=
    fun θ => (hT (circleMap c r θ)).comp (continuous_circleMap c r).continuousAt
  obtain ⟨B, hB⟩ := (hcomp.upperSemicontinuousOn (Icc 0 (2 * π))).bddAbove_of_isCompact isCompact_Icc
  have hmeas : Measurable (fun θ : ℝ => T (circleMap c r θ)) := hcomp.measurable
  unfold CircleIntegrable
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le two_pi_pos.le]
  refine Measure.integrableOn_of_bounded (M := max B (-L)) measure_Icc_lt_top.ne hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Eventually.of_forall (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have hup : T (circleMap c r θ) ≤ B := hB ⟨θ, hθ, rfl⟩
  have hlo := hL (circleMap c r θ)
  constructor
  · linarith [le_max_right B (-L)]
  · linarith [le_max_left B (-L)]

theorem trunc_circleIntegrable {V : ℂ → EReal} (hV : IsSubharmonic V) (n : ℕ) (c : ℂ) (r : ℝ) :
    CircleIntegrable (fun z => potentialTrunc n (V z)) c r :=
  usc_circleIntegrable (trunc_usc' hV.1 hV.2.1 n) (fun z => SubharmonicBasic.trunc_ge (hV.1 z) n) c r

/-! ### The upper regularization -/

theorem le_uscRegC (u : ℂ → EReal) (z : ℂ) : u z ≤ uscRegC u z := by
  unfold uscRegC
  exact le_iInf fun ε => le_iSup₂_of_le z (mem_ball_self ε.2) le_rfl

/-- `u⋆` is upper semicontinuous. -/
theorem uscRegC_usc (u : ℂ → EReal) : UpperSemicontinuous (uscRegC u) := by
  intro z y hy
  obtain ⟨ε, hε⟩ := iInf_lt_iff.mp hy
  have hε2 : (0 : ℝ) < (ε : ℝ) / 2 := half_pos ε.2
  filter_upwards [ball_mem_nhds z hε2] with z' hz'
  refine lt_of_le_of_lt ?_ hε
  unfold uscRegC
  refine (iInf_le _ ⟨(ε : ℝ) / 2, hε2⟩).trans (biSup_mono fun w hw => ?_)
  have hsub : ball z' ((ε : ℝ) / 2) ⊆ ball z (ε : ℝ) :=
    ball_subset_ball' (by rw [mem_ball] at hz'; linarith)
  exact hsub hw

/-- `u⋆ ≤ F` for a usc real `F ≥ u`. -/
theorem uscRegC_le_usc {u : ℂ → EReal} {F : ℂ → ℝ} (hF : UpperSemicontinuous F) (hle : ∀ z, u z ≤ (F z : EReal))
    (z : ℂ) : uscRegC u z ≤ (F z : EReal) := by
  rw [← EReal.le_of_forall_lt_iff_le]
  intro b hb
  have hb' : F z < b := EReal.coe_lt_coe_iff.mp hb
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hF z b hb')
  unfold uscRegC
  refine (iInf_le _ ⟨ε, hε⟩).trans ?_
  refine iSup₂_le fun y hy => (hle y).trans ?_
  exact EReal.coe_le_coe_iff.mpr (hball (mem_ball.mp hy)).le

/-- `u⋆ ≠ ⊤` for a locally uniformly bounded above family. -/
theorem uscRegC_ne_top {ι : Type} (u : ι → ℂ → EReal) (hbdd : LocUnifBddAboveC u) (z : ℂ) :
    uscRegC (fun z => ⨆ i, u i z) z ≠ ⊤ := by
  obtain ⟨ε, hε, M, hM⟩ := hbdd z
  have h : uscRegC (fun z => ⨆ i, u i z) z ≤ (M : EReal) := by
    unfold uscRegC
    exact (iInf_le _ ⟨ε, hε⟩).trans (iSup₂_le fun y hy => iSup_le fun i => hM i y hy)
  exact ne_top_of_le_ne_top (EReal.coe_ne_top M) h

/-! ### Circle averages of usc functions are usc (Fatou) -/

theorem continuous_circleMap_center (r θ : ℝ) : Continuous (fun z : ℂ => circleMap z r θ) := by
  unfold circleMap; fun_prop

/-- The pointwise step: `z ↦ ofReal (B - T (circleMap z r θ))` is lsc. -/
theorem lsc_ofReal_sub {T : ℂ → ℝ} (hT : UpperSemicontinuous T) (B r θ : ℝ) :
    LowerSemicontinuous (fun z : ℂ => ENNReal.ofReal (B - T (circleMap z r θ))) := by
  intro c y hy
  have hyt : y ≠ ⊤ := ne_top_of_lt hy
  have hlt : y.toReal < B - T (circleMap c r θ) := (ENNReal.lt_ofReal_iff_toReal_lt hyt).mp hy
  have hev0 : ∀ᶠ w in 𝓝 (circleMap c r θ), T w < B - y.toReal := hT _ _ (by linarith)
  have hev : ∀ᶠ z in 𝓝 c, T (circleMap z r θ) < B - y.toReal :=
    ((continuous_circleMap_center r θ).tendsto c).eventually hev0
  filter_upwards [hev] with z hz
  exact (ENNReal.lt_ofReal_iff_toReal_lt hyt).mpr (by linarith)

/-- The lintegral of `ofReal (B - T ∘ circle)` is `ofReal (2π (B - circleAverage T z r))` when `T ≤ B` on the circle. -/
theorem lintegral_ofReal_sub {T : ℂ → ℝ} (hT : UpperSemicontinuous T) {L : ℝ} (hL : ∀ z, L ≤ T z) {B r : ℝ} {z : ℂ}
    (hB : ∀ θ, T (circleMap z r θ) ≤ B) :
    ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (B - T (circleMap z r θ)) =
      ENNReal.ofReal (2 * π * (B - circleAverage T z r)) := by
  have hint : IntervalIntegrable (fun θ => T (circleMap z r θ)) volume 0 (2 * π) := usc_circleIntegrable hT hL z r
  have hint' : IntegrableOn (fun θ => B - T (circleMap z r θ)) (Ioc 0 (2 * π)) :=
    ((intervalIntegrable_const (c := B)).sub hint).1
  rw [← ofReal_integral_eq_lintegral_ofReal hint' (Eventually.of_forall fun θ => by simp [hB θ])]
  congr 1
  rw [← intervalIntegral.integral_of_le two_pi_pos.le, intervalIntegral.integral_sub intervalIntegrable_const hint,
    intervalIntegral.integral_const, circleAverage_def]
  simp only [sub_zero, smul_eq_mul]
  field_simp

/-- **Circle averages of a usc function bounded below are usc in the center** (Fatou's lemma). -/
theorem circleAverage_usc {T : ℂ → ℝ} (hT : UpperSemicontinuous T) {L : ℝ} (hL : ∀ z, L ≤ T z) (r : ℝ) :
    UpperSemicontinuous (fun z => circleAverage T z r) := by
  intro c y hy
  obtain ⟨B0, hB0⟩ := (hT.upperSemicontinuousOn (closedBall c (|r| + 1))).bddAbove_of_isCompact
    (isCompact_closedBall c _)
  set B := B0 + 1
  have hnear : ∀ z ∈ ball c 1, ∀ θ, T (circleMap z r θ) ≤ B0 := by
    intro z hz θ
    refine hB0 ⟨circleMap z r θ, ?_, rfl⟩
    rw [mem_closedBall]
    calc dist (circleMap z r θ) c ≤ dist (circleMap z r θ) z + dist z c := dist_triangle _ _ _
      _ ≤ |r| + 1 := by
        rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero]
        exact add_le_add le_rfl (mem_ball.mp hz).le
  set g : ℂ → ℝ → ENNReal := fun z θ => ENNReal.ofReal (B - T (circleMap z r θ))
  have hmeas : ∀ z, Measurable (g z) := fun z =>
    ENNReal.measurable_ofReal.comp (measurable_const.sub
      (hT.measurable.comp (continuous_circleMap z r).measurable))
  have hfatou : ∫⁻ θ in Ioc 0 (2 * π), g c θ ≤ liminf (fun z => ∫⁻ θ in Ioc 0 (2 * π), g z θ) (𝓝 c) :=
    (lintegral_mono fun θ => LowerSemicontinuousAt.le_liminf (lsc_ofReal_sub hT B r θ c)).trans (lintegral_liminf_le hmeas)
  have hc : ∫⁻ θ in Ioc 0 (2 * π), g c θ = ENNReal.ofReal (2 * π * (B - circleAverage T c r)) :=
    lintegral_ofReal_sub hT hL fun θ => (hnear c (mem_ball_self one_pos) θ).trans (by simp [B])
  have hFc : circleAverage T c r ≤ B0 :=
    circleAverage_mono_on_of_le_circle (usc_circleIntegrable hT hL c r) fun x hx => by
      refine hB0 ⟨x, ?_, rfl⟩
      rw [mem_closedBall]; rw [mem_sphere] at hx; linarith
  have hlt : ENNReal.ofReal (2 * π * (B - y)) < ∫⁻ θ in Ioc 0 (2 * π), g c θ := by
    rw [hc, ENNReal.ofReal_lt_ofReal_iff (by nlinarith [pi_pos])]
    nlinarith [pi_pos]
  filter_upwards [eventually_lt_of_lt_liminf (hlt.trans_le hfatou), ball_mem_nhds c one_pos] with z hz hzb
  rw [lintegral_ofReal_sub hT hL fun θ => (hnear z hzb θ).trans (by simp [B])] at hz
  have h2 := (ENNReal.ofReal_lt_ofReal_iff'.mp hz).1
  nlinarith [pi_pos]

/-! ### Demailly (4.24) -/

/-- **Demailly (4.24), first part, on ℂ, PROVED** (exact type of `Cited.Textbook.demailly_4_24_envelope`): the upper
regularization of the upper envelope of a locally uniformly bounded above family of subharmonic functions is subharmonic. -/
theorem demailly_4_24 {ι : Type} (u : ι → ℂ → EReal) (hsh : ∀ i, IsSubharmonic (u i))
    (hbdd : LocUnifBddAboveC u) : IsSubharmonic (uscRegC (fun z => ⨆ i, u i z)) := by
  set U := uscRegC (fun z => ⨆ i, u i z) with hUdef
  have hne : ∀ z, U z ≠ ⊤ := uscRegC_ne_top u hbdd
  have husc : UpperSemicontinuous U := uscRegC_usc _
  refine ⟨hne, husc, fun n c r hr => ?_⟩
  set T : ℂ → ℝ := fun z => potentialTrunc n (U z) with hTdef
  have hTusc : UpperSemicontinuous T := trunc_usc' hne husc n
  have hTlow : ∀ z, -(n : ℝ) ≤ T z := fun z => SubharmonicBasic.trunc_ge (hne z) n
  have hTint : ∀ z, CircleIntegrable T z r := fun z => usc_circleIntegrable hTusc hTlow z r
  -- every member lies below `F z = circleAverage T z r`
  have hmem : ∀ i z, u i z ≤ ((circleAverage T z r : ℝ) : EReal) := by
    intro i z
    have hiU : ∀ w, u i w ≤ ((T w : ℝ) : EReal) := fun w =>
      ((le_iSup (fun j => u j w) i).trans (le_uscRegC (fun z => ⨆ i, u i z) w)).trans (SubharmonicBasic.le_trunc (hne w) n)
    have h1 : potentialTrunc n (u i z) ≤ circleAverage (fun w => potentialTrunc n (u i w)) z r := (hsh i).2.2 n z r hr
    have h2 : circleAverage (fun w => potentialTrunc n (u i w)) z r ≤ circleAverage T z r :=
      circleAverage_mono (trunc_circleIntegrable (hsh i) n z r) (hTint z)
        fun w _ => SubharmonicBasic.trunc_le ((hsh i).1 w) (hiU w) n (hTlow w)
    exact (SubharmonicBasic.le_trunc ((hsh i).1 z) n).trans (EReal.coe_le_coe_iff.mpr (h1.trans h2))
  have hUc : U c ≤ ((circleAverage T c r : ℝ) : EReal) :=
    uscRegC_le_usc (circleAverage_usc hTusc hTlow r) (fun z => iSup_le fun i => hmem i z) c
  have hFlow : -(n : ℝ) ≤ circleAverage T c r := by
    have h := circleAverage_mono (circleIntegrable_const (-(n : ℝ)) c r) (hTint c) fun w _ => hTlow w
    rwa [circleAverage_const] at h
  exact SubharmonicBasic.trunc_le (hne c) hUc n hFlow

end Envelope

end GKSharp
