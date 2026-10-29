/- GKSharp/Proofs/Sec4bChecks.lean - slice (b): the PROVED-GIVEN threshold rows of sec4b (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v0.80, each as `<row>_proved` with the row's exact type. The computer checks
(GKSharp.ComputerChecked.Check...) enter ONLY as the rows' own explicit hypotheses.
- pc_spec (B:93-103): `localF > 0` on `(1, 1.2134]` (localF_endpoint_one, CheckLocalF), `< 0` on `[1.2136, 2)`
  (CheckLocalF, localF_endpoint_two), strictly decreasing on `[1.2134, 1.2136]` (`deriv localF < 0` there, which also
  gives continuity); the kernel bracket signs at `1.213490304`, `1.213490305` and the intermediate value theorem give the
  one zero `z`, so `localZeros = {z}` and `pc = z`.
- lambdaLoc_spec (B:20-21): `0 < localD2 < 1` below `pc` (`localD2 < 1` is strict_jordan_pp), so `λ_loc ∈ (0, 1)`.
- deltaLoc_gap (B:135-136): `1 - λ_loc = 2√D/(1 + √D) ≤ 2√D ≤ 0.03` (CheckLocalGap).
- boundary_sliver (B:134-136): `δ = 1 - λ_loc ∈ (0, 0.03]`, h_le_delta_g at `s = 1371/5000`, CheckBoundarySliver.
  Premise row: cDelta_eq_gk (through h_le_delta_g).
- boundary_bulk (B:121-123): the witness `θ` of CheckBoundaryBulk forces `λ_loc ≠ 1` (the bound is `0` at `λ = 1`), so
  `λ_loc ∈ (0, 1)`, and h_le_axisUpper gives `h ≤ bound < 0`.
-/
import GKSharp.Proofs.Sec4bLocal
import GKSharp.Proofs.Sec4bAxis
import GKSharp.Proofs.LocalFCertificate
import GKSharp.Proofs.GKSymm
import GKSharp.ComputerChecked

namespace GKSharp

open Set GKSharp.Threshold GKSharp.ComputerChecked

/-- `localD2 = (J + cs⁴ - 1)/cs⁴` with `J = pp'/4 · sn²`. -/
lemma sec4b_localD2_eq' (p : ℝ) : localD2 p = (p * dual p / 4 * sn p ^ 2 + cs p ^ 4 - 1) / cs p ^ 4 := by
  have hsc : sn p ^ 2 + cs p ^ 2 = 1 := by
    unfold sn cs
    rw [neg_sq]
    exact Real.sin_sq_add_cos_sq _
  unfold localD2
  congr 1
  have : sn p ^ 2 = 1 - cs p ^ 2 := by linarith
  rw [this]
  ring

/-- `localD2 < 1` on `(1, 2)` (strict Jordan). -/
lemma sec4b_localD2_lt_one {p : ℝ} (hp : 1 < p) (hp2 : p < 2) : localD2 p < 1 := by
  have hc4 : 0 < cs p ^ 4 := pow_pos (sec4b_cs_pos hp hp2) 4
  have hJ := strict_jordan_pp_proved p hp hp2
  rw [sec4b_localD2_eq', div_lt_one hc4]
  linarith

/-- `localD2 > 0` where `localF > 0`. -/
lemma sec4b_localD2_pos {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (hF : 0 < localF p) : 0 < localD2 p := by
  rw [sec4b_localD2_eq]
  exact div_pos (mul_pos (pow_pos (sec4a_sn_pos hp) 2) (by linarith)) (pow_pos (sec4b_cs_pos hp hp2) 4)

/-- `λ_loc = (1 - √D)/(1 + √D) ∈ (0, 1)` where `localF > 0`. -/
lemma sec4b_lambdaLoc_mem {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (hF : 0 < localF p) :
    lambdaLoc p = (1 - Real.sqrt (localD2 p)) / (1 + Real.sqrt (localD2 p)) ∧ lambdaLoc p ∈ Ioo (0 : ℝ) 1 := by
  have hk0 : 0 < Real.sqrt (localD2 p) := Real.sqrt_pos.2 (sec4b_localD2_pos hp hp2 hF)
  have hk1 : Real.sqrt (localD2 p) < 1 :=
    calc Real.sqrt (localD2 p) < Real.sqrt 1 :=
          Real.sqrt_lt_sqrt (sec4b_localD2_pos hp hp2 hF).le (sec4b_localD2_lt_one hp hp2)
      _ = 1 := Real.sqrt_one
  have hlam : lambdaLoc p = (1 - Real.sqrt (localD2 p)) / (1 + Real.sqrt (localD2 p)) := by
    unfold lambdaLoc
    rw [ite_eq_left hF]
  refine ⟨hlam, ?_, ?_⟩
  · rw [hlam]
    exact div_pos (by linarith) (by linarith)
  · rw [hlam, div_lt_one (by linarith)]
    linarith

/-- B:93-103, row `pc_spec`. -/
theorem pc_spec_proved (hc : CheckLocalF) :
    IsLeast localZeros pc ∧ pc ∈ Ioo (1213490304 / 1000000000 : ℝ) (1213490305 / 1000000000) ∧
    (∀ p ∈ Ioo (1 : ℝ) 2, localF p = 0 ↔ p = pc) ∧
    (∀ p ∈ Ioo (1 : ℝ) 2, 0 < localF p ↔ p < pc) ∧
    deriv localF pc < 0 := by
  obtain ⟨h1, h2, h3⟩ := hc
  have hpos : ∀ p ∈ Ioc (1 : ℝ) (6067 / 5000), 0 < localF p := by
    rintro p ⟨hp1, hp2⟩
    by_cases hp : p ≤ 1000001 / 1000000
    · exact (localF_endpoint_one_proved p hp1 hp).2
    · push Not at hp
      exact h1 p ⟨hp.le, hp2⟩
  have hneg : ∀ p ∈ Ico (1517 / 1250 : ℝ) 2, localF p < 0 := by
    rintro p ⟨hp1, hp2⟩
    by_cases hp : p ≤ 3 / 2
    · exact h2 p ⟨hp1, hp⟩
    · push Not at hp
      exact (localF_endpoint_two_proved p hp.le hp2).2
  have hcont : ContinuousOn localF (Icc (6067 / 5000 : ℝ) (1517 / 1250)) := fun x hx =>
    (differentiableAt_of_deriv_ne_zero (h3 x hx).ne).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn localF (Icc (6067 / 5000 : ℝ) (1517 / 1250)) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont fun x hx => h3 x (interior_subset hx)
  have hsub : Icc (1213490304 / 1000000000 : ℝ) (1213490305 / 1000000000) ⊆ Icc (6067 / 5000) (1517 / 1250) :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' (by norm_num) (hcont.mono hsub)
    ⟨localF_bracket_upper, localF_bracket_lower⟩
  have hzab : z ∈ Icc (6067 / 5000 : ℝ) (1517 / 1250) := hsub (Ioo_subset_Icc_self hz)
  have hzero : ∀ p ∈ Ioo (1 : ℝ) 2, localF p = 0 ↔ p = z := by
    rintro p ⟨hp1, hp2⟩
    constructor
    · intro hp
      by_cases ha : p ≤ 6067 / 5000
      · exact absurd hp (hpos p ⟨hp1, ha⟩).ne'
      by_cases hb : 1517 / 1250 ≤ p
      · exact absurd hp (hneg p ⟨hb, hp2⟩).ne
      push Not at ha hb
      exact hanti.injOn ⟨ha.le, hb.le⟩ hzab (hp.trans hz0.symm)
    · rintro rfl
      exact hz0
  have hZ : localZeros = {z} := by
    ext p
    rw [mem_singleton_iff]
    constructor
    · rintro ⟨hp1, hp2, hp⟩
      exact (hzero p ⟨hp1, hp2⟩).1 hp
    · rintro rfl
      exact ⟨by linarith [hzab.1], by linarith [hzab.2], hz0⟩
  have hpc : pc = z := by
    unfold pc
    rw [hZ, csInf_singleton]
  rw [hpc]
  refine ⟨by rw [hZ]; exact isLeast_singleton, hz, hzero, ?_, h3 z hzab⟩
  rintro p ⟨hp1, hp2⟩
  constructor
  · intro hp
    by_contra hge
    push Not at hge
    by_cases hb : 1517 / 1250 ≤ p
    · linarith [hneg p ⟨hb, hp2⟩]
    push Not at hb
    have hpab : p ∈ Icc (6067 / 5000 : ℝ) (1517 / 1250) := ⟨le_trans hzab.1 hge, hb.le⟩
    rcases hge.lt_or_eq with hlt | heq
    · have := hanti hzab hpab hlt
      linarith
    · rw [← heq] at hp
      linarith
  · intro hp
    by_cases ha : p ≤ 6067 / 5000
    · exact hpos p ⟨hp1, ha⟩
    push Not at ha
    have hpab : p ∈ Icc (6067 / 5000 : ℝ) (1517 / 1250) := ⟨ha.le, by linarith [hzab.2]⟩
    have := hanti hpab hzab hp
    linarith

/-- B:20-21, row `lambdaLoc_spec`. -/
theorem lambdaLoc_spec_proved (hc : CheckLocalF) :
    (∀ p ∈ Ioo (1 : ℝ) pc, localD2 p ∈ Ioo (0 : ℝ) 1 ∧ lambdaLoc p ∈ Ioo (0 : ℝ) 1) ∧
    (∀ p ∈ Ico pc (2 : ℝ), lambdaLoc p = 1) := by
  obtain ⟨-, ⟨hlo, hhi⟩, -, hsign, -⟩ := pc_spec_proved hc
  constructor
  · rintro p ⟨hp1, hp2⟩
    have hp2' : p < 2 := by linarith
    have hF : 0 < localF p := (hsign p ⟨hp1, hp2'⟩).2 hp2
    exact ⟨⟨sec4b_localD2_pos hp1 hp2' hF, sec4b_localD2_lt_one hp1 hp2'⟩, (sec4b_lambdaLoc_mem hp1 hp2' hF).2⟩
  · rintro p ⟨hp1, hp2⟩
    have hp1' : 1 < p := by linarith
    have hF : ¬ 0 < localF p := fun h => absurd ((hsign p ⟨hp1', hp2⟩).1 h) (not_lt.2 hp1)
    unfold lambdaLoc
    rw [ite_eq_right hF]

/-- B:135-136, row `deltaLoc_gap`. -/
theorem deltaLoc_gap_proved (hc : CheckLocalF) (hg : CheckLocalGap) (p : ℝ)
    (hp : p ∈ Ico (6067 / 5000 : ℝ) pc) :
    0 < 1 - lambdaLoc p ∧ 1 - lambdaLoc p ≤ 3 / 100 := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨-, ⟨hlo, hhi⟩, -, hsign, -⟩ := pc_spec_proved hc
  have hp1' : 1 < p := by linarith
  have hp2' : p < 2 := by linarith
  have hF : 0 < localF p := (hsign p ⟨hp1', hp2'⟩).2 hp2
  have hDpos := sec4b_localD2_pos hp1' hp2' hF
  have hgap := hg p ⟨hp1, by linarith⟩
  rw [max_eq_left hDpos.le] at hgap
  have hk0 : 0 < Real.sqrt (localD2 p) := Real.sqrt_pos.2 hDpos
  have h1 : 1 - lambdaLoc p = 2 * Real.sqrt (localD2 p) / (1 + Real.sqrt (localD2 p)) := by
    rw [(sec4b_lambdaLoc_mem hp1' hp2' hF).1, eq_div_iff (by linarith), sub_mul,
      div_mul_cancel₀ _ (by linarith)]
    ring
  rw [h1]
  constructor
  · exact div_pos (by linarith) (by linarith)
  · rw [div_le_iff₀ (by linarith)]
    linarith

/-- B:134-136, row `boundary_sliver` (premise row `cDelta_eq_gk`, through h_le_delta_g). -/
theorem boundary_sliver_proved (hcd : CDeltaEqGkHyp) (hc : CheckLocalF) (hs : CheckBoundarySliver)
    (hg : CheckLocalGap) (p : ℝ) (hp : p ∈ Ico (6067 / 5000 : ℝ) pc) :
    Threshold.h p (lambdaLoc p) < 0 := by
  obtain ⟨hd0, hd1⟩ := deltaLoc_gap_proved hc hg p hp
  obtain ⟨-, ⟨hlo, hhi⟩, -, -, -⟩ := pc_spec_proved hc
  obtain ⟨hp1, hp2⟩ := hp
  have hle := h_le_delta_g_proved hcd p (1 - lambdaLoc p) (1371 / 5000) (by linarith) (by linarith)
    ⟨hd0, by linarith⟩ ⟨by norm_num, by norm_num⟩
  rw [show (1 : ℝ) - (1 - lambdaLoc p) = lambdaLoc p by ring] at hle
  have hgneg := hs p ⟨hp1, by linarith⟩ (1 - lambdaLoc p) ⟨hd0.le, hd1⟩
  nlinarith

/-- B:121-123, row `boundary_bulk`. -/
theorem boundary_bulk_proved (hb : CheckBoundaryBulk) (p : ℝ)
    (hp : p ∈ Icc (1000001 / 1000000 : ℝ) (6067 / 5000)) :
    Threshold.h p (lambdaLoc p) < 0 := by
  obtain ⟨hp1, hp2⟩ := hp
  have hp1' : 1 < p := by linarith
  have hp2' : p < 2 := by linarith
  obtain ⟨θ, hθ, hneg⟩ := hb p ⟨hp1, hp2⟩
  have hF : 0 < localF p := by
    by_contra hF
    have h1 : lambdaLoc p = 1 := by
      unfold lambdaLoc
      rw [ite_eq_right hF]
    rw [h1] at hneg
    have h0 : axisUpper p 1 θ = 0 := by
      unfold axisUpper kConst
      simp [gk_one]
    linarith
  obtain ⟨-, hmem⟩ := sec4b_lambdaLoc_mem hp1' hp2' hF
  have hle := h_le_axisUpper_proved p (lambdaLoc p) θ hp1' hp2' ⟨hmem.1.le, hmem.2⟩ hθ
  linarith

end GKSharp
