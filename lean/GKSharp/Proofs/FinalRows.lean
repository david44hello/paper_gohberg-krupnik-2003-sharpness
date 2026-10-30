/-
GKSharp/Proofs/FinalRows.lean — paper 019 short v3.30: proofs of the rows added at the final re-reference pass
(the largest interval (0, λ₁(p)] of Section 4.3, and the small printed facts listed in the row docstrings).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
No Paper import (the rows live in Paper/Statements.lean, which imports this file).
-/
import GKSharp.Proofs.Sec4aEndpoint
import GKSharp.Proofs.PropositionEdge
import GKSharp.Proofs.Sec4bChecks
import GKSharp.Proofs.AxisOrigin
import GKSharp.Proofs.Sec4Continuity
import GKSharp.Proofs.Sec4Near
import GKSharp.Proofs.TheoremCstar
import GKSharp.Proofs.Sec4bLocal
import GKSharp.Proofs.Sec4aBasic
import GKSharp.Proofs.MonotoneSign

namespace GKSharp.Proofs.FinalRows

open Set Filter Topology GKSharp GKSharp.Threshold GKSharp.ComputerChecked

/-- A function continuous on `(−1, 1)`, positive at `0` and negative near `1` has a largest interval `(0, l₁]`,
`0 < l₁ < 1`, on which it is nonnegative. -/
theorem largest_nonneg_interval (f : ℝ → ℝ) (hcont : ContinuousOn f (Ioo (-1) 1)) (h0 : 0 < f 0)
    (hnear : ∃ eps > 0, ∀ x : ℝ, 1 - eps < x → x < 1 → f x < 0) :
    ∃ l1 : ℝ, IsGreatest {l : ℝ | 0 < l ∧ l < 1 ∧ ∀ m ∈ Ioc 0 l, 0 ≤ f m} l1 := by
  obtain ⟨eps, heps, hneg⟩ := hnear
  set S : Set ℝ := {l : ℝ | 0 < l ∧ l < 1 ∧ ∀ m ∈ Ioc 0 l, 0 ≤ f m} with hS
  have hc0 : ContinuousAt f 0 := hcont.continuousAt (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp (hc0.eventually (lt_mem_nhds h0))
  have hl0S : min (d / 2) (1 / 2) ∈ S := by
    refine ⟨lt_min (half_pos hd) (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
    intro m hm
    refine (hball ?_).le
    rw [Real.dist_eq, sub_zero, abs_of_pos hm.1]
    exact lt_of_le_of_lt (hm.2.trans (min_le_left _ _)) (half_lt_self hd)
  have hbound : ∀ l ∈ S, l ≤ 1 - eps := by
    intro l hl
    by_contra hlt
    exact absurd (hl.2.2 l ⟨hl.1, le_rfl⟩) (not_le.mpr (hneg l (not_le.mp hlt) hl.2.1))
  have hne : S.Nonempty := ⟨_, hl0S⟩
  have hbdd : BddAbove S := ⟨1 - eps, hbound⟩
  have hpos : 0 < sSup S := lt_of_lt_of_le hl0S.1 (le_csSup hbdd hl0S)
  have hlt1 : sSup S < 1 := lt_of_le_of_lt (csSup_le hne hbound) (by linarith)
  have hbelow : ∀ m ∈ Ioo 0 (sSup S), 0 ≤ f m := by
    intro m hm
    obtain ⟨s, hs, hms⟩ := exists_lt_of_lt_csSup hne hm.2
    exact hs.2.2 m ⟨hm.1, hms.le⟩
  have hcl : ContinuousAt f (sSup S) :=
    hcont.continuousAt (Ioo_mem_nhds (by linarith) hlt1)
  have hat : 0 ≤ f (sSup S) :=
    ge_of_tendsto (hcl.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_of_mem (Ioo_mem_nhdsLT hpos) hbelow)
  refine ⟨sSup S, ⟨hpos, hlt1, fun m hm => ?_⟩, fun l hl => le_csSup hbdd hl⟩
  rcases hm.2.lt_or_eq with hlt | heq
  · exact hbelow m ⟨hm.1, hlt⟩
  · exact heq ▸ hat

/-- `λ₁(p) < λ_loc(p)` for `1 < p < p_c`: `h(λ_loc(p), p) < 0` while `h ≥ 0` on `(0, λ₁]`. -/
theorem lambda1_lt_lambdaLoc (hc : CheckLocalF) (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver) {p l1 : ℝ}
    (hp1 : 1 < p) (hpc : p < pc) (hl1 : ∀ m ∈ Ioc 0 l1, 0 ≤ h p m) : l1 < lambdaLoc p := by
  have hedge := boundary_edge_proved hc hb hs p hp1 hpc
  have hloc := ((lambdaLoc_spec_proved hc).1 p ⟨hp1, hpc⟩).2
  by_contra hle
  exact absurd (hl1 _ ⟨hloc.1, not_lt.mp hle⟩) (not_le.mpr hedge)

/-- Row `sec4_lambda1_interval`: for `1 < p < p₀`, the largest interval `(0, λ₁(p)]` with `h(·, p) ≥ 0` exists,
`λ₁(p) < 1`, `λ₁(p) < λ_loc(p)` when `p < p_c`, and the bound is sharp for `0 < λ ≤ λ₁(p)`. -/
theorem sec4_lambda1_interval_proved (hn : CheckOmegaNeg) (hr : CheckOmegaRoot) (hc : CheckLocalF)
    (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver) {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (P : RieszProjection p) (hp1 : 1 < p) (hpp0 : p < p0) :
    ∃ lam1 : ℝ, IsGreatest {lam : ℝ | 0 < lam ∧ lam < 1 ∧ ∀ mu ∈ Ioc 0 lam, 0 ≤ h p mu} lam1 ∧
      (p < pc → lam1 < lambdaLoc p) ∧ ∀ lam ∈ Ioc 0 lam1, pencilNorm P lam = gk p lam := by
  obtain ⟨-, -, hb0, -, hneg, -⟩ := p0_spec_proved hn hr
  have hp2 : p < 2 := lt_trans hpp0 (lt_trans hb0 (by norm_num [b0]))
  obtain ⟨l1, hl1⟩ := largest_nonneg_interval (h p) (sec4_h_continuousOn_proved p hp1 hp2)
    (axis_zero_positive_proved p hp1 hp2) (omega_negative_eventual_h_proved p hp1 hp2 (hneg p ⟨hp1, hpp0⟩))
  have hloc1 : p < pc → l1 < lambdaLoc p := fun hpc => lambda1_lt_lambdaLoc hc hb hs hp1 hpc hl1.1.2.2
  refine ⟨l1, hl1, hloc1, fun lam hlam => ?_⟩
  have hlt1 : lam < 1 := lt_of_le_of_lt hlam.2 hl1.1.2.1
  have hloc : lam < lambdaLoc p := by
    rcases lt_or_ge p pc with hpc | hpc
    · exact lt_of_le_of_lt hlam.2 (hloc1 hpc)
    · rw [((lambdaLoc_spec_proved hc).2 p ⟨hpc, hp2⟩)]
      exact hlt1
  have htest : kConst p lam ≤ obstacle p (gk p lam) lam 0 := by
    have := hl1.1.2.2 lam hlam
    simpa [Threshold.h, GKSharp.axisGap, sub_nonneg] using this
  exact (TheoremCstar.thm_Cstar_of TheoremCstar.kf_slope hc hp1 hp2 P
    (fun hpc => boundary_edge_proved hc hb hs p hp1 hpc) hlam.1 hlt1).mpr ⟨htest, hloc⟩

/-- `localTest p λ < 1 ↔ λ < λ_loc(p)` for `1 < p < 2`, `0 < λ < 1` (the "less than" case of Lemma 4.6(b)). -/
theorem localTest_lt_one_iff (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ioo (0 : ℝ) 1) :
    localTest p lam < 1 ↔ lam < lambdaLoc p := by
  obtain ⟨hl0, hl1⟩ := hlam
  have hc := sec4b_cs_pos hp hp2
  have hc4 : 0 < cs p ^ 4 := by positivity
  have hl1' : 0 < 1 + lam := by linarith
  have hu : 0 < (1 - lam) / (1 + lam) := div_pos (by linarith) hl1'
  have h4 : 4 * lam / (1 + lam) ^ 2 = 1 - ((1 - lam) / (1 + lam)) ^ 2 := by
    field_simp
    ring
  have hkey : localTest p lam < 1 ↔ localD2 p < ((1 - lam) / (1 + lam)) ^ 2 := by
    have ht : localTest p lam = p * dual p / 4 * sn p ^ 2 + cs p ^ 4 * (1 - ((1 - lam) / (1 + lam)) ^ 2) := by
      unfold localTest
      rw [← h4]
      ring
    have hD : localD2 p = (p * dual p / 4 * sn p ^ 2 + cs p ^ 4 - 1) / cs p ^ 4 := by
      unfold localD2
      congr 1
      have : sn p ^ 2 = 1 - cs p ^ 2 := by
        have hsc : sn p ^ 2 + cs p ^ 2 = 1 := by
          unfold sn cs
          rw [neg_sq]
          exact Real.sin_sq_add_cos_sq _
        linarith
      rw [this]
      ring
    rw [ht, hD, div_lt_iff₀ hc4]
    constructor <;> intro h <;> linarith
  rw [hkey]
  by_cases hF : 0 < localF p
  · have hDpos : 0 < localD2 p := by
      rw [sec4b_localD2_eq]
      have := sec4a_sn_pos hp
      positivity
    have hk0 : 0 < Real.sqrt (localD2 p) := Real.sqrt_pos.2 hDpos
    have hlam : lambdaLoc p = (1 - Real.sqrt (localD2 p)) / (1 + Real.sqrt (localD2 p)) := by
      unfold lambdaLoc
      rw [ite_eq_left hF]
    rw [hlam, ← Real.sqrt_lt' hu, lt_div_iff₀ hl1', lt_div_iff₀ (by linarith)]
    constructor <;> intro h <;> nlinarith
  · have hlam : lambdaLoc p = 1 := by
      unfold lambdaLoc
      rw [ite_eq_right hF]
    have hD0 : localD2 p ≤ 0 := by
      rw [sec4b_localD2_eq]
      push Not at hF
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
        (by positivity)
    rw [hlam]
    constructor
    · intro _
      exact hl1
    · intro _
      nlinarith [sq_pos_of_pos hu]

/-- `0 < λ_loc(p) ≤ 1` for `1 < p < 2` (Lemma 4.6(b), last sentence; no computer check). -/
theorem lambdaLoc_pos_le_one (p : ℝ) (hp : 1 < p) (hp2 : p < 2) : 0 < lambdaLoc p ∧ lambdaLoc p ≤ 1 := by
  by_cases hF : 0 < localF p
  · have hc := sec4b_cs_pos hp hp2
    have hc4 : 0 < cs p ^ 4 := by positivity
    have hDpos : 0 < localD2 p := by
      rw [sec4b_localD2_eq]
      have := sec4a_sn_pos hp
      positivity
    have hD1 : localD2 p < 1 := by
      have hj := strict_jordan_pp_proved p hp hp2
      have hD : localD2 p = (p * dual p / 4 * sn p ^ 2 + cs p ^ 4 - 1) / cs p ^ 4 := by
        unfold localD2
        congr 1
        have : sn p ^ 2 = 1 - cs p ^ 2 := by
          have hsc : sn p ^ 2 + cs p ^ 2 = 1 := by
            unfold sn cs
            rw [neg_sq]
            exact Real.sin_sq_add_cos_sq _
          linarith
        rw [this]
        ring
      rw [hD, div_lt_one hc4]
      linarith
    have hs0 : 0 < Real.sqrt (localD2 p) := Real.sqrt_pos.2 hDpos
    have hs1 : Real.sqrt (localD2 p) < 1 := by
      rw [Real.sqrt_lt' one_pos]
      linarith
    have hlam : lambdaLoc p = (1 - Real.sqrt (localD2 p)) / (1 + Real.sqrt (localD2 p)) := by
      unfold lambdaLoc
      rw [ite_eq_left hF]
    rw [hlam]
    constructor
    · exact div_pos (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]
      linarith
  · have hlam : lambdaLoc p = 1 := by
      unfold lambdaLoc
      rw [ite_eq_right hF]
    rw [hlam]
    exact ⟨one_pos, le_rfl⟩

/-- Row `sec4_lemma_Pc_b` (Lemma 4.6(b)): for `0 < λ < 1` the left side of (4.2) is `< 1`, `= 1` or `> 1` according
as `λ < λ_loc(p)`, `λ = λ_loc(p)` or `λ > λ_loc(p)`; moreover `0 < λ_loc(p) ≤ 1`. -/
theorem sec4_lemma_Pc_b_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    (∀ lam ∈ Ioo (0 : ℝ) 1, (localTest p lam < 1 ↔ lam < lambdaLoc p) ∧
      (localTest p lam = 1 ↔ lam = lambdaLoc p) ∧ (1 < localTest p lam ↔ lambdaLoc p < lam)) ∧
    0 < lambdaLoc p ∧ lambdaLoc p ≤ 1 := by
  refine ⟨fun lam hlam => ?_, lambdaLoc_pos_le_one p hp hp2⟩
  have hlt := localTest_lt_one_iff p lam hp hp2 hlam
  have hgt := local_threshold_iff_proved p lam hp hp2 hlam
  refine ⟨hlt, ⟨fun heq => ?_, fun heq => ?_⟩, hgt⟩
  · rcases lt_trichotomy lam (lambdaLoc p) with h | h | h
    · exact absurd (hlt.mpr h) (by rw [heq]; exact lt_irrefl 1)
    · exact h
    · exact absurd (hgt.mpr h) (by rw [heq]; exact lt_irrefl 1)
  · rcases lt_trichotomy (localTest p lam) 1 with h | h | h
    · exact absurd (hlt.mp h) (by rw [heq]; exact lt_irrefl _)
    · exact h
    · exact absurd (hgt.mp h) (by rw [heq]; exact lt_irrefl _)

/-- Row `sec5e_routeB_identities` (proof of Theorem 5.3, "If"): at `θ = θ₀ = π/p`, with `m = p/(2 − p)` and
`ω = (1 − q)θ₀`, one has `mω = qθ₀ = π/2`, `sin ω = c₀`, `Ψ_m(ω) = (m²c₀² − 1)/c₀⁴`, `m²/(m² − 1) = pp′/4`,
`1/(m² − 1) = pp′/4 − 1`, `Ψ_m(ω)/(m² − 1) = (1 − (pp′/4)s₀²)/c₀⁴`, and `Ψ_m(ω) > 4(m² − 1)λ/(1 + λ)²` if and only if
`(pp′/4)s₀² + 4λc₀⁴/(1 + λ)² < 1`. -/
theorem sec5e_routeB_identities_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 < lam) :
    p / (2 - p) * ((1 - p / 2) * (Real.pi / p)) = Real.pi / 2 ∧ p / 2 * (Real.pi / p) = Real.pi / 2 ∧
    Real.sin ((1 - p / 2) * (Real.pi / p)) = cs p ∧
    monoPsi (p / (2 - p)) ((1 - p / 2) * (Real.pi / p)) = ((p / (2 - p)) ^ 2 * cs p ^ 2 - 1) / cs p ^ 4 ∧
    (p / (2 - p)) ^ 2 / ((p / (2 - p)) ^ 2 - 1) = p * dual p / 4 ∧
    1 / ((p / (2 - p)) ^ 2 - 1) = p * dual p / 4 - 1 ∧
    monoPsi (p / (2 - p)) ((1 - p / 2) * (Real.pi / p)) / ((p / (2 - p)) ^ 2 - 1) =
      (1 - p * dual p / 4 * sn p ^ 2) / cs p ^ 4 ∧
    (4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 < monoPsi (p / (2 - p)) ((1 - p / 2) * (Real.pi / p)) ↔
      localTest p lam < 1) := by
  have hp0 : p ≠ 0 := by linarith
  have h2p : 2 - p ≠ 0 := by linarith
  have hp1' : p - 1 ≠ 0 := by linarith
  have hc := sec4b_cs_pos hp1 hp2
  have hc4 : 0 < cs p ^ 4 := by positivity
  have hl1 : 0 < 1 + lam := by linarith
  have homega : (1 - p / 2) * (Real.pi / p) = Real.pi / p - Real.pi / 2 := by
    field_simp
  have hmw : p / (2 - p) * ((1 - p / 2) * (Real.pi / p)) = Real.pi / 2 := by
    rw [homega]
    field_simp
  have hqt : p / 2 * (Real.pi / p) = Real.pi / 2 := by
    field_simp
  have hsin : Real.sin ((1 - p / 2) * (Real.pi / p)) = cs p := by
    rw [homega, Real.sin_sub_pi_div_two]
    rfl
  have hpsi : monoPsi (p / (2 - p)) ((1 - p / 2) * (Real.pi / p)) = ((p / (2 - p)) ^ 2 * cs p ^ 2 - 1) / cs p ^ 4 := by
    unfold monoPsi
    rw [hmw, hsin, Real.sin_pi_div_two]
    ring
  have hm2 : (p / (2 - p)) ^ 2 - 1 = 4 * (p - 1) / (2 - p) ^ 2 := by
    field_simp
    ring
  have hm2pos : 0 < (p / (2 - p)) ^ 2 - 1 := by
    rw [hm2]
    have : 0 < (2 - p) ^ 2 := by positivity
    exact div_pos (by linarith) this
  have hdual : p * dual p / 4 = p ^ 2 / (4 * (p - 1)) := by
    unfold dual
    field_simp
  have hA : (p / (2 - p)) ^ 2 / ((p / (2 - p)) ^ 2 - 1) = p * dual p / 4 := by
    rw [hm2, hdual]
    field_simp
  have hB : 1 / ((p / (2 - p)) ^ 2 - 1) = p * dual p / 4 - 1 := by
    rw [hm2, hdual]
    field_simp
    ring
  have hsc : sn p ^ 2 = 1 - cs p ^ 2 := by
    have : sn p ^ 2 + cs p ^ 2 = 1 := by
      unfold sn cs
      rw [neg_sq]
      exact Real.sin_sq_add_cos_sq _
    linarith
  have hC : monoPsi (p / (2 - p)) ((1 - p / 2) * (Real.pi / p)) / ((p / (2 - p)) ^ 2 - 1) =
      (1 - p * dual p / 4 * sn p ^ 2) / cs p ^ 4 := by
    rw [hpsi, hsc]
    have e1 : ((p / (2 - p)) ^ 2 * cs p ^ 2 - 1) / cs p ^ 4 / ((p / (2 - p)) ^ 2 - 1) =
        ((p / (2 - p)) ^ 2 / ((p / (2 - p)) ^ 2 - 1) * cs p ^ 2 - 1 / ((p / (2 - p)) ^ 2 - 1)) / cs p ^ 4 := by
      field_simp
    rw [e1, hA, hB]
    ring
  refine ⟨hmw, hqt, hsin, hpsi, hA, hB, hC, ?_⟩
  have hiff : 4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 <
      monoPsi (p / (2 - p)) ((1 - p / 2) * (Real.pi / p)) ↔
      4 * lam / (1 + lam) ^ 2 < (1 - p * dual p / 4 * sn p ^ 2) / cs p ^ 4 := by
    rw [← hC, lt_div_iff₀ hm2pos]
    constructor <;> intro h <;> [skip; skip] <;> ring_nf at h ⊢ <;> linarith
  rw [hiff, lt_div_iff₀ hc4]
  unfold localTest
  constructor <;> intro h <;> [skip; skip] <;> ring_nf at h ⊢ <;> linarith

/-- Row `sec5e_Kf_slope_routeB` (proof of Theorem 5.3, "If", route of short v3.30): for `1 < p < 2` and
`0 < λ < λ_loc(p)`, `λ < 1`, `K_f′(θ₀) < 0` (Lemma 4.6(b), the identities above, and Lemma 5.8). -/
theorem sec5e_Kf_slope_routeB_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hloc : lam < lambdaLoc p) : deriv (curveKf p lam) (Real.pi / p) < 0 := by
  have hθ0 : 0 < Real.pi / p := div_pos Real.pi_pos (by linarith)
  have hθ : Real.pi / p < Real.pi := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [Real.pi_pos]
  have htest : localTest p lam < 1 := (localTest_lt_one_iff p lam hp1 hp2 ⟨hl0, hl1⟩).mpr hloc
  have hgt := ((sec5e_routeB_identities_proved hp1 hp2 (by linarith : -1 < lam)).2.2.2.2.2.2.2).mpr htest
  have hsign := (lemma_onevar_proved hp1 hp2 (by linarith : -1 < lam) hl1 hθ0 hθ).2
  rw [sign_neg (sub_neg.mpr hgt)] at hsign
  exact sign_eq_neg_one_iff.mp hsign

/-- `x log x` decreases on `(0, 1/e]` (its derivative `log x + 1` is `≤ 0` there). -/
theorem mul_log_antitoneOn : AntitoneOn (fun x : ℝ => x * Real.log x) (Ioc 0 (Real.exp (-1))) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 _) Real.continuous_mul_log.continuousOn
  · rw [interior_Ioc]
    exact Real.differentiableOn_mul_log.mono (fun x hx => hx.1.ne')
  · intro x hx
    rw [interior_Ioc] at hx
    rw [Real.deriv_mul_log hx.1.ne']
    have := (Real.log_lt_iff_lt_exp hx.1).2 hx.2
    linarith

/-- `x^x` decreases on `(0, 1/e]`. -/
theorem rpow_self_antitoneOn : AntitoneOn (fun x : ℝ => x ^ x) (Ioc 0 (Real.exp (-1))) := by
  intro x hx y hy hxy
  simp only
  rw [Real.rpow_def_of_pos hx.1, Real.rpow_def_of_pos hy.1, mul_comm (Real.log x), mul_comm (Real.log y)]
  exact Real.exp_le_exp.2 (mul_log_antitoneOn hx hy hxy)

/-- `0.001^{0.001} > 0.9931`: `0.001^{0.001} = e^{−y}`, `y = log 1000/1000 ≤ (10 log 2 + (1000/1024 − 1))/1000`,
and `e^{−y} ≥ (1 − y/2)²`. -/
theorem thousandth_rpow_gt : (9931 / 10000 : ℝ) < (1 / 1000 : ℝ) ^ (1 / 1000 : ℝ) := by
  have hL : Real.log 2 < 6931471808 / 10000000000 := by linarith [Real.log_two_lt_d9]
  have h3 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  have h2 : Real.log (1000 / 1024 : ℝ) = Real.log 1000 - Real.log 1024 :=
    Real.log_div (by norm_num) (by norm_num)
  have h1 : Real.log (1000 / 1024 : ℝ) ≤ 1000 / 1024 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hpos : 0 < Real.log 1000 := Real.log_pos (by norm_num)
  have hlog : Real.log (1 / 1000 : ℝ) = -Real.log 1000 := by rw [one_div, Real.log_inv]
  rw [Real.rpow_def_of_pos (by norm_num), hlog]
  set y := Real.log 1000 / 1000 with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyle : y ≤ 69080344 / 10000000000 := by rw [hy, div_le_iff₀ (by norm_num)]; linarith
  have hexp := Real.one_sub_div_pow_le_exp_neg (n := 2) (t := y) (by norm_num; linarith)
  simp only [Nat.cast_ofNat] at hexp
  have hc : (1 - 69080344 / 20000000000 : ℝ) ≤ 1 - y / 2 := by linarith
  have hsq := pow_le_pow_left₀ (by norm_num) hc 2
  rw [show -Real.log 1000 * (1 / 1000) = -y by rw [hy]; ring]
  have hnum : (9931 / 10000 : ℝ) < (1 - 69080344 / 20000000000) ^ 2 := by norm_num
  linarith

/-- Proposition 4.3, proof (range `1 < p`, `p − 1 ≤ 0.001`): Jordan's inequality `s₀ ≥ 2(p−1)/p`, then
`s₀^{p−1} ≥ (p−1)^{p−1} ≥ 0.001^{0.001} > 0.9931`, since `x^x` decreases on `(0, 1/e]`. -/
theorem sec4_omega_endpoint_chain_proved {p : ℝ} (hp : 1 < p) (hhi : p - 1 ≤ 1 / 1000) :
    2 * (p - 1) / p ≤ sn p ∧ (p - 1) ^ (p - 1) ≤ sn p ^ (p - 1) ∧
    (1 / 1000 : ℝ) ^ (1 / 1000 : ℝ) ≤ (p - 1) ^ (p - 1) ∧
    (9931 / 10000 : ℝ) < (1 / 1000 : ℝ) ^ (1 / 1000 : ℝ) ∧
    AntitoneOn (fun x : ℝ => x ^ x) (Ioc 0 (Real.exp (-1))) := by
  have hp0 : 0 < p := by linarith
  have he0 : 0 ≤ p - 1 := by linarith
  have hx0 : 0 ≤ Real.pi - Real.pi / p := by
    have : Real.pi / p ≤ Real.pi := div_le_self Real.pi_pos.le hp.le
    linarith
  have hx1 : Real.pi - Real.pi / p ≤ Real.pi / 2 := by
    have : Real.pi / 2 ≤ Real.pi / p := by
      rw [div_le_div_iff₀ two_pos hp0]
      nlinarith [Real.pi_pos]
    linarith
  have hsn : sn p = Real.sin (Real.pi - Real.pi / p) := by rw [Real.sin_pi_sub]; rfl
  have hJ : 2 * (p - 1) / p ≤ sn p := by
    rw [hsn]
    have h := Real.mul_le_sin hx0 hx1
    have he : 2 / Real.pi * (Real.pi - Real.pi / p) = 2 * (p - 1) / p := by
      field_simp
    linarith
  have hle : p - 1 ≤ 2 * (p - 1) / p := by
    rw [le_div_iff₀ hp0]
    nlinarith
  have he1 : (1 / 1000 : ℝ) ≤ Real.exp (-1) := by linarith [Real.exp_neg_one_gt_d9]
  refine ⟨hJ, Real.rpow_le_rpow he0 (hle.trans hJ) he0, ?_, thousandth_rpow_gt, rpow_self_antitoneOn⟩
  exact rpow_self_antitoneOn ⟨by linarith, hhi.trans he1⟩ ⟨by norm_num, he1⟩ hhi

end GKSharp.Proofs.FinalRows
