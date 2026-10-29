/- GKSharp/Proofs/GKLowerReal.lean — real GK lower bound from the actual contact.
Frozen source: short_v0.70/sec2_obstacle.tex:35,127; alternative proof of the cited lower bound.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactObstacle
import GKSharp.Proofs.ContactObstacleEndpoint
import GKSharp.Proofs.TheoremR

namespace GKSharp
open Threshold Set Filter
open scoped Topology

namespace ContactLower

lemma contact_minimum (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) :
    ∃ y0 : ℝ, gammaGK p lam y0 (theta p) = 0 ∧ ∀ y : ℝ, 0 ≤ gammaGK p lam y (theta p) := by
  by_cases heq : lam = -1
  · subst lam
    obtain ⟨hz, _, _, hs⟩ := ContactSmooth.endpoint_contact_data p hp hp2
    refine ⟨0, hz, fun y => ?_⟩
    by_cases hy : y = 0
    · simpa only [hy, hz] using (le_refl (0 : ℝ))
    · have hh := hs y hy
      rw [hz] at hh
      exact hh.le
  · have hl : lam ∈ Ioo (-1 : ℝ) 1 := ⟨by by_contra hh; exact heq (by linarith [hlam.1]), hlam.2⟩
    have hz := (contact_spec_proved p lam hp hp2 hl).2.2.2.2.1
    refine ⟨yContact p lam, hz, fun y => ?_⟩
    by_cases hy : y = yContact p lam
    · simpa only [hy, hz] using (le_refl (0 : ℝ))
    · have hh := ContactSmooth.gamma_contact_strict_min p lam hp hp2 hl y hy
      rw [hz] at hh
      exact hh.le

lemma contact_base_pos (p y : ℝ) (hp : 1 < p) :
    0 < 2 * Real.cosh y + 2 * Real.cos (theta p) := by
  have ht0 : 0 < theta p := div_pos Real.pi_pos (by linarith)
  have htpi : theta p < Real.pi := div_lt_self Real.pi_pos hp
  have hc : -1 < Real.cos (theta p) := by
    simpa only [Real.cos_pi] using Real.strictAntiOn_cos
      ⟨ht0.le, htpi.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ htpi
  linarith [Real.one_le_cosh y]

lemma gamma_change_C (p C lam y t : ℝ) :
    GKSharp.gamma p C (lam : ℂ) y t = gammaGK p lam y t +
      (C ^ p - gk p lam ^ p) * (2 * Real.cosh y + 2 * Real.cos t) ^ (p / 2) := by
  unfold gammaGK Threshold.gamma GKSharp.gamma
  ring

lemma ratio_norm_le_one (lam : ℝ) (hlam : lam ∈ Ico (-1 : ℝ) 1) : ‖(lam : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨hlam.1, hlam.2.le⟩

/-- Below GK, both actual contact obstacles are strictly negative. -/
lemma contact_obstacle_negative (p C lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) (hC : 1 < C) (hCG : C < gk p lam) :
    GKSharp.obstacle p C (lam : ℂ) (theta p) < 0 ∧
      GKSharp.obstacle p C (lam : ℂ) (-theta p) < 0 := by
  obtain ⟨y0, hz, _⟩ := contact_minimum p lam hp hp2 hlam
  have hCmax : max 1 ‖(lam : ℂ)‖ < C :=
    lt_of_le_of_lt (max_le le_rfl (ratio_norm_le_one lam hlam)) hC
  have hpow : C ^ p < gk p lam ^ p := Real.rpow_lt_rpow (by linarith) hCG (by linarith)
  have hneg : GKSharp.gamma p C (lam : ℂ) y0 (theta p) < 0 := by
    rw [gamma_change_C, hz, zero_add]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hpow)
      (Real.rpow_pos_of_pos (contact_base_pos p y0 hp) _)
  have hobs : GKSharp.obstacle p C (lam : ℂ) (theta p) < 0 :=
    lt_of_le_of_lt (csInf_le (obstacle_bddBelow (p := p) (by linarith) (lam : ℂ) hCmax _)
      ⟨y0, rfl⟩) hneg
  exact ⟨hobs, by rw [obstacle_even_real]; exact hobs⟩

/-- The complete contact-angle sign assertion from sec2 line127. -/
theorem contact_obstacle_sign (p C lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) (hC : 1 < C) :
    (0 ≤ GKSharp.obstacle p C (lam : ℂ) (theta p) ↔ gk p lam ≤ C) ∧
      (0 ≤ GKSharp.obstacle p C (lam : ℂ) (-theta p) ↔ gk p lam ≤ C) ∧
      Threshold.obstacle p lam (theta p) = 0 ∧ Threshold.obstacle p lam (-theta p) = 0 := by
  obtain ⟨y0, hz, hnonneg⟩ := contact_minimum p lam hp hp2 hlam
  have hiff : 0 ≤ GKSharp.obstacle p C (lam : ℂ) (theta p) ↔ gk p lam ≤ C := by
    constructor
    · intro hh
      by_contra hn
      exact not_lt_of_ge hh (contact_obstacle_negative p C lam hp hp2 hlam hC (lt_of_not_ge hn)).1
    · intro hCG
      apply le_csInf (range_nonempty _)
      rintro _ ⟨y, rfl⟩
      change 0 ≤ GKSharp.gamma p C (lam : ℂ) y (theta p)
      rw [gamma_change_C]
      exact add_nonneg (hnonneg y) (mul_nonneg
        (sub_nonneg.mpr (Real.rpow_le_rpow (gk_nonneg _ _) hCG (by linarith)))
        (Real.rpow_nonneg (contact_base_pos p y hp).le _))
  have hzobs : Threshold.obstacle p lam (theta p) = 0 := by
    have hl : IsLeast (range (fun y => gammaGK p lam y (theta p))) 0 := by
      refine ⟨⟨y0, hz⟩, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact hnonneg y
    exact hl.csInf_eq
  exact ⟨hiff, by rw [obstacle_even_real]; exact hiff, hzobs,
    by rw [threshold_obstacle_even_proved]; exact hzobs⟩

end ContactLower

/-- Real ratios in [-1,1), 1<p<2: GK is a genuine operator-norm lower bound.
This proof uses only the already reviewed Cole input through Theorem R. -/
theorem gk_le_pencilNorm_real (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p)
    (hp : 1 < p) (hp2 : p < 2) (lam : ℝ) (hlam : lam ∈ Ico (-1 : ℝ) 1) :
    gk p lam ≤ pencilNorm P lam := by
  by_contra hn
  have hNG : pencilNorm P (lam : ℂ) < gk p lam := lt_of_not_ge hn
  let C := (pencilNorm P (lam : ℂ) + gk p lam) / 2
  have hNC : pencilNorm P (lam : ℂ) < C := by dsimp [C]; linarith
  have hCG : C < gk p lam := by dsimp [C]; linarith
  have hCmax : max 1 ‖(lam : ℂ)‖ < C := (max_one_le_pencilNorm P _).trans_lt hNC
  have hC1 : 1 < C := lt_of_le_of_lt (le_max_left _ _) hCmax
  obtain ⟨phi, hphi, hle⟩ := thmR_only_if hp P (lam : ℂ) hCmax hNC.le
  have hconv := (TheoremRIf.qsub_continuous_trigconvex_proved (q p) (by unfold q; linarith) phi hphi).2
  have hneg := ContactLower.contact_obstacle_negative p C lam hp hp2 hlam hC1 hCG
  have hright : phi (theta p) < 0 := lt_of_le_of_lt (hle _) hneg.1
  have hleft : phi (-theta p) < 0 := lt_of_le_of_lt (hle _) hneg.2
  have hp0 : p ≠ 0 := by linarith
  have hargp : (Real.pi / 2) / q p = theta p := by unfold q theta; field_simp
  have hargm : (-(Real.pi / 2)) / q p = -theta p := by rw [neg_div, hargp]
  have harch := sec4a_trig_arch hconv
    (by simpa only [hargm] using hleft.le) (by simpa only [hargp] using hright.le)
  have hz : phi (theta p) = 0 := by simpa only [hargp] using harch.2.1
  exact ne_of_lt hright hz

end GKSharp

#print axioms GKSharp.ContactLower.contact_obstacle_sign
#print axioms GKSharp.gk_le_pencilNorm_real
