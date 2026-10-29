/- GKSharp/Proofs/LemmaEContact.lean — complete contact-angle Lemma E.
Frozen source: short_v0.70/sec2_obstacle.tex:127; complete approved O33 target.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GKLowerReal

namespace GKSharp
open Threshold Set

namespace ContactLower

lemma contactRadius_interior (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) : contactRadius p lam = rContact p lam := by
  rw [(contact_gk_radius p lam hp hp2 hlam).1]
  unfold contactRadius contactKappa cs
  rw [abs_of_neg (cos_theta_negative hp hp2)]
  ring

lemma contactRadius_endpoint (p : ℝ) (hp : 1 < p) (hp2 : p < 2) : contactRadius p (-1) = 1 := by
  let C := gk p (-1 : ℝ)
  let aa := 2 + 2 * Real.cos (theta p)
  let bb := 2 - 2 * Real.cos (theta p)
  have hC : 1 < C := lt_of_le_of_lt (le_max_left _ _)
    (gk_gt_max hp (ne_of_lt hp2) (ρ := ((-1 : ℝ) : ℂ)) (by norm_num))
  have haa : 0 < aa := by simpa only [aa, Real.cosh_zero, mul_one] using contact_base_pos p 0 hp
  have hc : Real.cos (theta p) < 0 := cos_theta_negative hp hp2
  have hbb : 0 < bb := by dsimp [bb]; linarith
  have hz := (ContactSmooth.endpoint_contact_data p hp hp2).1
  rw [sec4b_gammaGK_eq] at hz
  norm_num only [Real.cosh_zero, Real.exp_zero, neg_zero, neg_one_sq, one_mul, neg_one_mul,
    mul_neg] at hz
  have hpow : C ^ p * aa ^ (p / 2) = (C ^ 2 * aa) ^ (p / 2) := by
    rw [Real.mul_rpow (sq_nonneg C) haa.le, ← Real.rpow_natCast C 2,
      ← Real.rpow_mul (by linarith : 0 ≤ C)]
    congr 2
    ring
  have heq : C ^ 2 * aa = bb := by
    apply (Real.rpow_left_inj (mul_nonneg (sq_nonneg C) haa.le) hbb.le
      (by linarith : p / 2 ≠ 0)).mp
    rw [← hpow]
    change C ^ p * aa ^ (p / 2) - bb ^ (p / 2) = 0 at hz
    exact sub_eq_zero.mp hz
  have hden : C ^ 2 - 1 ≠ 0 := by nlinarith [sq_nonneg (C - 1)]
  unfold contactRadius contactKappa
  rw [abs_of_neg (cos_theta_negative hp hp2)]
  change (C ^ 2 - -1) / (C ^ 2 - 1) * -Real.cos (theta p) = 1
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hden).mpr
  dsimp [aa, bb] at heq
  nlinarith [heq]

lemma gamma_contact_zero_iff (p lam y : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) :
    gammaGK p lam y (theta p) = 0 ↔ Real.exp y = contactRadius p lam := by
  by_cases heq : lam = -1
  · subst lam
    obtain ⟨hz, _, _, hstrict⟩ := ContactSmooth.endpoint_contact_data p hp hp2
    rw [contactRadius_endpoint p hp hp2, Real.exp_eq_one_iff]
    constructor
    · intro hy
      by_contra hn
      have hh := hstrict y hn
      rw [hz, hy] at hh
      exact lt_irrefl _ hh
    · rintro rfl
      exact hz
  · have hl : lam ∈ Ioo (-1 : ℝ) 1 := ⟨by by_contra hh; exact heq (by linarith [hlam.1]), hlam.2⟩
    have hz := (contact_spec_proved p lam hp hp2 hl).2.2.2.2.1
    have hr := (contact_root_properties hp hp2 hl).1
    have hey : Real.exp (yContact p lam) = rContact p lam := Real.exp_log (by linarith)
    rw [contactRadius_interior p lam hp hp2 hl, ← hey, Real.exp_injective.eq_iff]
    constructor
    · intro hy
      by_contra hn
      have hh := ContactSmooth.gamma_contact_strict_min p lam hp hp2 hl y hn
      rw [hz, hy] at hh
      exact lt_irrefl _ hh
    · rintro rfl
      exact hz

end ContactLower

/-- Complete approved six-clause Lemma E, including lambda=-1 and unique actual radius. -/
theorem slice_O33_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (C lam : ℝ) (hC : 1 < C)
    (hlam : -1 ≤ lam ∧ lam < 1) :
    (0 ≤ GKSharp.obstacle p C (lam : ℂ) (Real.pi / p) ↔ gk p (lam : ℂ) ≤ C) ∧
    (0 ≤ GKSharp.obstacle p C (lam : ℂ) (-(Real.pi / p)) ↔ gk p (lam : ℂ) ≤ C) ∧
    GKSharp.obstacle p (gk p (lam : ℂ)) (lam : ℂ) (Real.pi / p) = 0 ∧
    GKSharp.obstacle p (gk p (lam : ℂ)) (lam : ℂ) (-(Real.pi / p)) = 0 ∧
    ∀ r : ℝ, 0 < r →
      (obstacleG p (gk p (lam : ℂ)) (lam : ℂ) ((r : ℂ) * unitPoint (Real.pi / p)) = 0 ↔
        r = contactRadius p lam) ∧
      (obstacleG p (gk p (lam : ℂ)) (lam : ℂ) ((r : ℂ) * unitPoint (-(Real.pi / p))) = 0 ↔
        r = contactRadius p lam) := by
  obtain ⟨h1, h2, h3, h4⟩ := ContactLower.contact_obstacle_sign p C lam hp hp2 hlam hC
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro r hr
  have hscale (t : ℝ) : gammaGK p lam (Real.log r) t =
      r ^ (-(p / 2)) * obstacleG p (gk p lam) (lam : ℂ) ((r : ℂ) * unitPoint t) := by
    change GKSharp.gamma p (gk p lam) (lam : ℂ) (Real.log r) t = _
    rw [gamma_radial, Real.exp_log hr]
  have hscaleNe : r ^ (-(p / 2)) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hiff (t : ℝ) : obstacleG p (gk p lam) (lam : ℂ) ((r : ℂ) * unitPoint t) = 0 ↔
      gammaGK p lam (Real.log r) t = 0 := by
    rw [hscale, mul_eq_zero]
    simp only [hscaleNe, false_or]
  have hzero : gammaGK p lam (Real.log r) (theta p) = 0 ↔ r = contactRadius p lam := by
    simpa only [Real.exp_log hr] using ContactLower.gamma_contact_zero_iff p lam (Real.log r) hp hp2 hlam
  refine ⟨(hiff _).trans hzero, ?_⟩
  rw [hiff]
  change gammaGK p lam (Real.log r) (-theta p) = 0 ↔ _
  rw [show gammaGK p lam (Real.log r) (-theta p) = gammaGK p lam (Real.log r) (theta p) from
    gamma_even_real p (gk p lam) lam (Real.log r) (theta p)]
  exact hzero

end GKSharp

#print axioms GKSharp.slice_O33_proved
