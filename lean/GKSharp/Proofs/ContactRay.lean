/- GKSharp/Proofs/ContactRay.lean — identify the contact with the actual matrix norm.
Frozen source: short_v0.40/sec4b_failure.tex:28–32.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactScalar
import GKSharp.Proofs.GKProps

namespace GKSharp
open Threshold Set

set_option maxHeartbeats 600000 in
/-- The actual contact radius is the matrix-GK radius, and determines its
squared norm. No analytic contact or maximum hypothesis is assumed. -/
theorem contact_gk_radius (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    rContact p lam = cs p * (gk p lam ^ 2 - lam) / (gk p lam ^ 2 - 1) ∧
      gk p lam ^ 2 = (rContact p lam ^ 2 - lam ^ 2) / (rContact p lam ^ 2 - 1) := by
  let CC : ℝ := gk p lam
  have hC1 : 1 < CC := by
    exact lt_of_le_of_lt (le_max_left _ _)
      (gk_gt_max hp (ne_of_lt hp2) (ρ := (lam : ℂ)) (by
        intro hh
        have hh' : lam = 1 := by exact_mod_cast hh
        linarith [hlam.2]))
  have hC0 : 0 < CC := by linarith
  have hden : 0 < CC ^ 2 - 1 := by nlinarith
  have hD : 0 < CC ^ 2 - lam := by linarith [hlam.2]
  have hp0 : 0 < p := by linarith
  have hc : 0 < cs p := by
    unfold cs
    apply neg_pos.mpr
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · rw [lt_div_iff₀ hp0]
      nlinarith [Real.pi_pos]
    · have ht : Real.pi / p < Real.pi := by
        rw [div_lt_iff₀ hp0]
        nlinarith [Real.pi_pos]
      linarith [Real.pi_pos]
  have htrig : sn p ^ 2 + cs p ^ 2 = 1 := by simp [sn, cs]
  have hCeq : (1 - lam) * CC = sn p * (CC ^ 2 - lam) := (gk_real_eq hp hlam.2).1
  have hCsq := congrArg (fun x : ℝ => x ^ 2) hCeq
  have hid : cs p ^ 2 * (CC ^ 2 - lam) ^ 2 = (CC ^ 2 - 1) * (CC ^ 2 - lam ^ 2) := by
    linear_combination (CC ^ 2 - lam) ^ 2 * htrig + hCsq
  let rr : ℝ := cs p * (CC ^ 2 - lam) / (CC ^ 2 - 1)
  have hrr0 : 0 < rr := div_pos (mul_pos hc hD) hden
  have hrrsq : rr ^ 2 = (CC ^ 2 - lam ^ 2) / (CC ^ 2 - 1) := by
    dsimp only [rr]
    rw [div_pow, mul_pow, hid]
    field_simp [ne_of_gt hden]
    <;> ring
  have hlamsq : lam ^ 2 < 1 := by
    nlinarith [mul_pos (show 0 < 1 - lam by linarith [hlam.2])
      (show 0 < 1 + lam by linarith [hlam.1])]
  have hrr1 : 1 < rr := by
    have hh : 1 < rr ^ 2 := by
      rw [hrrsq, lt_div_iff₀ hden]
      linarith
    nlinarith only [hh, hrr0]
  have hrrquad : rr ^ 2 + lam = sigmaContact p lam * rr := by
    rw [hrrsq]
    dsimp only [sigmaContact, rr]
    field_simp [ne_of_gt hc, ne_of_gt hden]
    <;> ring
  obtain ⟨hr, _, _, hsum⟩ := contact_root_properties hp hp2 hlam
  have hr0 : rContact p lam ≠ 0 := by linarith
  have hroot : rContact p lam ^ 2 + lam = sigmaContact p lam * rContact p lam := by
    field_simp [hr0] at hsum
    nlinarith only [hsum]
  have hfac : (rr - rContact p lam) * (rr * rContact p lam - lam) = 0 := by
    linear_combination rContact p lam * hrrquad - rr * hroot
  have hprod : 0 < rr * rContact p lam - lam := by
    nlinarith only [hrr1, hr, mul_pos (sub_pos.mpr hrr1) (sub_pos.mpr hr), hlam.2]
  have heq : rr = rContact p lam :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right (ne_of_gt hprod))
  have hrden : rContact p lam ^ 2 - 1 ≠ 0 := by
    nlinarith only [hr, sq_nonneg (rContact p lam - 1)]
  refine ⟨heq.symm, ?_⟩
  change CC ^ 2 = _
  rw [heq] at hrrsq
  apply (eq_div_iff hrden).mpr
  field_simp [ne_of_gt hden] at hrrsq
  nlinarith only [hrrsq]

/-- The complete squared ray inequality is a nonnegative square, with its
unique zero at the actual chosen contact radius. -/
theorem contact_ray_squared_gap (p lam x : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    gk p lam ^ 2 * (x ^ 2 - 2 * cs p * x + 1) -
        (x ^ 2 - 2 * lam * cs p * x + lam ^ 2) =
      (gk p lam ^ 2 - 1) * (x - rContact p lam) ^ 2 := by
  obtain ⟨hrr, hCC⟩ := contact_gk_radius p lam hp hp2 hlam
  obtain ⟨hr, _, _, _⟩ := contact_root_properties hp hp2 hlam
  have hrden : rContact p lam ^ 2 - 1 ≠ 0 := by
    nlinarith only [hr, sq_nonneg (rContact p lam - 1)]
  have hC1 : 1 < gk p lam := by
    exact lt_of_le_of_lt (le_max_left _ _)
      (gk_gt_max hp (ne_of_lt hp2) (ρ := (lam : ℂ)) (by
        intro hh
        have hh' : lam = 1 := by exact_mod_cast hh
        linarith [hlam.2]))
  have hCden : gk p lam ^ 2 - 1 ≠ 0 := by
    nlinarith only [hC1, sq_nonneg (gk p lam - 1)]
  have hlin : cs p * (gk p lam ^ 2 - lam) =
      (gk p lam ^ 2 - 1) * rContact p lam := by
    field_simp [hCden] at hrr
    nlinarith only [hrr]
  have hconst : gk p lam ^ 2 - lam ^ 2 =
      (gk p lam ^ 2 - 1) * rContact p lam ^ 2 := by
    field_simp [hrden] at hCC
    nlinarith only [hCC]
  linear_combination -2 * x * hlin + hconst

end GKSharp

#print axioms GKSharp.contact_gk_radius
#print axioms GKSharp.contact_ray_squared_gap
