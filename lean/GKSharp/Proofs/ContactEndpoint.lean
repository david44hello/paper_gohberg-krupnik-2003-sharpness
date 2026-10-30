/- GKSharp/Proofs/ContactEndpoint.lean — the endpoint contact at lambda=-1.
Frozen source: short_v2.30/sec4a_criterion.tex:28 (support at λ = −1 for the row obstacle_smooth_contact, which
covers the printed derivative m'_GK(θ₀) = −Kq; the paper takes that derivative from Section 2.4).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactMinimum
import GKSharp.Proofs.ContactEnvelope
import GKSharp.Proofs.ContactK

namespace GKSharp
open Threshold ContactCalc Set Filter
open scoped Topology ContDiff

namespace ContactSmooth

/-- Endpoint contact data avoid the false interior inequality rContact>1 at lambda=-1. -/
lemma endpoint_contact_data (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    gammaGK p (-1) 0 (theta p) = 0 ∧
      dy (gammaGK p (-1)) 0 (theta p) = 0 ∧
      0 < dyy (gammaGK p (-1)) 0 (theta p) ∧
      (∀ y : ℝ, y ≠ 0 → gammaGK p (-1) 0 (theta p) < gammaGK p (-1) y (theta p)) := by
  let C := gk p (-1 : ℝ)
  let a := 2 * Real.cos (theta p)
  let A : ℝ → ℝ := fun y => 2 * Real.cosh y + a
  let B : ℝ → ℝ := fun y => 2 * Real.cosh y - a
  have hp0 : 0 < p := by linarith
  have hq : 0 < p / 2 := by linarith
  have ht0 : 0 < theta p := div_pos Real.pi_pos hp0
  have htpi : theta p < Real.pi := div_lt_self Real.pi_pos hp
  have hc0 : Real.cos (theta p) < 0 := cos_theta_negative hp hp2
  have hc1 : -1 < Real.cos (theta p) := by
    simpa only [Real.cos_pi] using Real.strictAntiOn_cos
      ⟨ht0.le, htpi.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ htpi
  have hA (y : ℝ) : 0 < A y := by dsimp [A, a]; linarith [Real.one_le_cosh y]
  have hB (y : ℝ) : 0 < B y := by dsimp [B, a]; linarith [Real.one_le_cosh y]
  have hC : 1 < C := lt_of_le_of_lt (le_max_left _ _)
    (gk_gt_max hp (ne_of_lt hp2) (ρ := ((-1 : ℝ) : ℂ)) (by norm_num))
  have hCp : C ^ p = (C ^ 2) ^ (p / 2) := by
    rw [← Real.rpow_natCast C 2, ← Real.rpow_mul (by linarith : 0 ≤ C)]
    congr 1
    ring
  have hslice (y : ℝ) : gammaGK p (-1) y (theta p) = C ^ p * A y ^ (p / 2) - B y ^ (p / 2) := by
    rw [sec4b_gammaGK_eq]
    dsimp [C, A, B, a]
    norm_num only [neg_one_sq, one_mul, neg_one_mul]
    congr 1
    congr 1
    rw [Real.cosh_eq]
    ring
  have hzero : gammaGK p (-1) 0 (theta p) = 0 := sec4a_gamma_endpoint hp hp2 rfl
  have hbase : C ^ 2 * A 0 = B 0 := by
    have hz := hzero
    rw [hslice, hCp, ← Real.mul_rpow (sq_nonneg C) (hA 0).le] at hz
    exact (Real.rpow_left_inj (mul_nonneg (sq_nonneg C) (hA 0).le) (hB 0).le hq.ne').mp
      (sub_eq_zero.mp hz)
  have hAd (y : ℝ) : HasDerivAt A (2 * Real.sinh y) y :=
    ((Real.hasDerivAt_cosh y).const_mul 2).add_const a
  have hBd (y : ℝ) : HasDerivAt B (2 * Real.sinh y) y :=
    ((Real.hasDerivAt_cosh y).const_mul 2).sub_const a
  let D : ℝ → ℝ := fun y => C ^ p * (2 * Real.sinh y * (p / 2) * A y ^ (p / 2 - 1)) -
    2 * Real.sinh y * (p / 2) * B y ^ (p / 2 - 1)
  have hD (y : ℝ) : HasDerivAt (fun y => gammaGK p (-1) y (theta p)) (D y) y := by
    have hh := (((hAd y).rpow_const (p := p / 2) (Or.inl (hA y).ne')).const_mul (C ^ p)).sub
      ((hBd y).rpow_const (p := p / 2) (Or.inl (hB y).ne'))
    exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall hslice)
  have hdy (y : ℝ) : dy (gammaGK p (-1)) y (theta p) = D y := (hD y).deriv
  have hstationary : dy (gammaGK p (-1)) 0 (theta p) = 0 := by
    rw [hdy]
    simp [D]
  have hD2 : HasDerivAt D (p * (C ^ p * A 0 ^ (p / 2 - 1) - B 0 ^ (p / 2 - 1))) 0 := by
    have hh := (((((Real.hasDerivAt_sinh 0).const_mul 2).mul_const (p / 2)).mul
      ((hAd 0).rpow_const (p := p / 2 - 1) (Or.inl (hA 0).ne'))).const_mul (C ^ p)).sub
      ((((Real.hasDerivAt_sinh 0).const_mul 2).mul_const (p / 2)).mul
        ((hBd 0).rpow_const (p := p / 2 - 1) (Or.inl (hB 0).ne')))
    convert hh using 1 <;> simp only [Real.cosh_zero, Real.sinh_zero, mul_zero, zero_mul, add_zero, zero_add] <;> ring
  have hpower : C ^ p * A 0 ^ (p / 2 - 1) = C ^ 2 * B 0 ^ (p / 2 - 1) := by
    rw [← hbase, Real.mul_rpow (sq_nonneg C) (hA 0).le, hCp]
    have hh : (C ^ 2) ^ (p / 2 - 1) * C ^ 2 = (C ^ 2) ^ (p / 2) := by
      rw [← Real.rpow_add_one (by positivity : C ^ 2 ≠ 0)]
      congr 1
      ring
    rw [← hh]
    ring
  have hyy : 0 < dyy (gammaGK p (-1)) 0 (theta p) := by
    change 0 < deriv (fun y => dy (gammaGK p (-1)) y (theta p)) 0
    rw [show (fun y => dy (gammaGK p (-1)) y (theta p)) = D from funext hdy, hD2.deriv, hpower]
    have hpos := Real.rpow_pos_of_pos (hB 0) (p / 2 - 1)
    have hsq : 0 < C ^ 2 - 1 := by nlinarith [sq_nonneg (C - 1)]
    have hh := mul_pos hp0 (mul_pos hsq hpos)
    convert hh using 1 <;> ring
  refine ⟨hzero, hstationary, hyy, ?_⟩
  intro y hy
  rw [hzero, hslice, hCp, ← Real.mul_rpow (sq_nonneg C) (hA y).le]
  apply sub_pos.mpr
  apply Real.rpow_lt_rpow (hB y).le _ hq
  have hcosh : 1 < Real.cosh y := Real.one_lt_cosh.mpr hy
  have hsq : 0 < C ^ 2 - 1 := by nlinarith [sq_nonneg (C - 1)]
  have hdiff : C ^ 2 * A y - B y = (C ^ 2 - 1) * (2 * Real.cosh y - 2) := by
    dsimp [A, B] at *
    rw [Real.cosh_zero] at hbase
    nlinarith [hbase]
  have hh := mul_pos hsq (show 0 < 2 * Real.cosh y - 2 by linarith)
  linarith

end ContactSmooth
end GKSharp

#print axioms GKSharp.ContactSmooth.endpoint_contact_data
