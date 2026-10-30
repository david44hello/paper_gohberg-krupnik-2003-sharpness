/-
RealSegment.lean — real-segment calculus, Section 5.3.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.MobiusDict

namespace GKSharp.Proofs.RealSegment

open GKSharp Filter Topology

lemma reQPow_ofReal {x : ℝ} (hx : 0 ≤ x) (q : ℝ) : reQPow (x : ℂ) q = x ^ q := by
  simp [reQPow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
    Complex.arg_ofReal_of_nonneg hx]

lemma mobQ_ofReal (lam x : ℝ) : mobQ lam (x : ℂ) = (((x - lam) * (1 - x) : ℝ) : ℂ) := by
  simp [mobQ]

lemma real_derivative {p C K lam ρ : ℝ} (hρ : 0 < ρ) (hQ : 0 < (ρ - lam) * (1 - ρ)) :
    HasDerivAt (fun x : ℝ => mobPhi p C K lam (x : ℂ))
      (-(1 - lam) ^ p * p * ρ ^ (p - 1) -
        K * (p / 2) * ((ρ - lam) * (1 - ρ)) ^ (p / 2 - 1) * (1 + lam - 2 * ρ)) ρ := by
  have dq : HasDerivAt (fun x : ℝ => (x - lam) * (1 - x)) (1 + lam - 2 * ρ) ρ := by
    convert ((hasDerivAt_id ρ).sub_const lam).mul ((hasDerivAt_const ρ 1).sub (hasDerivAt_id ρ)) using 1
    · funext x <;> dsimp <;> ring
    · dsimp <;> ring
  have dp := (Real.hasDerivAt_rpow_const (p := p) (Or.inl (ne_of_gt hρ)))
  have derivative := ((hasDerivAt_const ρ (C ^ p)).sub dp).const_mul ((1 - lam) ^ p)
  have derivative := derivative.sub ((dq.rpow_const (p := p / 2) (Or.inl (ne_of_gt hQ))).const_mul K)
  have local_eq : (fun x : ℝ => mobPhi p C K lam (x : ℂ)) =ᶠ[𝓝 ρ]
      (fun x : ℝ => (1 - lam) ^ p * (C ^ p - x ^ p) - K * ((x - lam) * (1 - x)) ^ (p / 2)) := by
    have positiveQ : ∀ᶠ x : ℝ in 𝓝 ρ, 0 < (x - lam) * (1 - x) :=
      (dq.continuousAt.eventually (eventually_gt_nhds hQ))
    filter_upwards [eventually_gt_nhds hρ, positiveQ] with x hx hqx
    rw [mobPhi, mobQ_ofReal, reQPow_ofReal hqx.le]
    simp [Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx]
  exact (derivative.congr_deriv (by ring)).congr_of_eventuallyEq local_eq

lemma real_factorization {p K lam ρ : ℝ} (hQ : 0 < (ρ - lam) * (1 - ρ))
    (hd : 2 * ρ - 1 - lam ≠ 0) :
    -(1 - lam) ^ p * p * ρ ^ (p - 1) -
      K * (p / 2) * ((ρ - lam) * (1 - ρ)) ^ (p / 2 - 1) * (1 + lam - 2 * ρ) =
    p / 2 * ((ρ - lam) * (1 - ρ)) ^ (p / 2 - 1) * (2 * ρ - 1 - lam) *
      (K - 2 * (1 - lam) ^ p * ρ ^ (p - 1) * ((ρ - lam) * (1 - ρ)) ^ (1 - p / 2) /
        (2 * ρ - 1 - lam)) := by
  rw [show 1 - p / 2 = -(p / 2 - 1) by ring, Real.rpow_neg hQ.le]
  have nonzero := ne_of_gt (Real.rpow_pos_of_pos hQ (p / 2 - 1))
  field_simp
  <;> ring

lemma log_derivative {p lam ρ : ℝ} (hl1 : lam < 1) (hρ : 0 < ρ)
    (hQ : 0 < (ρ - lam) * (1 - ρ)) (hd : 0 < 2 * ρ - 1 - lam) :
    HasDerivAt (fun x : ℝ => Real.log (2 * (1 - lam) ^ p * x ^ (p - 1) *
        ((x - lam) * (1 - x)) ^ (1 - p / 2) / (2 * x - 1 - lam)))
      ((p - 1) / ρ - 2 / (2 * ρ - 1 - lam) -
        (1 - p / 2) * (2 * ρ - 1 - lam) / ((ρ - lam) * (1 - ρ))) ρ := by
  have dq : HasDerivAt (fun x : ℝ => (x - lam) * (1 - x)) (1 + lam - 2 * ρ) ρ := by
    convert ((hasDerivAt_id ρ).sub_const lam).mul ((hasDerivAt_const ρ 1).sub (hasDerivAt_id ρ)) using 1
    · funext x <;> dsimp <;> ring
    · dsimp <;> ring
  have dd : HasDerivAt (fun x : ℝ => 2 * x - 1 - lam) 2 ρ := by
    convert (((hasDerivAt_id ρ).const_mul 2).sub_const 1).sub_const lam using 1
    · funext x <;> dsimp <;> ring
    · ring
  have dnum := ((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl (ne_of_gt hρ))).const_mul
    (2 * (1 - lam) ^ p)).mul (dq.rpow_const (p := 1 - p / 2) (Or.inl (ne_of_gt hQ)))
  have ha := Real.rpow_pos_of_pos (sub_pos.mpr hl1) p
  have hb := Real.rpow_pos_of_pos hρ (p - 1)
  have hc := Real.rpow_pos_of_pos hQ (1 - p / 2)
  have positive : 0 < 2 * (1 - lam) ^ p * ρ ^ (p - 1) *
      ((ρ - lam) * (1 - ρ)) ^ (1 - p / 2) / (2 * ρ - 1 - lam) := by positivity
  have derivative := (dnum.div dd (ne_of_gt hd)).log (ne_of_gt positive)
  convert derivative using 1
  dsimp
  rw [Real.rpow_sub_one (ne_of_gt hρ), Real.rpow_sub_one (ne_of_gt hQ)]
  rw [show 1 + lam - 2 * ρ = -(2 * ρ - 1 - lam) by ring]
  generalize (1 - lam) ^ p = aa at *
  generalize ρ ^ (p - 1) = bb at *
  generalize (ρ - lam) * (1 - ρ) = qq at *
  generalize 2 * ρ - 1 - lam = dd at *
  generalize qq ^ (1 - p / 2) = cc at *
  field_simp [ne_of_gt hρ, ne_of_gt hQ, ne_of_gt hd, ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
  <;> ring

lemma log_derivative_negative {p lam ρ : ℝ} (hp2 : p < 2) (hl : -1 ≤ lam)
    (hρ : 0 < ρ) (hQ : 0 < (ρ - lam) * (1 - ρ)) (hd : 0 < 2 * ρ - 1 - lam) :
    (p - 1) / ρ - 2 / (2 * ρ - 1 - lam) -
      (1 - p / 2) * (2 * ρ - 1 - lam) / ((ρ - lam) * (1 - ρ)) < 0 := by
  have first : (p - 1) / ρ < 1 / ρ := (div_lt_div_iff_of_pos_right hρ).mpr (by linarith)
  have second : 1 / ρ ≤ 2 / (2 * ρ - 1 - lam) := by
    apply (div_le_div_iff₀ hρ hd).mpr
    linarith
  have last : 0 < (1 - p / 2) * (2 * ρ - 1 - lam) / ((ρ - lam) * (1 - ρ)) :=
    div_pos (mul_pos (by linarith) hd) hQ
  linarith

theorem reduction_real_segment_proved {p C K lam ρ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hρ0 : 0 < ρ) (hQ : 0 < (ρ - lam) * (1 - ρ)) :
    HasDerivAt (fun x : ℝ => mobPhi p C K lam (x : ℂ))
      (-(1 - lam) ^ p * p * ρ ^ (p - 1) - K * (p / 2) * ((ρ - lam) * (1 - ρ)) ^ (p / 2 - 1) * (1 + lam - 2 * ρ)) ρ ∧
    (2 * ρ - 1 - lam ≠ 0 →
      -(1 - lam) ^ p * p * ρ ^ (p - 1) - K * (p / 2) * ((ρ - lam) * (1 - ρ)) ^ (p / 2 - 1) * (1 + lam - 2 * ρ) =
        p / 2 * ((ρ - lam) * (1 - ρ)) ^ (p / 2 - 1) * (2 * ρ - 1 - lam) *
          (K - 2 * (1 - lam) ^ p * ρ ^ (p - 1) * ((ρ - lam) * (1 - ρ)) ^ (1 - p / 2) / (2 * ρ - 1 - lam))) ∧
    ((1 + lam) / 2 < ρ → ρ < 1 →
      HasDerivAt (fun x => Real.log (2 * (1 - lam) ^ p * x ^ (p - 1) * ((x - lam) * (1 - x)) ^ (1 - p / 2) /
          (2 * x - 1 - lam)))
        ((p - 1) / ρ - 2 / (2 * ρ - 1 - lam) - (1 - p / 2) * (2 * ρ - 1 - lam) / ((ρ - lam) * (1 - ρ))) ρ ∧
      (p - 1) / ρ - 2 / (2 * ρ - 1 - lam) - (1 - p / 2) * (2 * ρ - 1 - lam) / ((ρ - lam) * (1 - ρ)) < 0) := by
  refine ⟨real_derivative hρ0 hQ, real_factorization hQ, ?_⟩
  intro hmid _
  have hd : 0 < 2 * ρ - 1 - lam := by linarith
  exact ⟨log_derivative hl1 hρ0 hQ hd, log_derivative_negative hp2 hl hρ0 hQ hd⟩

end GKSharp.Proofs.RealSegment

#print axioms GKSharp.Proofs.RealSegment.reduction_real_segment_proved
