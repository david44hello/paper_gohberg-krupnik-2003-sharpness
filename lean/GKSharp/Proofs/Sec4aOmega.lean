/- GKSharp/Proofs/Sec4aOmega.lean - slice (b): the first Omega term and its minimizer (short v0.40).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Rows of PROPOSAL_CHECKS_THRESHOLDS.lean v0.80, each as `<row>_proved` with the row's exact type.
- sStar_spec (A:38, A:51-52): with `A = 2q - 1 > 0`, `B = b > 0`, `c = qa > 0`, `S = √(B² + 4Ac)`,
  `s* = 2c/(B + S)` is a root of `sQuad = As² + Bs - c`, lies in `(0, 1)` (`sQuad(1) = q + qa > 0`), and is the only
  root there (`sQuad s - sQuad s* = (s - s*)(A(s + s*) + B)`). `ω₁'(s) = p u^{q-1} sQuad(s) / u^{2q}`, `u = s(1 - s)`,
  so `ω₁` is strictly decreasing on `(0, s*]` and strictly increasing on `[s*, 1)`.
- omega_midpoint_bound (A:54): `ω₁(1/2) = p 2^{p-1}/sn`, and `s*` minimizes `ω₁`.
-/
import GKSharp.Proofs.Sec4aBasic

namespace GKSharp

open Set GKSharp.Threshold

/-- `sin(π/p) < 1` for `1 < p < 2`. -/
lemma sec4a_sn_lt_one {p : ℝ} (hp : 1 < p) (hp2 : p < 2) : sn p < 1 := by
  have hp0 : 0 < p := by linarith
  set w := Real.pi / p - Real.pi / 2 with hw
  have hw0 : 0 < w := by
    rw [hw, sub_pos]
    exact div_lt_div_of_pos_left Real.pi_pos hp0 hp2
  have hw1 : w < Real.pi / 2 := by
    have : Real.pi / p < Real.pi := div_lt_self Real.pi_pos hp
    rw [hw]
    linarith
  have hsn : sn p = Real.cos w := by
    rw [hw, Real.cos_sub_pi_div_two]
    rfl
  have hs : 0 < Real.sin w := Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos w := Real.cos_pos_of_mem_Ioo ⟨by linarith, hw1⟩
  rw [hsn]
  nlinarith [Real.sin_sq_add_cos_sq w, mul_pos hs hs]

/-- `a = (1 - sn)/(2 sn) > 0` for `1 < p < 2`. -/
lemma sec4a_aConst_pos {p : ℝ} (hp : 1 < p) (hp2 : p < 2) : 0 < aConst p := by
  have h1 := sec4a_sn_pos hp
  have h2 := sec4a_sn_lt_one hp hp2
  unfold aConst
  exact div_pos (by linarith) (by linarith)

/-- The derivative of `ω₁` on `(0, 1)` (quotient rule). -/
lemma sec4a_omegaFirst_hasDerivAt (p : ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt (omegaFirst p)
      ((p * (s * (1 - s)) ^ q p - p * (aConst p + s) * ((1 - 2 * s) * q p * (s * (1 - s)) ^ (q p - 1))) /
        ((s * (1 - s)) ^ q p) ^ 2) s := by
  have hu : 0 < s * (1 - s) := mul_pos hs0 (by linarith)
  have hf : HasDerivAt (fun x => p * (aConst p + x)) p s := by
    simpa using ((hasDerivAt_id' s).const_add (aConst p)).const_mul p
  have hin : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * s) s := by
    have := (hasDerivAt_id' s).mul ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id' s))
    convert this using 1
    simp only [Pi.sub_apply]
    ring
  have hg : HasDerivAt (fun x : ℝ => (x * (1 - x)) ^ q p) ((1 - 2 * s) * q p * (s * (1 - s)) ^ (q p - 1)) s :=
    hin.rpow_const (Or.inl hu.ne')
  exact hf.div hg (Real.rpow_pos_of_pos hu _).ne'

/-- A:38, A:51-52, row `sStar_spec`. -/
theorem sStar_spec_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    sStar p ∈ Ioo (0 : ℝ) 1 ∧ sQuad p (sStar p) = 0 ∧
    (∀ s ∈ Ioo (0 : ℝ) 1, sQuad p s = 0 → s = sStar p) ∧
    (∀ s ∈ Ioo (0 : ℝ) 1, omegaFirst p (sStar p) ≤ omegaFirst p s) ∧
    (∀ s ∈ Ioo (0 : ℝ) 1, omegaFirst p s = omegaFirst p (sStar p) → s = sStar p) := by
  have ha := sec4a_aConst_pos hp hp2
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q p := by unfold q; linarith
  have hq1 : q p < 1 := by unfold q; linarith
  have hr0 : sStar p = 2 * (q p * aConst p) /
      (bConst p + Real.sqrt (bConst p ^ 2 + 4 * (2 * q p - 1) * (q p * aConst p))) := by
    unfold sStar
    rw [mul_assoc 2 (q p) (aConst p), mul_assoc (4 * (2 * q p - 1)) (q p) (aConst p)]
  have hQ : ∀ s, sQuad p s = (2 * q p - 1) * s ^ 2 + bConst p * s - q p * aConst p := fun s => rfl
  have hBv : bConst p = 1 - q p + 2 * q p * aConst p := rfl
  set A := 2 * q p - 1 with hA
  set B := bConst p with hB
  set c := q p * aConst p with hc
  have hA0 : 0 < A := by rw [hA]; unfold q; linarith
  have hc0 : 0 < c := mul_pos hq0 ha
  have hB0 : 0 < B := by rw [hBv]; nlinarith
  have hD0 : 0 < B ^ 2 + 4 * A * c := by positivity
  set S := Real.sqrt (B ^ 2 + 4 * A * c) with hS
  have hS0 : 0 < S := Real.sqrt_pos.2 hD0
  have hSS : S ^ 2 = B ^ 2 + 4 * A * c := Real.sq_sqrt hD0.le
  have hBS : 0 < B + S := by linarith
  set r := sStar p with hr
  have hrB : r * (B + S) = 2 * c := by rw [hr0, div_mul_cancel₀ _ hBS.ne']
  -- `s*` is a root
  have hroot : A * r ^ 2 + B * r - c = 0 := by
    have h2 : (A * r ^ 2 + B * r - c) * (B + S) ^ 2 = 0 := by
      linear_combination (A * (r * (B + S) + 2 * c) + B * (B + S)) * hrB - c * hSS
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h (pow_ne_zero 2 hBS.ne')
  -- `s* ∈ (0, 1)`
  have hrpos : 0 < r := by rw [hr0]; exact div_pos (by linarith) hBS
  have hr1 : r < 1 := by
    rw [hr0, div_lt_one hBS]
    have hABc : 0 < A + B - c := by rw [hA, hBv, hc]; nlinarith
    have hS2 : 2 * c - B < S := by
      by_contra hcon
      push Not at hcon
      have h0 : 0 ≤ 2 * c - B := le_trans hS0.le hcon
      nlinarith [mul_le_mul hcon hcon hS0.le h0]
    linarith
  -- the factorization `sQuad s = (s - s*)(A(s + s*) + B)`
  have hfac : ∀ s : ℝ, A * s ^ 2 + B * s - c = (s - r) * (A * (s + r) + B) := fun s => by
    linear_combination hroot
  have hpos : ∀ s : ℝ, 0 < s → 0 < A * (s + r) + B := fun s hs => by nlinarith
  -- uniqueness
  have huniq : ∀ s ∈ Ioo (0 : ℝ) 1, sQuad p s = 0 → s = r := by
    rintro s ⟨hs0, -⟩ hs
    rw [hQ, hfac] at hs
    have := (mul_eq_zero.1 hs).resolve_right (hpos s hs0).ne'
    linarith
  -- the numerator of `ω₁'` is `p u^{q-1} sQuad(s)`
  have hN : ∀ s : ℝ, 0 < s → s < 1 →
      p * (s * (1 - s)) ^ q p - p * (aConst p + s) * ((1 - 2 * s) * q p * (s * (1 - s)) ^ (q p - 1)) =
        p * (s * (1 - s)) ^ (q p - 1) * (A * s ^ 2 + B * s - c) := by
    intro s hs0 hs1
    have hu : 0 < s * (1 - s) := mul_pos hs0 (by linarith)
    have he : (s * (1 - s)) ^ q p = (s * (1 - s)) ^ (q p - 1) * (s * (1 - s)) := by
      rw [Real.rpow_sub_one hu.ne', div_mul_cancel₀ _ hu.ne']
    rw [he]
    simp only [hA, hB, hc, bConst]
    ring
  have hderiv_sign : ∀ s : ℝ, 0 < s → s < 1 →
      deriv (omegaFirst p) s = p * (s * (1 - s)) ^ (q p - 1) * ((s - r) * (A * (s + r) + B)) /
        ((s * (1 - s)) ^ q p) ^ 2 := by
    intro s hs0 hs1
    rw [(sec4a_omegaFirst_hasDerivAt p hs0 hs1).deriv, hN s hs0 hs1, hfac]
  have hcoef : ∀ s : ℝ, 0 < s → s < 1 → 0 < p * (s * (1 - s)) ^ (q p - 1) := fun s hs0 hs1 =>
    mul_pos hp0 (Real.rpow_pos_of_pos (mul_pos hs0 (by linarith)) _)
  have hden : ∀ s : ℝ, 0 < s → s < 1 → 0 < ((s * (1 - s)) ^ q p) ^ 2 := fun s hs0 hs1 =>
    pow_pos (Real.rpow_pos_of_pos (mul_pos hs0 (by linarith)) _) 2
  -- strictly decreasing on `(0, s*]`, strictly increasing on `[s*, 1)`
  have hanti : StrictAntiOn (omegaFirst p) (Ioc 0 r) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc 0 r)
    · intro s hs
      exact (sec4a_omegaFirst_hasDerivAt p hs.1 (by linarith [hs.2])).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ioc] at hs
      obtain ⟨hs0, hs1⟩ := hs
      rw [hderiv_sign s hs0 (by linarith)]
      apply div_neg_of_neg_of_pos _ (hden s hs0 (by linarith))
      exact mul_neg_of_pos_of_neg (hcoef s hs0 (by linarith))
        (mul_neg_of_neg_of_pos (by linarith) (hpos s hs0))
  have hmono : StrictMonoOn (omegaFirst p) (Ico r 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico r 1)
    · intro s hs
      exact (sec4a_omegaFirst_hasDerivAt p (by linarith [hs.1]) hs.2).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      obtain ⟨hs0, hs1⟩ := hs
      have hs0' : 0 < s := by linarith
      rw [hderiv_sign s hs0' hs1]
      apply div_pos _ (hden s hs0' hs1)
      exact mul_pos (hcoef s hs0' hs1) (mul_pos (by linarith) (hpos s hs0'))
  have hlt : ∀ s ∈ Ioo (0 : ℝ) 1, s ≠ r → omegaFirst p r < omegaFirst p s := by
    rintro s ⟨hs0, hs1⟩ hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hanti ⟨hs0, h.le⟩ ⟨hrpos, le_rfl⟩ h
    · exact hmono ⟨le_rfl, hr1⟩ ⟨h.le, hs1⟩ h
  refine ⟨⟨hrpos, hr1⟩, by rw [hQ]; exact hroot, huniq, fun s hs => ?_, fun s hs heq => ?_⟩
  · by_cases hne : s = r
    · rw [hne]
    · exact (hlt s hs hne).le
  · by_contra hne
    exact (hlt s hs hne).ne' heq

/-- A:54, row `omega_midpoint_bound`. -/
theorem omega_midpoint_bound_proved (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    omegaFirst p (sStar p) ≤ p * 2 ^ (p - 1) / sn p := by
  have h := (sStar_spec_proved p hp hp2).2.2.2.1 (1 / 2) ⟨by norm_num, by norm_num⟩
  have hs := (sec4a_sn_pos hp).ne'
  have h2p : (2 : ℝ) ^ p ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) p).ne'
  have h4 : ((1 : ℝ) / 2 * (1 - 1 / 2)) ^ (p / 2) = ((2 : ℝ) ^ p)⁻¹ := by
    rw [show ((1 : ℝ) / 2 * (1 - 1 / 2)) = ((2 : ℝ) ^ (2 : ℝ))⁻¹ by rw [Real.rpow_two]; norm_num,
      Real.inv_rpow (by positivity), ← Real.rpow_mul (by norm_num)]
    congr 2
    ring
  have h2 : (2 : ℝ) ^ (p - 1) = 2 ^ p / 2 := Real.rpow_sub_one (by norm_num) p
  have hval : omegaFirst p (1 / 2) = p * 2 ^ (p - 1) / sn p := by
    unfold omegaFirst aConst q
    rw [h4, h2]
    field_simp
    ring
  rw [hval] at h
  exact h

end GKSharp
