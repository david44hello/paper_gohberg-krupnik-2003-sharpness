/-
GKSharp/Proofs/StripInvolution.lean — Lemma J of paper 019 (sec5f_strip.tex l. 24-33): the involution
`δ ↦ -δ/(1-δ)`, `s ↦ s(1-δ)/(1-sδ)` of the rescaled gap `g`, with the exact type of the draft row `involution`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.StripLeaves

namespace GKSharp.Strip

open Set GKSharp.Threshold

lemma sn_lt_one {p : ℝ} (hp : 1 < p) (hp2 : p < 2) : sn p < 1 := by
  have hsn := sn_pos hp
  have hlo : Real.pi / 2 < Real.pi / p := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
    nlinarith [Real.pi_pos]
  have hhi : Real.pi / p < Real.pi + Real.pi / 2 := by
    have : Real.pi / p < Real.pi := div_lt_self Real.pi_pos hp
    linarith [Real.pi_pos]
  have hcos : Real.cos (Real.pi / p) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hlo hhi
  have hsq : sn p ^ 2 + Real.cos (Real.pi / p) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  nlinarith

/-- `C = cDelta p d` is a positive root of `sn·C² - d·C - sn·(1-d) = 0` for `d < 1`. -/
lemma cDelta_props {p d : ℝ} (hp : 1 < p) (hd : d < 1) :
    0 < cDelta p d ∧ sn p * cDelta p d ^ 2 - d * cDelta p d - sn p * (1 - d) = 0 := by
  have hsn := sn_pos hp
  have hrad : 0 < d ^ 2 / (4 * sn p ^ 2) + 1 - d := by
    have : 0 ≤ d ^ 2 / (4 * sn p ^ 2) := by positivity
    linarith
  set R := Real.sqrt (d ^ 2 / (4 * sn p ^ 2) + 1 - d) with hR
  set b := d / (2 * sn p) with hb
  have hr2 : R ^ 2 = b ^ 2 + 1 - d := by
    rw [hR, Real.sq_sqrt hrad.le, hb]
    field_simp
    ring
  have hR0 : 0 < R := Real.sqrt_pos.2 hrad
  have hd' : d = 2 * b * sn p := by
    rw [hb]
    field_simp
  have hc : cDelta p d = b + R := rfl
  rw [hc]
  refine ⟨?_, by linear_combination (sn p) * hr2 - (b + R) * hd'⟩
  by_contra hneg
  have h1 : R ≤ -b := by linarith [not_lt.1 hneg]
  nlinarith [h1, hr2, hR0]

/-- The positive root is unique. -/
lemma cDelta_unique {p d y : ℝ} (hp : 1 < p) (hd : d < 1) (hy : 0 < y)
    (hq : sn p * y ^ 2 - d * y - sn p * (1 - d) = 0) : y = cDelta p d := by
  obtain ⟨hC0, hC⟩ := cDelta_props hp hd
  have hsn := sn_pos hp
  have h1 : (y - cDelta p d) * (sn p * (y + cDelta p d) - d) = 0 := by
    linear_combination hq - hC
  rcases mul_eq_zero.1 h1 with h | h
  · linarith
  · have hprod : sn p * (cDelta p d * y) + sn p * (1 - d) = 0 := by
      linear_combination -hC + (cDelta p d) * h
    linarith [mul_pos hsn (mul_pos hC0 hy), mul_pos hsn (sub_pos.2 hd)]

/-- The numerator of `g`: `T₁ + s·φ(sd) = (C^p - (1-sd)^p)/d` for `d ≠ 0`. -/
lemma num_form {p d s : ℝ} (hp : 1 < p) (hp2 : p < 2) (hd : d < 1) (hd0 : d ≠ 0) (hs0 : 0 < s) :
    tOne p d + s * phi p (s * d) = (cDelta p d ^ p - (1 - s * d) ^ p) / d := by
  obtain ⟨hC0, hC⟩ := cDelta_props hp hd
  have hsn := sn_pos hp
  have hsn1 := sn_lt_one hp hp2
  have hC1 : cDelta p d ≠ 1 := by
    intro h
    rw [h] at hC
    have : d * (sn p - 1) = 0 := by linear_combination hC
    rcases mul_eq_zero.1 this with h' | h'
    · exact hd0 h'
    · linarith
  have hsd : s * d ≠ 0 := mul_ne_zero hs0.ne' hd0
  have hρ1 : 1 - s * d ≠ 1 := fun h => hsd (by linarith)
  have e1 : cDelta p d - sn p = sn p * (cDelta p d ^ 2 - 1) / d := by
    field_simp
    linear_combination -hC
  have hC1' : cDelta p d - 1 ≠ 0 := sub_ne_zero.2 hC1
  have hCp1 : cDelta p d + 1 ≠ 0 := by linarith
  have hρm : 1 - s * d - 1 ≠ 0 := by
    intro h
    exact hsd (by linarith)
  unfold tOne phi
  simp only [powSlope, hC1, hρ1, ↓reduceIte]
  rw [e1]
  field_simp
  ring


lemma sEta_of_ne {eta sigma : ℝ} (he : eta ≠ 0) (hs : sigma ≠ 0) :
    sEta eta sigma = (1 - Real.exp (-(sigma * eta))) / (1 - Real.exp (-eta)) := by
  have hse : sigma * eta ≠ 0 := mul_ne_zero hs he
  rw [sEta, exprel_of_ne hse, exprel_of_ne he]
  have hA := one_sub_exp_neg_ne he
  field_simp

lemma sEta_mem {eta sigma : ℝ} (he : eta ≠ 0) (hs : sigma ∈ Ioo (0 : ℝ) 1) : sEta eta sigma ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨hs0, hs1⟩ := hs
  rw [sEta_of_ne he hs0.ne']
  rcases lt_or_gt_of_ne he with h | h
  · have h1 : 1 < Real.exp (-(sigma * eta)) := Real.one_lt_exp_iff.2 (by nlinarith)
    have h2 : Real.exp (-(sigma * eta)) < Real.exp (-eta) := Real.exp_lt_exp.2 (by nlinarith)
    exact ⟨div_pos_of_neg_of_neg (by linarith) (by linarith), (div_lt_one_of_neg (by linarith)).2 (by linarith)⟩
  · have h1 : Real.exp (-(sigma * eta)) < 1 := by
      simpa using Real.exp_lt_exp.2 (show -(sigma * eta) < 0 by nlinarith)
    have h2 : Real.exp (-eta) < Real.exp (-(sigma * eta)) := Real.exp_lt_exp.2 (by nlinarith)
    exact ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

/-- The derivative of an even function is odd (no differentiability needed). -/
lemma deriv_odd_of_even {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (x : ℝ) : deriv f (-x) = -deriv f x := by
  have h : (fun y => f (-y)) = f := funext hf
  have key := deriv_comp_neg (f := f) (x := x)
  rw [h] at key
  linarith

/-- The derivative of an odd function is even (no differentiability needed). -/
lemma deriv_even_of_odd {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) (x : ℝ) : deriv f (-x) = deriv f x := by
  have h : (fun y => f (-y)) = -f := funext hf
  have key := deriv_comp_neg (f := f) (x := x)
  rw [h, deriv.neg] at key
  linarith

end GKSharp.Strip

namespace GKSharp

open Set GKSharp.Threshold GKSharp.Strip

theorem involution_proved (p delta s : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hd : delta < 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    cDelta p delta * cDelta p (-delta / (1 - delta)) = 1 ∧
    g p delta s =
      (1 - delta) ^ (q p - 1) * cDelta p delta ^ p *
        g p (-delta / (1 - delta)) (s * (1 - delta) / (1 - s * delta)) := by
  obtain ⟨hs0, hs1⟩ := hs
  have hsn := sn_pos hp
  obtain ⟨hC0, hC⟩ := cDelta_props hp hd
  have hl0 : 0 < 1 - delta := by linarith
  set C := cDelta p delta with hCdef
  set dp := -delta / (1 - delta) with hdp
  have hdp1 : dp < 1 := by
    rw [hdp, div_lt_one hl0]
    linarith
  -- part 1: C(δ') = 1/C(δ)
  have hCp : cDelta p dp = C⁻¹ := by
    refine (cDelta_unique hp hdp1 (inv_pos.2 hC0) ?_).symm
    have e : sn p * C⁻¹ ^ 2 - dp * C⁻¹ - sn p * (1 - dp) =
        -(sn p * C ^ 2 - delta * C - sn p * (1 - delta)) / (C ^ 2 * (1 - delta)) := by
      rw [hdp]
      field_simp
      ring
    rw [e, hC, neg_zero, zero_div]
  refine ⟨by rw [hCp, mul_inv_cancel₀ hC0.ne'], ?_⟩
  -- part 2
  by_cases hd0 : delta = 0
  · have hdp0 : dp = 0 := by rw [hdp, hd0]; simp
    have hC1 : C = 1 := by rw [hCdef, hd0, cDelta_zero]
    rw [hdp0, hC1, hd0]
    simp
  set sp := s * (1 - delta) / (1 - s * delta) with hsp
  have hρ0 : 0 < 1 - s * delta := by nlinarith [mul_pos hs0 hl0]
  have hdp0 : dp ≠ 0 := by
    rw [hdp]
    exact div_ne_zero (neg_ne_zero.2 hd0) hl0.ne'
  have hsp0 : 0 < sp := by rw [hsp]; positivity
  have hsp1 : sp < 1 := by
    rw [hsp, div_lt_one hρ0]
    nlinarith
  have hnum := num_form hp hp2 hd hd0 hs0
  have hnum' := num_form hp hp2 hdp1 hdp0 hsp0
  have hρ' : 1 - sp * dp = (1 - s * delta)⁻¹ := by
    rw [hsp, hdp]
    field_simp
    ring
  have hss' : sp * (1 - sp) = (1 - delta) * (s * (1 - s)) / (1 - s * delta) ^ 2 := by
    rw [hsp]
    field_simp
    ring
  have hden : 0 < s * (1 - s) := mul_pos hs0 (by linarith)
  -- rpow facts
  have hqp : 2 * q p = p := by unfold q; ring
  have hCpow : (C ^ 2) ^ (q p - 1) * C ^ 2 = C ^ p := by
    have h1 : (C ^ 2) ^ (q p) = C ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hC0.le]
      congr 1
    rw [← h1, Real.rpow_sub_one (by positivity)]
    field_simp
  have hρpow : ((1 - s * delta) ^ 2) ^ (q p) = (1 - s * delta) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
    congr 1
  have hlpow : (1 - delta) ^ (q p) = (1 - delta) ^ (q p - 1) * (1 - delta) := by
    rw [Real.rpow_sub_one hl0.ne']
    field_simp
  have hmid : C⁻¹ ^ 2 + 1 - dp = (C ^ 2 + 1 - delta) / (C ^ 2 * (1 - delta)) := by
    rw [hdp]
    field_simp
    ring
  have hbase : 0 < C ^ 2 + 1 - delta := by nlinarith [sq_nonneg C]
  have r1 : ((1 - delta) * (s * (1 - s)) / (1 - s * delta) ^ 2) ^ q p =
      (1 - delta) ^ (q p - 1) * (1 - delta) * (s * (1 - s)) ^ q p / (1 - s * delta) ^ p := by
    rw [Real.div_rpow (mul_pos hl0 hden).le (by positivity), Real.mul_rpow hl0.le hden.le, hρpow, hlpow]
  have r2 : ((C ^ 2 + 1 - delta) / (C ^ 2 * (1 - delta))) ^ (q p - 1) =
      (C ^ 2 + 1 - delta) ^ (q p - 1) / ((C ^ 2) ^ (q p - 1) * (1 - delta) ^ (q p - 1)) := by
    rw [Real.div_rpow hbase.le (mul_pos (by positivity) hl0).le, Real.mul_rpow (sq_nonneg C) hl0.le]
  rw [← hCdef] at hnum
  unfold g
  rw [hnum, hnum', hρ', hss', hCp]
  unfold kap
  rw [← hCdef, hCp, hmid, r1, r2, Real.inv_rpow hC0.le, Real.inv_rpow hρ0.le, ← hCpow]
  have hA : 0 < (C ^ 2) ^ (q p - 1) := Real.rpow_pos_of_pos (by positivity) _
  have hB : 0 < (1 - delta) ^ (q p - 1) := Real.rpow_pos_of_pos hl0 _
  have hS : 0 < (s * (1 - s)) ^ (q p) := Real.rpow_pos_of_pos hden _
  have hR : 0 < (1 - s * delta) ^ p := Real.rpow_pos_of_pos hρ0 _
  have hM : 0 < (C ^ 2 + 1 - delta) ^ (q p - 1) := Real.rpow_pos_of_pos hbase _
  rw [hdp]
  field_simp
  ring


theorem etilde_even_proved (p sigma : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hs : sigma ∈ Ioo (0 : ℝ) 1) : Function.Even (fun eta => etilde p eta sigma) := by
  intro eta
  show etilde p (-eta) sigma = etilde p eta sigma
  by_cases he : eta = 0
  · rw [he, neg_zero]
  have hs0 := hs.1
  have hdl : deltaEta eta < 1 := by
    rw [deltaEta]
    linarith [Real.exp_pos (-eta)]
  have hsm := sEta_mem he hs
  obtain ⟨hinv1, hinv2⟩ := involution_proved p (deltaEta eta) (sEta eta sigma) hp hp2 hdl hsm
  obtain ⟨hC0, -⟩ := cDelta_props hp hdl
  have hX : Real.exp eta ≠ 0 := (Real.exp_pos _).ne'
  have hY : Real.exp (sigma * eta) ≠ 0 := (Real.exp_pos _).ne'
  have hX1 : Real.exp eta ≠ 1 := fun h => he (Real.exp_eq_one_iff _ |>.1 h)
  have hY1 : Real.exp (sigma * eta) ≠ 1 := fun h => (mul_ne_zero hs0.ne' he) (Real.exp_eq_one_iff _ |>.1 h)
  have hdp : -deltaEta eta / (1 - deltaEta eta) = deltaEta (-eta) := by
    rw [deltaEta, deltaEta, neg_neg, Real.exp_neg]
    field_simp
    ring
  have hsp : sEta eta sigma * (1 - deltaEta eta) / (1 - sEta eta sigma * deltaEta eta) = sEta (-eta) sigma := by
    rw [sEta_of_ne he hs0.ne', sEta_of_ne (neg_ne_zero.2 he) hs0.ne', deltaEta, mul_neg, neg_neg,
      Real.exp_neg, Real.exp_neg, neg_neg]
    have h1 : 1 - (Real.exp eta)⁻¹ ≠ 0 := by
      intro h
      apply hX1
      field_simp at h
      linarith
    have h2 : 1 - Real.exp (sigma * eta) ≠ 0 := sub_ne_zero.2 (Ne.symm hY1)
    have h3 : 1 - Real.exp eta ≠ 0 := sub_ne_zero.2 (Ne.symm hX1)
    have h4 : Real.exp (sigma * eta) - 1 ≠ 0 := sub_ne_zero.2 hY1
    field_simp
    ring
  rw [hdp, hsp] at hinv2
  have hCp : cDelta p (deltaEta (-eta)) = (cDelta p (deltaEta eta))⁻¹ := by
    rw [← hdp]
    exact eq_inv_of_mul_eq_one_right hinv1
  -- `etilde = g / vWeight`
  unfold etilde vWeight
  rw [hCp, hinv2]
  have hl : 1 - deltaEta eta = Real.exp (-eta) := by rw [deltaEta]; ring
  rw [hl, ← Real.exp_mul, Real.inv_rpow hC0.le]
  have hH : cDelta p (deltaEta eta) ^ p = cDelta p (deltaEta eta) ^ (p / 2) * cDelta p (deltaEta eta) ^ (p / 2) := by
    rw [← Real.rpow_add hC0]
    ring_nf
  have hE : Real.exp (-eta * (q p - 1)) = Real.exp ((1 - q p) * eta / 2) * Real.exp ((1 - q p) * eta / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have hE' : Real.exp ((1 - q p) * -eta / 2) = (Real.exp ((1 - q p) * eta / 2))⁻¹ := by
    rw [← Real.exp_neg]
    ring_nf
  rw [hH, hE, hE']
  have hP : 0 < cDelta p (deltaEta eta) ^ (p / 2) := Real.rpow_pos_of_pos hC0 _
  have hQ : 0 < Real.exp ((1 - q p) * eta / 2) := Real.exp_pos _
  field_simp

theorem etilde_odd_derivatives_proved (p sigma : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hs : sigma ∈ Ioo (0 : ℝ) 1) :
    deriv (fun eta => etilde p eta sigma) 0 = 0 ∧
    deriv (deriv (deriv (fun eta => etilde p eta sigma))) 0 = 0 := by
  have hev : ∀ x, (fun eta => etilde p eta sigma) (-x) = (fun eta => etilde p eta sigma) x :=
    etilde_even_proved p sigma hp hp2 hs
  have h1 := deriv_odd_of_even (f := fun eta => etilde p eta sigma) hev
  have h2 : ∀ x, deriv (deriv (fun eta => etilde p eta sigma)) (-x) =
      deriv (deriv (fun eta => etilde p eta sigma)) x := deriv_even_of_odd h1
  have h3 := deriv_odd_of_even h2
  constructor
  · have := h1 0
    rw [neg_zero] at this
    linarith
  · have := h3 0
    rw [neg_zero] at this
    linarith

end GKSharp
