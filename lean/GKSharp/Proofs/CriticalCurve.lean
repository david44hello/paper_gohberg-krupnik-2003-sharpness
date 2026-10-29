/- GKSharp/Proofs/CriticalCurve.lean - the critical-point function D(theta, r) of Section 5: its unique root R(theta) in
(0, 1), the root formula, the product of the zeros, the limits at 0 and pi, and analyticity
(sec5_sharp_inequality.tex l.45-53).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.CriticalCurve

namespace GKSharp

open Filter Topology

section Root

variable {lam a b : ℝ}

theorem curveRoot_disc (ha : 0 < a) (hab : a ≤ b) :
    (1 - lam) ^ 2 * a ^ 2 ≤ (1 + lam) ^ 2 * b ^ 2 - 4 * lam * a ^ 2 := by
  have h : 0 ≤ (1 + lam) ^ 2 * (b ^ 2 - a ^ 2) := mul_nonneg (sq_nonneg _) (by nlinarith)
  nlinarith

theorem curveRoot_den_pos (hl : -1 ≤ lam) (hl1 : lam < 1) (ha : 0 < a) (hab : a ≤ b) :
    0 < (1 + lam) * b + Real.sqrt ((1 + lam) ^ 2 * b ^ 2 - 4 * lam * a ^ 2) := by
  have hd := curveRoot_disc (lam := lam) ha hab
  have hpos : 0 < (1 - lam) ^ 2 * a ^ 2 := by
    have : 0 < 1 - lam := by linarith
    positivity
  have h1 : 0 < Real.sqrt ((1 + lam) ^ 2 * b ^ 2 - 4 * lam * a ^ 2) := Real.sqrt_pos.2 (by linarith)
  have h2 : 0 ≤ (1 + lam) * b := mul_nonneg (by linarith) (by linarith)
  linarith

theorem curveRoot_pos (hl : -1 ≤ lam) (hl1 : lam < 1) (ha : 0 < a) (hab : a ≤ b) : 0 < curveRoot lam a b :=
  div_pos (by linarith) (curveRoot_den_pos hl hl1 ha hab)

theorem curveRoot_isRoot (hl : -1 ≤ lam) (hl1 : lam < 1) (ha : 0 < a) (hab : a ≤ b) :
    (1 + lam) * curveRoot lam a b * b - (1 + lam * curveRoot lam a b ^ 2) * a = 0 := by
  have hd := curveRoot_disc (lam := lam) ha hab
  have hden := curveRoot_den_pos hl hl1 ha hab
  have hS : Real.sqrt ((1 + lam) ^ 2 * b ^ 2 - 4 * lam * a ^ 2) ^ 2 =
      (1 + lam) ^ 2 * b ^ 2 - 4 * lam * a ^ 2 := Real.sq_sqrt (by nlinarith)
  have key : ∀ S : ℝ, S ^ 2 = (1 + lam) ^ 2 * b ^ 2 - 4 * lam * a ^ 2 → (1 + lam) * b + S ≠ 0 →
      (1 + lam) * (2 * a / ((1 + lam) * b + S)) * b - (1 + lam * (2 * a / ((1 + lam) * b + S)) ^ 2) * a = 0 := by
    intro S hS hne
    field_simp
    linear_combination (-a) * hS
  exact key _ hS hden.ne'

theorem curveRoot_lt_one (hl : -1 < lam) (hl1 : lam < 1) (ha : 0 < a) (hab : a < b) : curveRoot lam a b < 1 := by
  have hden := curveRoot_den_pos hl.le hl1 ha hab.le
  unfold curveRoot
  rw [div_lt_one hden]
  have hS : 2 * a - (1 + lam) * b < Real.sqrt ((1 + lam) ^ 2 * b ^ 2 - 4 * lam * a ^ 2) := by
    rcases lt_or_ge (2 * a - (1 + lam) * b) 0 with h | h
    · exact lt_of_lt_of_le h (Real.sqrt_nonneg _)
    · rw [Real.lt_sqrt h]
      nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < 1 + lam) ha) (by linarith : (0 : ℝ) < b - a)]
  linarith

theorem curveRoot_le_one (hl : -1 ≤ lam) (hl1 : lam < 1) (ha : 0 < a) (hab : a < b) : curveRoot lam a b ≤ 1 := by
  rcases hl.lt_or_eq with h | h
  · exact (curveRoot_lt_one h hl1 ha hab).le
  · subst h
    unfold curveRoot
    have h2 : (1 + -1 : ℝ) ^ 2 * b ^ 2 - 4 * -1 * a ^ 2 = (2 * a) ^ 2 := by ring
    rw [h2, Real.sqrt_sq (by linarith), show (1 + -1 : ℝ) * b + 2 * a = 2 * a by ring, div_self (by positivity)]

theorem curveRoot_minus_one (ha : 0 < a) (b : ℝ) : curveRoot (-1) a b = 1 := by
  unfold curveRoot
  have h2 : (1 + -1 : ℝ) ^ 2 * b ^ 2 - 4 * -1 * a ^ 2 = (2 * a) ^ 2 := by ring
  rw [h2, Real.sqrt_sq (by linarith), show (1 + -1 : ℝ) * b + 2 * a = 2 * a by ring, div_self (by positivity)]

theorem curveRoot_diag (hl1 : lam < 1) (ha : 0 < a) : curveRoot lam a a = 1 := by
  unfold curveRoot
  have h2 : (1 + lam) ^ 2 * a ^ 2 - 4 * lam * a ^ 2 = ((1 - lam) * a) ^ 2 := by ring
  have h3 : 0 ≤ (1 - lam) * a := mul_nonneg (by linarith) ha.le
  rw [h2, Real.sqrt_sq h3, show (1 + lam) * a + (1 - lam) * a = 2 * a by ring, div_self (by positivity)]

theorem curveRoot_smul {t : ℝ} (ht : 0 < t) (lam a b : ℝ) :
    curveRoot lam (t * a) (t * b) = curveRoot lam a b := by
  unfold curveRoot
  have h : (1 + lam) ^ 2 * (t * b) ^ 2 - 4 * lam * (t * a) ^ 2 =
      t ^ 2 * ((1 + lam) ^ 2 * b ^ 2 - 4 * lam * a ^ 2) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  rw [show (1 + lam) * (t * b) + t * Real.sqrt ((1 + lam) ^ 2 * b ^ 2 - 4 * lam * a ^ 2) =
      t * ((1 + lam) * b + Real.sqrt ((1 + lam) ^ 2 * b ^ 2 - 4 * lam * a ^ 2)) by ring,
    show 2 * (t * a) = t * (2 * a) by ring, mul_div_mul_left _ _ ht.ne']

end Root

section Sines

variable {p θ : ℝ}

/-- sec5_sharp_inequality.tex l.45: `0 < s₁ < s₂`, as `s₂ - s₁ = 2 cos(θ/2) sin(εθ/2)`, `ε = p - 1`. -/
theorem curve_sines (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    0 < Real.sin ((1 - p / 2) * θ) ∧ Real.sin ((1 - p / 2) * θ) < Real.sin (p / 2 * θ) ∧
      Real.sin (p / 2 * θ) - Real.sin ((1 - p / 2) * θ) = 2 * Real.cos (θ / 2) * Real.sin ((p - 1) * θ / 2) := by
  have hid : Real.sin (p / 2 * θ) - Real.sin ((1 - p / 2) * θ) =
      2 * Real.cos (θ / 2) * Real.sin ((p - 1) * θ / 2) := by
    rw [Real.sin_sub_sin]
    rw [show (p / 2 * θ - (1 - p / 2) * θ) / 2 = (p - 1) * θ / 2 by ring,
      show (p / 2 * θ + (1 - p / 2) * θ) / 2 = θ / 2 by ring]
    ring
  have hpθ : 0 < p * θ := mul_pos (by linarith) hθ0
  have h2pθ : 0 < (2 - p) * θ := mul_pos (by linarith) hθ0
  have hs1 : 0 < Real.sin ((1 - p / 2) * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith [Real.pi_pos])
  have hc : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs : 0 < Real.sin ((p - 1) * θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith [Real.pi_pos])
  refine ⟨hs1, ?_, hid⟩
  have := mul_pos (mul_pos two_pos hc) hs
  linarith

end Sines

section Curve

variable {p lam θ : ℝ}

theorem curveD_sub (p lam θ r r' : ℝ) :
    curveD p lam θ r - curveD p lam θ r' =
      (r - r') * ((1 + lam) * Real.sin (p / 2 * θ) - lam * (r + r') * Real.sin ((1 - p / 2) * θ)) := by
  unfold curveD; ring

/-- The bracket `(1 + λ) s₂ - λ (r + r') s₁` is positive for `r, r' ∈ [0, 1]`, `-1 < λ < 1`. -/
theorem curve_bracket_pos (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hl : -1 < lam) (hl1 : lam < 1) {r r' : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) (hr' : r' ∈ Set.Icc (0 : ℝ) 1) :
    0 < (1 + lam) * Real.sin (p / 2 * θ) - lam * (r + r') * Real.sin ((1 - p / 2) * θ) := by
  obtain ⟨hs1, hs12, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hr0', hr1'⟩ := hr'
  rcases le_or_gt lam 0 with h | h
  · have h1 : 0 < (1 + lam) * Real.sin (p / 2 * θ) := mul_pos (by linarith) (by linarith)
    have h2 : lam * (r + r') * Real.sin ((1 - p / 2) * θ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h (by linarith)) hs1.le
    linarith
  · have h1 : lam * (r + r') * Real.sin ((1 - p / 2) * θ) ≤ lam * 2 * Real.sin ((1 - p / 2) * θ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) h.le) hs1.le
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 + lam) (by linarith : 0 < Real.sin (p / 2 * θ) -
      Real.sin ((1 - p / 2) * θ)), mul_pos (by linarith : (0 : ℝ) < 1 - lam) hs1]

/-- sec5_sharp_inequality.tex l.46: `∂_r D = (1 + λ) s₂ - 2 λ r s₁`. -/
theorem curveD_hasDerivAt (p lam θ r : ℝ) :
    HasDerivAt (curveD p lam θ)
      ((1 + lam) * Real.sin (p / 2 * θ) - 2 * lam * r * Real.sin ((1 - p / 2) * θ)) r := by
  have h := (((hasDerivAt_id r).const_mul ((1 + lam) * Real.sin (p / 2 * θ))).sub
    ((((hasDerivAt_pow 2 r).const_mul lam).const_add 1).mul_const (Real.sin ((1 - p / 2) * θ))))
  convert h using 1
  · funext x; simp only [curveD, Pi.sub_apply, id]; ring
  · push_cast; ring

/-- sec5_sharp_inequality.tex l.45-47 (`-1 < λ < 1`): `D(θ, 0) = -s₁ < 0 < (1 + λ)(s₂ - s₁) = D(θ, 1)`, `∂_r D > 0` on
`[0, 1]`, and `D(θ, ·)` has exactly one zero `R(θ) ∈ (0, 1)` on `[0, 1]`. -/
theorem curve_root_unique (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hl : -1 < lam) (hl1 : lam < 1) :
    curveD p lam θ 0 = -Real.sin ((1 - p / 2) * θ) ∧ -Real.sin ((1 - p / 2) * θ) < 0 ∧
    0 < (1 + lam) * (Real.sin (p / 2 * θ) - Real.sin ((1 - p / 2) * θ)) ∧
    curveD p lam θ 1 = (1 + lam) * (Real.sin (p / 2 * θ) - Real.sin ((1 - p / 2) * θ)) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) 1, 0 < (1 + lam) * Real.sin (p / 2 * θ) - 2 * lam * r * Real.sin ((1 - p / 2) * θ)) ∧
    0 < curveR p lam θ ∧ curveR p lam θ < 1 ∧ curveD p lam θ (curveR p lam θ) = 0 ∧
    ∀ r ∈ Set.Icc (0 : ℝ) 1, curveD p lam θ r = 0 → r = curveR p lam θ := by
  obtain ⟨hs1, hs12, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  have hR0 : 0 < curveR p lam θ := curveRoot_pos hl.le hl1 hs1 hs12.le
  have hR1 : curveR p lam θ < 1 := curveRoot_lt_one hl hl1 hs1 hs12
  have hDR : curveD p lam θ (curveR p lam θ) = 0 := by
    have h := curveRoot_isRoot hl.le hl1 hs1 hs12.le
    unfold curveD; unfold curveR; linarith
  refine ⟨by unfold curveD; ring, by linarith, mul_pos (by linarith) (by linarith), by unfold curveD; ring,
    fun r hr => ?_, hR0, hR1, hDR, fun r hr hDr => ?_⟩
  · have h := curve_bracket_pos hp1 hp2 hθ0 hθ hl hl1 hr hr
    linarith
  · have hb := curve_bracket_pos hp1 hp2 hθ0 hθ hl hl1 hr ⟨hR0.le, hR1.le⟩
    have hsub := curveD_sub p lam θ r (curveR p lam θ)
    rw [hDr, hDR, sub_zero] at hsub
    have := (mul_eq_zero.1 hsub.symm).resolve_right hb.ne'
    linarith

/-- sec5_sharp_inequality.tex l.47-48 (`λ = -1`): `D = -(1 - r²) s₁`, and the formula gives `R = 1`. -/
theorem curve_root_minus_one (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (∀ r, curveD p (-1) θ r = -(1 - r ^ 2) * Real.sin ((1 - p / 2) * θ)) ∧ curveR p (-1) θ = 1 := by
  obtain ⟨hs1, -, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  exact ⟨fun r => by unfold curveD; ring, curveRoot_minus_one hs1 _⟩

/-- sec5_sharp_inequality.tex l.48 (`-1 ≤ λ < 1`): "In both cases R = 2s₁/((1+λ)s₂ + √((1+λ)²s₂² − 4λs₁²)), with
discriminant ≥ (1−λ)²s₁² > 0": the formula is a zero of `D(θ, ·)` in `(0, 1]`. -/
theorem curve_root_formula (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hl : -1 ≤ lam) (hl1 : lam < 1) :
    (1 - lam) ^ 2 * Real.sin ((1 - p / 2) * θ) ^ 2 ≤
      (1 + lam) ^ 2 * Real.sin (p / 2 * θ) ^ 2 - 4 * lam * Real.sin ((1 - p / 2) * θ) ^ 2 ∧
    0 < (1 - lam) ^ 2 * Real.sin ((1 - p / 2) * θ) ^ 2 ∧
    0 < curveR p lam θ ∧ curveR p lam θ ≤ 1 ∧ curveD p lam θ (curveR p lam θ) = 0 := by
  obtain ⟨hs1, hs12, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  refine ⟨curveRoot_disc (lam := lam) hs1 hs12.le, ?_, curveRoot_pos hl hl1 hs1 hs12.le, curveRoot_le_one hl hl1 hs1 hs12, ?_⟩
  · have : 0 < 1 - lam := by linarith
    positivity
  · have h := curveRoot_isRoot hl hl1 hs1 hs12.le
    unfold curveD; unfold curveR; linarith

/-- sec5_sharp_inequality.tex l.49-51 (`λ ≠ 0`): "the zeros of D(θ, ·) have product 1/λ: for λ ≤ 0 there is no other
positive zero; for λ > 0 the other one, 1/(λR), gives the image of R e^{−iθ} under the inversion z ↦ 1/(λ z̄)". -/
theorem curve_root_product (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hl0 : lam ≠ 0) :
    (∀ r, curveD p lam θ r = -lam * Real.sin ((1 - p / 2) * θ) * (r - curveR p lam θ) *
      (r - 1 / (lam * curveR p lam θ))) ∧
    (lam < 0 → ∀ r, 0 < r → curveD p lam θ r = 0 → r = curveR p lam θ) ∧
    (0 < lam → curveD p lam θ (1 / (lam * curveR p lam θ)) = 0 ∧
      1 / ((lam : ℂ) * starRingEnd ℂ (curveZ p lam θ)) =
        ((1 / (lam * curveR p lam θ) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)) := by
  obtain ⟨-, -, -, -, hDR⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  obtain ⟨hs1, -, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  obtain ⟨-, -, hR0, -, -⟩ := curve_root_formula hp1 hp2 hθ0 hθ hl hl1
  set R := curveR p lam θ with hRdef
  have hfac : ∀ r, curveD p lam θ r = -lam * Real.sin ((1 - p / 2) * θ) * (r - R) * (r - 1 / (lam * R)) := by
    intro r
    have key : -lam * Real.sin ((1 - p / 2) * θ) * (r - R) * (r - 1 / (lam * R)) =
        curveD p lam θ r - r / R * curveD p lam θ R := by
      unfold curveD; field_simp; ring
    rw [key, hDR, mul_zero, sub_zero]
  refine ⟨hfac, fun hneg r hr hDr => ?_, fun hpos => ⟨by rw [hfac]; ring, ?_⟩⟩
  · rw [hfac] at hDr
    have h1 : 1 / (lam * R) < 0 := by
      rw [one_div_neg]; exact mul_neg_of_neg_of_pos hneg hR0
    have h2 : r - 1 / (lam * R) ≠ 0 := by linarith
    have h3 : -lam * Real.sin ((1 - p / 2) * θ) ≠ 0 := mul_ne_zero (by linarith) hs1.ne'
    rcases mul_eq_zero.1 hDr with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' h3
      · linarith
    · exact absurd h h2
  · unfold curveZ
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal,
      Complex.conj_I]
    have hE : Complex.exp (-(θ : ℂ) * -Complex.I) = (Complex.exp (-(θ : ℂ) * Complex.I))⁻¹ := by
      rw [← Complex.exp_neg]; ring_nf
    rw [hE]
    have hR : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0.ne'
    have hl' : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl0
    have hE0 : Complex.exp (-(θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    push_cast
    field_simp
    rw [← hRdef]
    exact div_self hR

/-- sec5_sharp_inequality.tex l.48-49: "R(π⁻) = 1, and r₀ := R(0⁺) ∈ (0, 1]" (with `r₀` the same root formula
at `s₁ = 1 - q`, `s₂ = q`). -/
theorem curve_root_limits (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    Tendsto (curveR p lam) (𝓝[<] Real.pi) (𝓝 1) ∧
    Tendsto (curveR p lam) (𝓝[>] 0) (𝓝 (curveRoot lam (1 - p / 2) (p / 2))) ∧
    0 < curveRoot lam (1 - p / 2) (p / 2) ∧ curveRoot lam (1 - p / 2) (p / 2) ≤ 1 := by
  have hq1 : 0 < 1 - p / 2 := by linarith
  have hq2 : 1 - p / 2 < p / 2 := by linarith
  refine ⟨?_, ?_, curveRoot_pos hl hl1 hq1 hq2.le, curveRoot_le_one hl hl1 hq1 hq2⟩
  · -- continuity at π, where s₁ = s₂ = sin(qπ) > 0
    have hsπ : Real.sin ((1 - p / 2) * Real.pi) = Real.sin (p / 2 * Real.pi) := by
      rw [show (1 - p / 2) * Real.pi = Real.pi - p / 2 * Real.pi by ring, Real.sin_pi_sub]
    have hspos : 0 < Real.sin (p / 2 * Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    have hval : curveR p lam Real.pi = 1 := by
      unfold curveR; rw [hsπ]; exact curveRoot_diag hl1 hspos
    have hden : (1 + lam) * Real.sin (p / 2 * Real.pi) + Real.sqrt ((1 + lam) ^ 2 * Real.sin (p / 2 * Real.pi) ^ 2 -
        4 * lam * Real.sin ((1 - p / 2) * Real.pi) ^ 2) ≠ 0 :=
      (curveRoot_den_pos hl hl1 (hsπ ▸ hspos) hsπ.le).ne'
    have hc : ContinuousAt (curveR p lam) Real.pi := by
      unfold curveR curveRoot
      exact ContinuousAt.div (by fun_prop) (by fun_prop) hden
    rw [← hval]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  · -- divide `s₁, s₂` by `θ > 0` and use `sinc`
    set A : ℝ → ℝ := fun θ => (1 - p / 2) * Real.sinc ((1 - p / 2) * θ) with hA
    set B : ℝ → ℝ := fun θ => p / 2 * Real.sinc (p / 2 * θ) with hB
    have hAc : Continuous A := continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))
    have hBc : Continuous B := continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))
    have hA0 : A 0 = 1 - p / 2 := by simp [hA]
    have hB0 : B 0 = p / 2 := by simp [hB]
    have hden : (1 + lam) * B 0 + Real.sqrt ((1 + lam) ^ 2 * B 0 ^ 2 - 4 * lam * A 0 ^ 2) ≠ 0 := by
      rw [hA0, hB0]; exact (curveRoot_den_pos hl hl1 hq1 hq2.le).ne'
    have hc : ContinuousAt (fun θ => curveRoot lam (A θ) (B θ)) 0 := by
      unfold curveRoot
      exact ContinuousAt.div (by fun_prop) (by fun_prop) hden
    have hlim := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simp only [hA0, hB0] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ (hθ : 0 < θ)
    have hsin : ∀ c : ℝ, 0 < c → Real.sin (c * θ) = θ * (c * Real.sinc (c * θ)) := by
      intro c hc
      rw [Real.sinc_of_ne_zero (by positivity)]
      field_simp
    unfold curveR
    rw [hsin _ hq1, hsin _ (by linarith : (0 : ℝ) < p / 2), curveRoot_smul hθ]

/-- sec5_sharp_inequality.tex l.48: "R is real-analytic" on `(0, π)`. -/
theorem curve_root_analytic (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) : AnalyticAt ℝ (curveR p lam) θ := by
  obtain ⟨hs1, hs12, -⟩ := curve_sines hp1 hp2 hθ0 hθ
  set d : ℝ → ℝ := fun x => (1 + lam) ^ 2 * Real.sin (p / 2 * x) ^ 2 - 4 * lam * Real.sin ((1 - p / 2) * x) ^ 2
    with hd
  have hdpos : 0 < d θ := by
    have h1 := curveRoot_disc (lam := lam) hs1 hs12.le
    have h2 : 0 < (1 - lam) ^ 2 * Real.sin ((1 - p / 2) * θ) ^ 2 := by
      have : 0 < 1 - lam := by linarith
      positivity
    simp only [hd]; linarith
  have hdan : AnalyticAt ℝ d θ := by simp only [hd]; fun_prop
  have hdc : ContinuousAt d θ := hdan.continuousAt
  have hsq : AnalyticAt ℝ (fun x => Real.sqrt (d x)) θ := by
    have hexp : AnalyticAt ℝ (fun x => Real.exp (Real.log (d x) * (1 / 2))) θ :=
      analyticAt_rexp.comp ((hdan.log hdpos).mul analyticAt_const)
    refine hexp.congr ?_
    filter_upwards [hdc.eventually (lt_mem_nhds hdpos)] with x hx
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  have hden : (1 + lam) * Real.sin (p / 2 * θ) + Real.sqrt (d θ) ≠ 0 :=
    (curveRoot_den_pos hl hl1 hs1 hs12.le).ne'
  have hnum : AnalyticAt ℝ (fun x => 2 * Real.sin ((1 - p / 2) * x)) θ := by fun_prop
  have hlin : AnalyticAt ℝ (fun x => (1 + lam) * Real.sin (p / 2 * x)) θ := by fun_prop
  exact hnum.div (hlin.add hsq) hden

end Curve

end GKSharp
