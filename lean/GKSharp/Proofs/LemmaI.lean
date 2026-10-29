/- GKSharp/Proofs/LemmaI.lean - Lemma I, the inversion z' = 1/(lam conj z) (sec5_sharp_inequality.tex l.124-134).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.RealLine

namespace GKSharp

open ComplexConjugate

/-- `x^p = (x^{p/2})²` for `x ≥ 0`. -/
lemma rpow_eq_sq_half (x p : ℝ) (hx : 0 ≤ x) : x ^ p = (x ^ (p / 2)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- `|1 + λ z|² - λ|1 + z|² = (1 - λ)(1 - λ|z|²)` (sec5_sharp_inequality.tex l.132). -/
lemma inversion_sign_identity (lam : ℝ) (z : ℂ) :
    ‖1 + (lam : ℂ) * z‖ ^ 2 - lam * ‖1 + z‖ ^ 2 = (1 - lam) * (1 - lam * ‖z‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

section inversion
variable {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : z ≠ 0)
include hlam hz

lemma inv_point_eq : 1 / ((lam : ℂ) * conj z) = (((1 / (lam * ‖z‖ ^ 2)) : ℝ) : ℂ) * z := by
  have hz' : conj z ≠ 0 := (map_ne_zero _).2 hz
  have hzz : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.conj_mul']; push_cast; ring
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hz)
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  calc 1 / ((lam : ℂ) * conj z) = z / ((lam : ℂ) * (conj z * z)) := by field_simp
    _ = (((1 / (lam * ‖z‖ ^ 2)) : ℝ) : ℂ) * z := by rw [hzz]; push_cast; field_simp

omit hz in
lemma norm_inv_point : ‖1 / ((lam : ℂ) * conj z)‖ = 1 / (lam * ‖z‖) := by
  rw [norm_div, norm_one, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hlam.le]

lemma arg_inv_point : Complex.arg (1 / ((lam : ℂ) * conj z)) = Complex.arg z := by
  rw [inv_point_eq hlam hz, Complex.arg_real_mul _ (by have := norm_pos_iff.2 hz; positivity)]

lemma norm_one_add_inv_point : ‖1 + 1 / ((lam : ℂ) * conj z)‖ = ‖1 + (lam : ℂ) * z‖ / (lam * ‖z‖) := by
  have hz' : conj z ≠ 0 := (map_ne_zero _).2 hz
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have : 1 + 1 / ((lam : ℂ) * conj z) = conj (1 + (lam : ℂ) * z) / ((lam : ℂ) * conj z) := by
    rw [map_add, map_one, map_mul, Complex.conj_ofReal]; field_simp; ring
  rw [this, norm_div, Complex.norm_conj, norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg hlam.le]

lemma norm_one_add_lam_inv_point : ‖1 + (lam : ℂ) * (1 / ((lam : ℂ) * conj z))‖ = ‖1 + z‖ / ‖z‖ := by
  have hz' : conj z ≠ 0 := (map_ne_zero _).2 hz
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have : 1 + (lam : ℂ) * (1 / ((lam : ℂ) * conj z)) = conj (1 + z) / conj z := by
    rw [map_add, map_one]; field_simp; ring
  rw [this, norm_div, Complex.norm_conj, Complex.norm_conj]

end inversion

/-- Lemma I (sec5_sharp_inequality.tex l.124-134), for `0 < λ < 1`, `1 < p < 2`, `q = p/2`, `C ≥ 0`, any `K`, `z ≠ 0`,
`z' = 1/(λ z̄)`: (1) `𝒟_C(z) - λ^q|z|^p 𝒟_C(z') = (C^p + λ^q)(|1+z|^p - λ^{-q}|1+λz|^p)`; (2) this is positive exactly
when `|z| > 1/√λ`; (3) i.e. (for `z ≠ -1`) when `|w| < √λ`; (4) so `𝒟_C ≥ 0` on `{|z| ≤ 1/√λ}` implies `𝒟_C > 0`
on `{|z| > 1/√λ}`; (5) in the `w`-plane, `z ↦ z'` is `w ↦ λ/w̄`. -/
theorem lemma_I {p C K lam : ℝ} (hp : 1 < p) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hC : 0 ≤ C) :
    (∀ z : ℂ, z ≠ 0 →
      critD p C K lam z - lam ^ (p / 2) * ‖z‖ ^ p * critD p C K lam (1 / ((lam : ℂ) * conj z)) =
        (C ^ p + lam ^ (p / 2)) * (‖1 + z‖ ^ p - lam ^ (-(p / 2)) * ‖1 + (lam : ℂ) * z‖ ^ p)) ∧
    (∀ z : ℂ, 0 < (C ^ p + lam ^ (p / 2)) * (‖1 + z‖ ^ p - lam ^ (-(p / 2)) * ‖1 + (lam : ℂ) * z‖ ^ p) ↔
      1 / Real.sqrt lam < ‖z‖) ∧
    (∀ z : ℂ, z ≠ -1 → (1 / Real.sqrt lam < ‖z‖ ↔ ‖mobW lam z‖ < Real.sqrt lam)) ∧
    ((∀ u : ℂ, ‖u‖ ≤ 1 / Real.sqrt lam → 0 ≤ critD p C K lam u) →
      ∀ u : ℂ, 1 / Real.sqrt lam < ‖u‖ → 0 < critD p C K lam u) ∧
    (∀ z : ℂ, z ≠ 0 → z ≠ -1 → 1 + (lam : ℂ) * z ≠ 0 →
      mobW lam (1 / ((lam : ℂ) * conj z)) = (lam : ℂ) / conj (mobW lam z)) := by
  have hp0 : 0 < p := by linarith
  have hLq : 0 < lam ^ (p / 2) := Real.rpow_pos_of_pos hlam0 _
  have hCp : 0 ≤ C ^ p := Real.rpow_nonneg hC _
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam0
  -- (1) the identity
  have hid : ∀ z : ℂ, z ≠ 0 →
      critD p C K lam z - lam ^ (p / 2) * ‖z‖ ^ p * critD p C K lam (1 / ((lam : ℂ) * conj z)) =
        (C ^ p + lam ^ (p / 2)) * (‖1 + z‖ ^ p - lam ^ (-(p / 2)) * ‖1 + (lam : ℂ) * z‖ ^ p) := by
    intro z hz
    have ha : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [critD, reQPow]
    rw [norm_one_add_inv_point hlam0 hz, norm_one_add_lam_inv_point hlam0 hz, norm_inv_point hlam0 (z := z),
      arg_inv_point hlam0 hz]
    rw [Real.div_rpow (norm_nonneg _) (by positivity), Real.div_rpow (norm_nonneg _) ha.le,
      Real.div_rpow zero_le_one (by positivity), Real.one_rpow, Real.mul_rpow hlam0.le ha.le,
      Real.mul_rpow hlam0.le ha.le, Real.rpow_neg hlam0.le,
      rpow_eq_sq_half lam p hlam0.le, rpow_eq_sq_half ‖z‖ p ha.le]
    have hAq : 0 < ‖z‖ ^ (p / 2) := Real.rpow_pos_of_pos ha _
    field_simp
    ring
  -- the comparison `|1 + λz| < √λ |1 + z|  ↔  |z| > 1/√λ`
  have hcmp : ∀ z : ℂ, ‖1 + (lam : ℂ) * z‖ < Real.sqrt lam * ‖1 + z‖ ↔ 1 / Real.sqrt lam < ‖z‖ := by
    intro z
    have hi := inversion_sign_identity lam z
    have hs2 := Real.sq_sqrt hlam0.le
    rw [← sq_lt_sq₀ (norm_nonneg _) (by positivity), mul_pow, hs2, div_lt_iff₀ hsl]
    constructor
    · intro h
      have h1 : 1 < lam * ‖z‖ ^ 2 := by nlinarith
      by_contra hcon
      have h2 : ‖z‖ * Real.sqrt lam ≤ 1 := not_lt.1 hcon
      nlinarith [mul_nonneg (norm_nonneg z) hsl.le]
    · intro h
      have h1 : 1 < lam * ‖z‖ ^ 2 := by nlinarith
      nlinarith
  have hlamq : lam ^ (p / 2) = Real.sqrt lam ^ p := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlam0.le]; ring_nf
  have hbr : ∀ z : ℂ, 0 < ‖1 + z‖ ^ p - lam ^ (-(p / 2)) * ‖1 + (lam : ℂ) * z‖ ^ p ↔
      ‖1 + (lam : ℂ) * z‖ < Real.sqrt lam * ‖1 + z‖ := by
    intro z
    rw [Real.rpow_neg hlam0.le, sub_pos, inv_mul_lt_iff₀ hLq, hlamq,
      ← Real.mul_rpow hsl.le (norm_nonneg _), Real.rpow_lt_rpow_iff (norm_nonneg _) (by positivity) hp0]
  have hsign : ∀ z : ℂ, 0 < (C ^ p + lam ^ (p / 2)) *
      (‖1 + z‖ ^ p - lam ^ (-(p / 2)) * ‖1 + (lam : ℂ) * z‖ ^ p) ↔ 1 / Real.sqrt lam < ‖z‖ := by
    intro z
    rw [← hcmp z, ← hbr z]
    constructor
    · intro h; exact pos_of_mul_pos_right h (by positivity)
    · intro h; positivity
  refine ⟨hid, hsign, ?_, ?_, ?_⟩
  -- (3) the `|w|` form
  · intro z hz1
    have h1z : 0 < ‖1 + z‖ := norm_pos_iff.2 (by intro h; apply hz1; linear_combination h)
    rw [mobW, norm_div, div_lt_iff₀ h1z, hcmp z]
  -- (4) the extension
  · intro hge u hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hu
      exact absurd hu (not_lt.2 (by positivity))
    have hua : 0 < ‖u‖ := norm_pos_iff.2 hu0
    have hsmall : ‖1 / ((lam : ℂ) * conj u)‖ ≤ 1 / Real.sqrt lam := by
      rw [norm_inv_point hlam0 (z := u)]
      rw [div_lt_iff₀ hsl] at hu
      rw [div_le_div_iff₀ (by positivity) hsl, one_mul, one_mul]
      have hs2 := Real.sq_sqrt hlam0.le
      nlinarith
    have h1 := hge _ hsmall
    have h2 := (hsign u).2 hu
    have h3 := hid u hu0
    have h4 : 0 ≤ lam ^ (p / 2) * ‖u‖ ^ p * critD p C K lam (1 / ((lam : ℂ) * conj u)) :=
      mul_nonneg (mul_nonneg hLq.le (Real.rpow_nonneg (norm_nonneg _) _)) h1
    linarith
  -- (5) the `w`-plane form
  · intro z hz hz1 hlz
    have hz' : conj z ≠ 0 := (map_ne_zero _).2 hz
    have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam0.ne'
    have h1 : 1 + conj z ≠ 0 := by
      intro h; apply hz1
      have := congrArg conj h
      rw [map_add, map_one, Complex.conj_conj, map_zero] at this
      linear_combination this
    have h2 : 1 + (lam : ℂ) * conj z ≠ 0 := by
      intro h; apply hlz
      have := congrArg conj h
      rw [map_add, map_one, map_mul, Complex.conj_conj, Complex.conj_ofReal, map_zero] at this
      exact this
    have h3 : (lam : ℂ) * conj z + 1 ≠ 0 := by rw [add_comm]; exact h2
    have h4 : conj z + 1 ≠ 0 := by rw [add_comm]; exact h1
    simp only [mobW, map_div₀, map_add, map_one, map_mul, Complex.conj_ofReal]
    field_simp
    ring

end GKSharp
