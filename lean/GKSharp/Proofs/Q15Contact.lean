/-
GKSharp/Proofs/Q15Contact.lean — paper 019 short v1.80, sec4b_failure.tex l.16, 26, 64, 94, 131 (the Q15 routes):
proofs of the rows q15_sec4b_T_sign, q15_sec4b_ray_signs, q15_sec4b_step6_identities, q15_sec4b_step6_normalized
and q15_sec4b_cDelta_quotient.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Route: the three rational contact identities (row contact_rational_identities), the Step 5 value of χ_y
(row contact_derivative_values), the factorization (row contact_sign_factorization), then field algebra.
-/
import GKSharp.Proofs.ContactScalar
import GKSharp.Proofs.ContactSign
import GKSharp.Proofs.Sec4bContactDeriv
import GKSharp.Proofs.StripExtras

namespace GKSharp.Proofs.Q15Contact

open Set Filter GKSharp.Threshold
open scoped Topology

private lemma sn_pos' {p : ℝ} (hp : 1 < p) : 0 < sn p :=
  Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hp)

private lemma cs_pos' {p : ℝ} (hp : 1 < p) (hp2 : p < 2) : 0 < cs p := by
  have hp0 : 0 < p := by linarith
  have h1 : Real.pi / 2 < Real.pi / p := by
    rw [lt_div_iff₀ hp0]
    nlinarith [Real.pi_pos]
  have h2 : Real.pi / p < Real.pi + Real.pi / 2 := by
    rw [div_lt_iff₀ hp0]
    nlinarith [Real.pi_pos]
  exact neg_pos.mpr (Real.cos_neg_of_pi_div_two_lt_of_lt h1 h2)

private lemma sn_sq_add_cs_sq (p : ℝ) : sn p ^ 2 + cs p ^ 2 = 1 := by
  unfold sn cs
  rw [neg_sq]
  exact Real.sin_sq_add_cos_sq _

/-- sec4b l.16 and l.94: `T(p) = sin²(π/p)(pp′/4 − 1 − cos²(π/p))/cos⁴(π/p)` is `d²` (`localD2`), `T = s₀²F/(4c₀⁴)`,
and on `1 < p < 2` the functions `T` and `F` have the same sign. -/
theorem q15_sec4b_T_sign_proved (p : ℝ) :
    localD2 p = Real.sin (Real.pi / p) ^ 2 * (p * (p / (p - 1)) / 4 - 1 - Real.cos (Real.pi / p) ^ 2) /
        Real.cos (Real.pi / p) ^ 4 ∧
    Real.sin (Real.pi / p) ^ 2 * (p * (p / (p - 1)) / 4 - 1 - Real.cos (Real.pi / p) ^ 2) /
        Real.cos (Real.pi / p) ^ 4 = sn p ^ 2 * localF p / (4 * cs p ^ 4) ∧
    (1 < p → p < 2 → SignType.sign (localD2 p) = SignType.sign (localF p)) := by
  have h1 : localD2 p = Real.sin (Real.pi / p) ^ 2 * (p * (p / (p - 1)) / 4 - 1 - Real.cos (Real.pi / p) ^ 2) /
      Real.cos (Real.pi / p) ^ 4 := by
    unfold localD2 sn cs dual
    ring
  have h2 : Real.sin (Real.pi / p) ^ 2 * (p * (p / (p - 1)) / 4 - 1 - Real.cos (Real.pi / p) ^ 2) /
      Real.cos (Real.pi / p) ^ 4 = sn p ^ 2 * localF p / (4 * cs p ^ 4) := by
    unfold localF sn cs dual
    ring
  refine ⟨h1, h2, fun hp hp2 => ?_⟩
  have hk : 0 < sn p ^ 2 / (4 * cs p ^ 4) := by
    have := sn_pos' hp
    have := cs_pos' hp hp2
    positivity
  rw [h1, h2, show sn p ^ 2 * localF p / (4 * cs p ^ 4) = sn p ^ 2 / (4 * cs p ^ 4) * localF p by ring,
    sign_mul, sign_pos hk, one_mul]

/-- On the ray `t = θ₀ = π/p`, `ζ + a ≠ 0` for real `a` (since `sin θ₀ ≠ 0`); `P_a = ‖ζ + a‖² > 0`. -/
private lemma ray_P_pos {p : ℝ} (hp : 1 < p) (a y : ℝ) (ha : a ≠ 0) :
    0 < Real.exp y * Real.exp y + 2 * a * Real.exp y * Real.cos (theta p) + a ^ 2 := by
  have hs : 0 < Real.sin (theta p) := sn_pos' hp
  have hsc := Real.sin_sq_add_cos_sq (theta p)
  nlinarith [sq_nonneg (Real.exp y + a * Real.cos (theta p)), sq_pos_of_ne_zero ha,
    mul_pos (sq_pos_of_ne_zero ha) (pow_pos hs 2)]

private lemma ray_norm_ne {p : ℝ} (hp : 1 < p) (a y : ℝ) (ha : a ≠ 0) : ‖zeta y (theta p) + (a : ℂ)‖ ≠ 0 := by
  have h := sec4b_norm_zeta_add_sq a y (theta p)
  have hP := ray_P_pos hp a y ha
  intro h0
  rw [h0] at h
  linarith

/-- The `y`-derivative of `log|w|` on the ray `t = θ₀` (`w = (ζ + λ)/(ζ + 1)`, `ζ = e^{y + iθ₀}`, `0 < λ`). -/
private lemma ray_log_hasDerivAt {p lam : ℝ} (hp : 1 < p) (hl0 : 0 < lam) (y : ℝ) :
    HasDerivAt (fun x => Real.log ‖mobContact lam (zeta x (theta p))‖)
      ((1 - lam) * Real.exp y ^ 2 * (1 + lam - cs p * (Real.exp y + lam / Real.exp y)) /
        ((Real.exp y * Real.exp y + 2 * lam * Real.exp y * Real.cos (theta p) + lam ^ 2) *
          (Real.exp y * Real.exp y + 2 * 1 * Real.exp y * Real.cos (theta p) + 1 ^ 2))) y := by
  have hf : (fun x => Real.log ‖mobContact lam (zeta x (theta p))‖) =
      fun x => chi lam x (theta p) - chi 1 x (theta p) := by
    funext x
    have h1 := ray_norm_ne hp lam x hl0.ne'
    have h2 : ‖zeta x (theta p) + 1‖ ≠ 0 := by
      simpa using ray_norm_ne hp 1 x one_ne_zero
    unfold mobContact chi
    rw [norm_div, Real.log_div h1 h2]
    push_cast
    ring_nf
  rw [hf]
  have hPl := ray_P_pos hp lam y hl0.ne'
  have hP1 := ray_P_pos hp 1 y one_ne_zero
  refine ((sec4b_hasDerivAt_chi_y (theta p) hPl.ne').sub
    (sec4b_hasDerivAt_chi_y (theta p) hP1.ne')).congr_deriv ?_
  have he0 : Real.exp y ≠ 0 := (Real.exp_pos y).ne'
  rw [div_sub_div _ _ hPl.ne' hP1.ne']
  congr 1
  have hcos : Real.cos (theta p) = -cs p := by unfold cs theta; ring
  rw [hcos]
  field_simp
  ring

/-- sec4b l.26 (`0 < λ < 1`): the sign of `∂_y log|w|` on the ray is the sign of `1 + λ − c₀(r + λ/r)`; it is
negative, positive, negative across the two positive roots `λ/r_*` and `r_*`; the smaller root is a local minimum and
the larger a local maximum of `log|w|`; `1 + λ − σ < 0`, i.e. `r² − σr + λ < 0` at `r = 1`, which places `1` between
the roots. -/
theorem q15_sec4b_ray_signs_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ioo (0 : ℝ) 1) :
    let f := fun y : ℝ => Real.log ‖mobContact lam (zeta y (theta p))‖
    let r₁ := lam / rContact p lam
    let r₂ := rContact p lam
    (∀ y : ℝ, SignType.sign (deriv f y) =
      SignType.sign (1 + lam - cs p * (Real.exp y + lam / Real.exp y))) ∧
    0 < r₁ ∧ r₁ < 1 ∧ 1 < r₂ ∧
    r₁ + lam / r₁ = sigmaContact p lam ∧ r₂ + lam / r₂ = sigmaContact p lam ∧
    (∀ r : ℝ, 0 < r → r < r₁ → 1 + lam - cs p * (r + lam / r) < 0) ∧
    (∀ r : ℝ, r₁ < r → r < r₂ → 0 < 1 + lam - cs p * (r + lam / r)) ∧
    (∀ r : ℝ, r₂ < r → 1 + lam - cs p * (r + lam / r) < 0) ∧
    IsLocalMin f (Real.log r₁) ∧ IsLocalMax f (Real.log r₂) ∧
    1 + lam - sigmaContact p lam < 0 ∧ (1 : ℝ) ^ 2 - sigmaContact p lam * 1 + lam < 0 := by
  intro f r₁ r₂
  obtain ⟨hl0, hl1⟩ := hlam
  obtain ⟨hr2, hlr, -, hsum⟩ := contact_root_properties hp hp2 ⟨by linarith, hl1⟩
  have hc := cs_pos' hp hp2
  have hc1 : cs p < 1 := by
    have := sn_pos' hp
    nlinarith [sn_sq_add_cs_sq p]
  have hr2pos : 0 < r₂ := by linarith
  have hr1pos : 0 < r₁ := div_pos hl0 hr2pos
  have hr1lt : r₁ < 1 := by
    show lam / rContact p lam < 1
    rw [div_lt_one hr2pos]
    linarith
  have hsig : 1 + lam = cs p * sigmaContact p lam := by
    unfold sigmaContact
    field_simp
  -- `1 + λ − c₀(r + λ/r) = −(c₀/r)(r − r₁)(r − r₂)`
  have key : ∀ r : ℝ, 0 < r → 1 + lam - cs p * (r + lam / r) = -(cs p / r) * ((r - r₁) * (r - r₂)) := by
    intro r hr
    rw [hsig, ← hsum]
    show _ = -(cs p / r) * ((r - lam / rContact p lam) * (r - rContact p lam))
    field_simp
    ring
  have hneg : ∀ r : ℝ, 0 < r → 0 < (r - r₁) * (r - r₂) → 1 + lam - cs p * (r + lam / r) < 0 := by
    intro r hr hpr
    rw [key r hr]
    have : 0 < cs p / r := div_pos hc hr
    nlinarith
  have hpos : ∀ r : ℝ, 0 < r → (r - r₁) * (r - r₂) < 0 → 0 < 1 + lam - cs p * (r + lam / r) := by
    intro r hr hpr
    rw [key r hr]
    have : 0 < cs p / r := div_pos hc hr
    nlinarith
  have hbelow : ∀ r : ℝ, 0 < r → r < r₁ → 1 + lam - cs p * (r + lam / r) < 0 := fun r hr h1 =>
    hneg r hr (mul_pos_of_neg_of_neg (by linarith) (by linarith))
  have hmid : ∀ r : ℝ, r₁ < r → r < r₂ → 0 < 1 + lam - cs p * (r + lam / r) := fun r h1 h2 =>
    hpos r (by linarith) (mul_neg_of_pos_of_neg (by linarith) (by linarith))
  have habove : ∀ r : ℝ, r₂ < r → 1 + lam - cs p * (r + lam / r) < 0 := fun r h2 =>
    hneg r (by linarith) (mul_pos (by linarith) (by linarith))
  -- the derivative and its sign
  have hd : ∀ y : ℝ, HasDerivAt f _ y := fun y => ray_log_hasDerivAt hp hl0 y
  have hden : ∀ y : ℝ, 0 < (1 - lam) * Real.exp y ^ 2 /
      ((Real.exp y * Real.exp y + 2 * lam * Real.exp y * Real.cos (theta p) + lam ^ 2) *
        (Real.exp y * Real.exp y + 2 * 1 * Real.exp y * Real.cos (theta p) + 1 ^ 2)) := by
    intro y
    have := ray_P_pos hp lam y hl0.ne'
    have := ray_P_pos hp 1 y one_ne_zero
    have : 0 < 1 - lam := by linarith
    positivity
  have hsign : ∀ y : ℝ, SignType.sign (deriv f y) =
      SignType.sign (1 + lam - cs p * (Real.exp y + lam / Real.exp y)) := by
    intro y
    rw [(hd y).deriv, mul_div_right_comm, sign_mul, sign_pos (hden y), one_mul]
  have hdiff : Differentiable ℝ f := fun y => (hd y).differentiableAt
  have hderiv_neg : ∀ y : ℝ, 1 + lam - cs p * (Real.exp y + lam / Real.exp y) < 0 → deriv f y < 0 := by
    intro y hy
    have h := hsign y
    rw [sign_neg hy] at h
    exact sign_eq_neg_one_iff.mp h
  have hderiv_pos : ∀ y : ℝ, 0 < 1 + lam - cs p * (Real.exp y + lam / Real.exp y) → 0 < deriv f y := by
    intro y hy
    have h := hsign y
    rw [sign_pos hy] at h
    exact sign_eq_one_iff.mp h
  have hy12 : Real.log r₁ < Real.log r₂ := Real.log_lt_log hr1pos (by linarith)
  have hmin : IsLocalMin f (Real.log r₁) := by
    refine isLocalMin_of_deriv_Ioo (a := Real.log r₁ - 1) (c := Real.log r₂) (by linarith) hy12
      (hdiff _).continuousAt hdiff.differentiableOn hdiff.differentiableOn ?_ ?_
    · intro x hx
      refine (hderiv_neg x (hbelow _ (Real.exp_pos x) ?_)).le
      rw [← Real.exp_log hr1pos]
      exact Real.exp_lt_exp.mpr hx.2
    · intro x hx
      refine (hderiv_pos x (hmid _ ?_ ?_)).le
      · rw [← Real.exp_log hr1pos]
        exact Real.exp_lt_exp.mpr hx.1
      · rw [← Real.exp_log hr2pos]
        exact Real.exp_lt_exp.mpr hx.2
  have hmax : IsLocalMax f (Real.log r₂) := by
    refine isLocalMax_of_deriv_Ioo (a := Real.log r₁) (c := Real.log r₂ + 1) hy12 (by linarith)
      (hdiff _).continuousAt hdiff.differentiableOn hdiff.differentiableOn ?_ ?_
    · intro x hx
      refine (hderiv_pos x (hmid _ ?_ ?_)).le
      · rw [← Real.exp_log hr1pos]
        exact Real.exp_lt_exp.mpr hx.1
      · rw [← Real.exp_log hr2pos]
        exact Real.exp_lt_exp.mpr hx.2
    · intro x hx
      refine (hderiv_neg x (habove _ ?_)).le
      rw [← Real.exp_log hr2pos]
      exact Real.exp_lt_exp.mpr hx.1
  have hroot1 : r₁ + lam / r₁ = sigmaContact p lam := by
    rw [← hsum]
    show lam / rContact p lam + lam / (lam / rContact p lam) = _
    field_simp
    ring
  have hgap : 1 + lam - sigmaContact p lam < 0 := by
    have : (1 + lam) * cs p < 1 + lam := by nlinarith
    have h := hsig
    nlinarith
  exact ⟨hsign, hr1pos, hr1lt, hr2, hroot1, hsum, hbelow, hmid, habove, hmin, hmax, hgap, by linarith⟩

/-- The scalar algebra of Step 6 from the three rational contact identities. -/
private lemma step6_algebra {p r lam c s2 D v σ χ : ℝ} (hr : 1 < r) (hlr : |lam| < r)
    (hc : c = (1 + lam) * r / (r ^ 2 + lam)) (hs : s2 = (r ^ 2 - 1) * (r ^ 2 - lam ^ 2) / (r ^ 2 + lam) ^ 2)
    (hD : D = (r ^ 2 - lam) * (r ^ 2 - lam ^ 2) / (r ^ 2 * (r ^ 2 + lam))) (hv : v = r - lam / r)
    (hσ : σ = r + lam / r) (hχ : χ = (1 - lam / r * c) / D) (hl : -1 < lam) :
    χ = r ^ 2 / (r ^ 2 - lam) ∧
    σ / v - p * χ + p / 2 = (1 - p / 2) * (σ / v) ∧
    s2 * v / (r * D) = (r ^ 2 - 1) / (r ^ 2 + lam) ∧
    2 * lam * (s2 * v / (r * D)) + (1 - lam) = (1 + lam) * (r ^ 2 - lam) / (r ^ 2 + lam) ∧
    (1 + lam) * (r ^ 2 - lam) / (r ^ 2 + lam) = c * v ∧
    c ^ 2 * v ^ 2 = (1 + lam) ^ 2 - 4 * lam * c ^ 2 ∧
    2 * p * lam * (1 - lam) / (r * v * D) + p * (1 - lam) ^ 2 / (s2 * v ^ 2) =
      p * (1 - lam) * c / (s2 * v) := by
  have hr0 : r ≠ 0 := by positivity
  have hlam2 : lam ^ 2 < r ^ 2 := by
    have := abs_nonneg lam
    nlinarith [sq_abs lam]
  have hA : r ^ 2 + lam ≠ 0 := by nlinarith
  have hB : r ^ 2 - lam ≠ 0 := by
    have : lam ≤ |lam| := le_abs_self lam
    nlinarith
  have hC : r ^ 2 - lam ^ 2 ≠ 0 := by nlinarith
  have hE : r ^ 2 - 1 ≠ 0 := by nlinarith
  have hvv : r ^ 2 - lam = r * v := by rw [hv]; field_simp
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hvv
    exact hB hvv
  have hχ' : χ = r ^ 2 / (r ^ 2 - lam) := by
    rw [hχ, hc, hD]
    field_simp
    ring
  have hs2v : s2 * v / (r * D) = (r ^ 2 - 1) / (r ^ 2 + lam) := by
    rw [hs, hD, hv]
    field_simp
  have hs20 : s2 ≠ 0 := by
    rw [hs]
    exact div_ne_zero (mul_ne_zero hE hC) (pow_ne_zero 2 hA)
  have hD0 : D ≠ 0 := by
    rw [hD]
    exact div_ne_zero (mul_ne_zero hB hC) (mul_ne_zero (pow_ne_zero 2 hr0) hA)
  refine ⟨hχ', ?_, hs2v, ?_, ?_, ?_, ?_⟩
  · rw [hχ', hσ, hv]
    field_simp
    ring
  · rw [hs2v]
    field_simp
    ring
  · rw [hc, hv]
    field_simp
  · rw [hc, hv]
    field_simp
    ring
  · rw [hs, hD, hv, hc]
    field_simp
    ring

/-- sec4b l.64 (Step 6, `X = r²`, `δ = 1 − λ`): the contact identities `χ_y = X/(X − λ)`,
`σ/v − pχ_y + p/2 = (1 − p/2)σ/v`, `s₀²v/(rD₁) = (X − 1)/(X + λ)`; hence `2λs₀²v/(rD₁) + δ = (1+λ)(X−λ)/(X+λ) = c₀v`
and `c₀²v² = (1+λ)² − 4λc₀²`; the first combines the two positive terms into `pδc₀/(s₀²v)`. -/
theorem q15_sec4b_step6_identities_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let r := rContact p lam
    let X := r ^ 2
    let δ := 1 - lam
    let v := vContact p lam
    let D := dOne p lam
    let σ := sigmaContact p lam
    let χy := dy (chi lam) (yContact p lam) (theta p)
    χy = X / (X - lam) ∧
    σ / v - p * χy + p / 2 = (1 - p / 2) * (σ / v) ∧
    sn p ^ 2 * v / (r * D) = (X - 1) / (X + lam) ∧
    2 * lam * (sn p ^ 2 * v / (r * D)) + δ = (1 + lam) * (X - lam) / (X + lam) ∧
    (1 + lam) * (X - lam) / (X + lam) = cs p * v ∧
    cs p ^ 2 * v ^ 2 = (1 + lam) ^ 2 - 4 * lam * cs p ^ 2 ∧
    2 * p * lam * δ / (r * v * D) + p * δ ^ 2 / (sn p ^ 2 * v ^ 2) = p * δ * cs p / (sn p ^ 2 * v) ∧
    (0 < lam → 0 < 2 * p * lam * δ / (r * v * D) ∧ 0 < p * δ ^ 2 / (sn p ^ 2 * v ^ 2)) := by
  intro r X δ v D σ χy
  obtain ⟨hr, hlr, hv, hsum⟩ := contact_root_properties hp hp2 hlam
  obtain ⟨hc, hs, hD⟩ := contact_rational_identities_proved p lam hp hp2 hlam
  have hχ := (contact_derivative_values_proved p lam hp hp2 hlam).2.2.2.1
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := step6_algebra (p := p) hr hlr hc hs hD rfl hsum.symm hχ hlam.1
  refine ⟨e1, e2, e3, e4, e5, e6, e7, fun hl0 => ⟨?_, ?_⟩⟩
  · have hD0 : 0 < D := by
      show 0 < dOne p lam
      rw [hD]
      have hlam2 : lam ^ 2 < r ^ 2 := by nlinarith [sq_abs lam, abs_nonneg lam]
      have : 0 < r ^ 2 - lam := by nlinarith [le_abs_self lam]
      have : 0 < r ^ 2 - lam ^ 2 := by linarith
      have : 0 < r ^ 2 + lam := by nlinarith
      positivity
    have : 0 < δ := by show 0 < 1 - lam; linarith [hlam.2]
    have : 0 < r := by linarith
    have : 0 < p := by linarith
    positivity
  · have : 0 < δ := by show 0 < 1 - lam; linarith [hlam.2]
    have : 0 < sn p := sn_pos' hp
    have : 0 < p := by linarith
    positivity

/-- sec4b l.64 (Step 6, with l.68-70 of short v1.70 moved): `B₀ = δ(1+λ)²/(c₀³s₀²v³) > 0`;
`e^{qy_*}μ_*″(θ₀)/(pPB₀) = (p−1)c₀⁴v²/(1+λ)² − s₀²(1 − p/2)²`; with `c₀²v² = (1+λ)² − 4λc₀²` and `c₀² + s₀² = 1` this is
the bracket `(p−1)(1 − 4λc₀⁴/(1+λ)²) − p²s₀²/4`. -/
theorem q15_sec4b_step6_normalized_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let v := vContact p lam
    bZero p lam = (1 - lam) * (1 + lam) ^ 2 / (cs p ^ 3 * sn p ^ 2 * v ^ 3) ∧ 0 < bZero p lam ∧
    Real.exp (q p * y) * muSecond p lam / (p * weightP p lam y (theta p) * bZero p lam) =
      (p - 1) * cs p ^ 4 * v ^ 2 / (1 + lam) ^ 2 - sn p ^ 2 * (1 - p / 2) ^ 2 ∧
    (p - 1) * cs p ^ 4 * v ^ 2 / (1 + lam) ^ 2 - sn p ^ 2 * (1 - p / 2) ^ 2 =
      (p - 1) * (1 - 4 * lam * cs p ^ 4 / (1 + lam) ^ 2) - p ^ 2 * sn p ^ 2 / 4 := by
  intro y v
  obtain ⟨hB, hfac, -⟩ := contact_sign_factorization_proved p lam hp hp2 hlam
  have hcv := (q15_sec4b_step6_identities_proved p lam hp hp2 hlam).2.2.2.2.2.1
  have hl : 1 + lam ≠ 0 := by linarith [hlam.1]
  have hbr : (p - 1) * cs p ^ 4 * v ^ 2 / (1 + lam) ^ 2 - sn p ^ 2 * (1 - p / 2) ^ 2 =
      (p - 1) * (1 - 4 * lam * cs p ^ 4 / (1 + lam) ^ 2) - p ^ 2 * sn p ^ 2 / 4 := by
    have hs2 : sn p ^ 2 = 1 - cs p ^ 2 := by linarith [sn_sq_add_cs_sq p]
    have h4 : (p - 1) * cs p ^ 4 * v ^ 2 = (p - 1) * cs p ^ 2 * (cs p ^ 2 * v ^ 2) := by ring
    rw [h4, hcv, hs2]
    field_simp
    ring
  refine ⟨rfl, hB, ?_, hbr⟩
  rw [← div_div, hfac, mul_div_cancel_left₀ _ hB.ne', hbr]
  rfl

/-- sec4b l.131 (`C = C(δ)`, the root near 1 of `s₀C² − δC − s₀(1 − δ) = 0`, `δ < 1`): `s₀(C² − 1) = δ(C − s₀)`, so
`(C − 1)/δ = (C − s₀)/(s₀(C + 1))` for `δ ≠ 0`; the right side has a positive denominator and is continuous at
`δ = 0` (regular there). -/
theorem q15_sec4b_cDelta_quotient_proved (p δ : ℝ) (hp : 1 < p) (hd : δ < 1) :
    sn p * (cDelta p δ ^ 2 - 1) = δ * (cDelta p δ - sn p) ∧
    0 < sn p * (cDelta p δ + 1) ∧
    (δ ≠ 0 → (cDelta p δ - 1) / δ = (cDelta p δ - sn p) / (sn p * (cDelta p δ + 1))) ∧
    ContinuousAt (fun d => (cDelta p d - sn p) / (sn p * (cDelta p d + 1))) 0 := by
  obtain ⟨hq, hC⟩ := cDelta_quadratic_proved p δ hp hd
  have hs := sn_pos' hp
  have h1 : sn p * (cDelta p δ ^ 2 - 1) = δ * (cDelta p δ - sn p) := by linear_combination hq
  have hden : 0 < sn p * (cDelta p δ + 1) := mul_pos hs (by linarith)
  refine ⟨h1, hden, fun hδ => ?_, ?_⟩
  · rw [div_eq_div_iff hδ hden.ne']
    linear_combination h1
  · have hcont : Continuous (fun d => cDelta p d) := by
      unfold cDelta
      fun_prop
    have hden0 : sn p * (cDelta p 0 + 1) ≠ 0 :=
      (mul_pos hs (by linarith [(cDelta_quadratic_proved p 0 hp (by norm_num)).2])).ne'
    exact ((hcont.continuousAt.sub continuousAt_const).div
      (continuousAt_const.mul (hcont.continuousAt.add continuousAt_const)) hden0)

end GKSharp.Proofs.Q15Contact
