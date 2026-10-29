/- GKSharp/Proofs/Window.lean - sec3_nonreal.tex l.18-29: the disk `D_C`, the window half-angle (3.3), Lemma W.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GKRoot
import GKSharp.Defs.Window

namespace GKSharp

/-! ### Coordinates -/

theorem norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- `c (C² - 1) = -(C² - ρ)`, in coordinates. -/
theorem diskCentre_coords {C : ℝ} (hC : 1 < C) (ρ : ℂ) :
    (diskCentre C ρ).re * (C ^ 2 - 1) = -(C ^ 2 - ρ.re) ∧ (diskCentre C ρ).im * (C ^ 2 - 1) = ρ.im := by
  have hX : ((C ^ 2 - 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by nlinarith)
  have h : diskCentre C ρ * ((C ^ 2 - 1 : ℝ) : ℂ) = -(((C ^ 2 : ℝ) : ℂ) - ρ) := by
    unfold diskCentre
    rw [← Complex.ofReal_pow, show ((C ^ 2 : ℝ) : ℂ) - 1 = ((C ^ 2 - 1 : ℝ) : ℂ) by norm_cast, neg_mul,
      div_mul_cancel₀ _ hX]
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.sub_re, Complex.sub_im] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- `(C² - 1)(R² - |ζ - c|²) = |ζ + ρ|² - C²|ζ + 1|²`. -/
theorem disk_identity {C : ℝ} (hC : 1 < C) (ρ ζ : ℂ) :
    (C ^ 2 - 1) * (diskRadiusSq C ρ - ‖ζ - diskCentre C ρ‖ ^ 2) = ‖ζ + ρ‖ ^ 2 - C ^ 2 * ‖ζ + 1‖ ^ 2 := by
  obtain ⟨hre, him⟩ := diskCentre_coords hC ρ
  have hX : C ^ 2 - 1 ≠ 0 := by nlinarith
  have hd : (C ^ 2 - 1) * ((C ^ 2 - ‖ρ‖ ^ 2) / (C ^ 2 - 1)) = C ^ 2 - ‖ρ‖ ^ 2 := mul_div_cancel₀ _ hX
  have hρ := norm_sq_eq ρ
  unfold diskRadiusSq
  rw [norm_sq_eq (ζ - diskCentre C ρ), norm_sq_eq (diskCentre C ρ), norm_sq_eq (ζ + ρ), norm_sq_eq (ζ + 1)]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
  linear_combination (2 * ζ.re) * hre + (2 * ζ.im) * him - hd + hρ

/-! ### c7 -/

theorem obstacleG_neg_iff {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C) (ρ ζ : ℂ) :
    obstacleG p C ρ ζ < 0 ↔ C * ‖ζ + 1‖ < ‖ζ + ρ‖ := by
  unfold obstacleG
  rw [sub_neg, ← Real.mul_rpow hC (norm_nonneg _), add_comm (1 : ℂ) ζ, add_comm ρ ζ,
    Real.rpow_lt_rpow_iff (mul_nonneg hC (norm_nonneg _)) (norm_nonneg _) hp]

theorem lt_iff_mem_disk {C : ℝ} (hC : 1 < C) (ρ ζ : ℂ) :
    C * ‖ζ + 1‖ < ‖ζ + ρ‖ ↔ ‖ζ - diskCentre C ρ‖ ^ 2 < diskRadiusSq C ρ := by
  have hid := disk_identity hC ρ ζ
  have hX : 0 < C ^ 2 - 1 := by nlinarith
  have hC0 : 0 ≤ C := by linarith
  have h1 := norm_nonneg (ζ + 1)
  have h2 := norm_nonneg (ζ + ρ)
  have key : C * ‖ζ + 1‖ < ‖ζ + ρ‖ ↔ 0 < ‖ζ + ρ‖ ^ 2 - C ^ 2 * ‖ζ + 1‖ ^ 2 := by
    constructor
    · intro h; nlinarith [mul_nonneg hC0 h1]
    · intro h
      by_contra hn
      have hn' := not_lt.1 hn
      nlinarith [mul_nonneg hC0 h1, mul_le_mul hn' hn' h2 (mul_nonneg hC0 h1)]
  rw [key, ← hid]
  exact ⟨fun h => sub_pos.1 (pos_of_mul_pos_right h hX.le), fun h => mul_pos hX (sub_pos.2 h)⟩

/-- c7, sec3_nonreal.tex l.18-21: `G_C < 0` exactly on `D_C = {|ζ + ρ| > C|ζ + 1|}`, which is the open disk with
centre `c` and radius `R`; it contains `-1` (when `ρ ≠ 1`) and its closure does not contain `0`. -/
theorem disk_of_obstacle {p C : ℝ} (hp : 0 < p) (ρ : ℂ) (hC : max 1 ‖ρ‖ < C) :
    (∀ ζ : ℂ, obstacleG p C ρ ζ < 0 ↔ C * ‖ζ + 1‖ < ‖ζ + ρ‖) ∧
      (∀ ζ : ℂ, C * ‖ζ + 1‖ < ‖ζ + ρ‖ ↔ ‖ζ - diskCentre C ρ‖ ^ 2 < diskRadiusSq C ρ) ∧
      (ρ ≠ 1 → ‖(-1 : ℂ) - diskCentre C ρ‖ ^ 2 < diskRadiusSq C ρ) ∧
      diskRadiusSq C ρ < ‖diskCentre C ρ‖ ^ 2 := by
  have hC1 : 1 < C := lt_of_le_of_lt (le_max_left _ _) hC
  have hρC : ‖ρ‖ < C := lt_of_le_of_lt (le_max_right _ _) hC
  refine ⟨fun ζ => obstacleG_neg_iff hp (by linarith) ρ ζ, fun ζ => lt_iff_mem_disk hC1 ρ ζ, fun hρ => ?_, ?_⟩
  · refine (lt_iff_mem_disk hC1 ρ (-1)).1 ?_
    rw [neg_add_cancel, norm_zero, mul_zero]
    exact norm_pos_iff.2 (fun h => hρ (by linear_combination h))
  · unfold diskRadiusSq
    have hn := norm_nonneg ρ
    have : 0 < (C ^ 2 - ‖ρ‖ ^ 2) / (C ^ 2 - 1) := div_pos (by nlinarith) (by nlinarith)
    linarith

/-! ### c8 -/

theorem norm_diskCentre {C : ℝ} (hC : 1 < C) (ρ : ℂ) :
    ‖diskCentre C ρ‖ = ‖(C : ℂ) ^ 2 - ρ‖ / (C ^ 2 - 1) := by
  have hX : 0 < C ^ 2 - 1 := by nlinarith
  unfold diskCentre
  rw [norm_neg, norm_div, show (C : ℂ) ^ 2 - 1 = ((C ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hX]

/-- c8, sec3_nonreal.tex l.23-25, (3.3): for `ρ ≠ 1` the half-angle lies in `(0, π/2)` and
`cos² ψ(C) = (C² - |ρ|²)(C² - 1)/|C² - ρ|²`. -/
theorem window_cos_sq {C : ℝ} {ρ : ℂ} (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    0 < windowHalfAngle C ρ ∧ windowHalfAngle C ρ < Real.pi / 2 ∧
      Real.cos (windowHalfAngle C ρ) ^ 2 = (C ^ 2 - ‖ρ‖ ^ 2) * (C ^ 2 - 1) / ‖(C : ℂ) ^ 2 - ρ‖ ^ 2 := by
  have hC1 : 1 < C := lt_of_le_of_lt (le_max_left _ _) hC
  have hX : 0 < C ^ 2 - 1 := by nlinarith
  obtain ⟨-, -, hm1, hRc⟩ := disk_of_obstacle one_pos ρ hC
  have hR : 0 < diskRadiusSq C ρ := lt_of_le_of_lt (sq_nonneg _) (hm1 hρ)
  have hc2 : 0 < ‖diskCentre C ρ‖ ^ 2 := hR.trans hRc
  have hc : 0 < ‖diskCentre C ρ‖ := lt_of_le_of_ne (norm_nonneg _) fun h => by
    rw [← h] at hc2; norm_num at hc2
  have hw : windowHalfAngle C ρ = Real.arcsin (Real.sqrt (diskRadiusSq C ρ) / ‖diskCentre C ρ‖) := rfl
  have hs0 : 0 < Real.sqrt (diskRadiusSq C ρ) / ‖diskCentre C ρ‖ := div_pos (Real.sqrt_pos.2 hR) hc
  have hs2 : (Real.sqrt (diskRadiusSq C ρ) / ‖diskCentre C ρ‖) ^ 2 = diskRadiusSq C ρ / ‖diskCentre C ρ‖ ^ 2 := by
    rw [div_pow, Real.sq_sqrt hR.le]
  have hs1 : Real.sqrt (diskRadiusSq C ρ) / ‖diskCentre C ρ‖ < 1 := by
    have h : (Real.sqrt (diskRadiusSq C ρ) / ‖diskCentre C ρ‖) ^ 2 < 1 := by
      rw [hs2, div_lt_one hc2]; exact hRc
    nlinarith
  rw [hw]
  refine ⟨Real.arcsin_pos.2 hs0, Real.arcsin_lt_pi_div_two.2 hs1, ?_⟩
  have hA : 0 < ‖(C : ℂ) ^ 2 - ρ‖ := by
    have := norm_diskCentre hC1 ρ
    rw [this] at hc
    exact (div_pos_iff_of_pos_right hX).1 hc
  rw [Real.cos_arcsin, Real.sq_sqrt (by nlinarith), hs2]
  unfold diskRadiusSq
  rw [norm_diskCentre hC1 ρ]
  field_simp
  ring

/-! ### c9, Lemma W -/

/-- On `(0, π/2)`, `x = y ↔ cos² x = cos² y`. -/
theorem eq_iff_cos_sq_eq {x y : ℝ} (hx0 : 0 < x) (hx1 : x < Real.pi / 2) (hy0 : 0 < y) (hy1 : y < Real.pi / 2) :
    x = y ↔ Real.cos x ^ 2 = Real.cos y ^ 2 := by
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩
  have hcy : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith, hy1⟩
  have hf : (Real.cos x - Real.cos y) * (Real.cos x + Real.cos y) = 0 := by linear_combination h
  have hxy : Real.cos x = Real.cos y := by
    rcases mul_eq_zero.1 hf with h1 | h1
    · linarith
    · linarith
  exact Real.injOn_cos ⟨hx0.le, by linarith [Real.pi_pos]⟩ ⟨hy0.le, by linarith [Real.pi_pos]⟩ hxy

/-- `max(p, p') > 2` for `1 < p`, `p ≠ 2`. -/
theorem two_lt_max {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) : 2 < max p (p / (p - 1)) := by
  rcases lt_or_gt_of_ne hp2 with h | h
  · exact lt_max_of_lt_right ((lt_div_iff₀ (by linarith)).2 (by linarith))
  · exact lt_max_of_lt_left h

/-- `cos²(π/max(p, p')) = cos²(π/p)`. -/
theorem cos_sq_max {p : ℝ} (hp : 1 < p) : Real.cos (Real.pi / max p (p / (p - 1))) ^ 2 = Real.cos (Real.pi / p) ^ 2 := by
  rcases max_choice p (p / (p - 1)) with h | h
  · rw [h]
  · rw [h, show Real.pi / (p / (p - 1)) = Real.pi - Real.pi / p by
      have : p - 1 ≠ 0 := by linarith
      have : p ≠ 0 := by linarith
      field_simp, Real.cos_pi_sub, neg_sq]

/-- With `X = C²`: `sin²(π/p) · (X² - gkMid X + |ρ|²) = (X - |ρ|²)(X - 1) - cos²(π/p) |X - ρ|²`. -/
theorem gkQuad_mul_sin_sq {p : ℝ} (hp : 1 < p) (ρ : ℂ) (C : ℝ) :
    Real.sin (Real.pi / p) ^ 2 * gkQuad p ρ (C ^ 2) =
      (C ^ 2 - ‖ρ‖ ^ 2) * (C ^ 2 - 1) - Real.cos (Real.pi / p) ^ 2 * ‖(C : ℂ) ^ 2 - ρ‖ ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hsin : Real.sin (Real.pi / p) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by rw [div_lt_iff₀ hp0]; nlinarith [Real.pi_pos])).ne'
  have hcot : Real.cot (Real.pi / p) ^ 2 * Real.sin (Real.pi / p) ^ 2 = Real.cos (Real.pi / p) ^ 2 := by
    rw [Real.cot_eq_cos_div_sin, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hsin)]
  have hpy := Real.sin_sq_add_cos_sq (Real.pi / p)
  unfold gkQuad gkMid
  rw [norm_sq_eq ρ, norm_sq_eq (1 - ρ), norm_sq_eq ((C : ℂ) ^ 2 - ρ), ← Complex.ofReal_pow]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination ((C ^ 2) ^ 2 - (1 + (ρ.re ^ 2 + ρ.im ^ 2)) * C ^ 2 + (ρ.re ^ 2 + ρ.im ^ 2)) * hpy -
    (((1 - ρ.re) ^ 2 + (0 - ρ.im) ^ 2) * C ^ 2) * hcot

/-- `gkQuad p ρ (C²) = 0 ↔ C = GK_p(ρ)` for `C > max(1, |ρ|)`: the smaller root is `|ρ|²/GK² < C²`. -/
theorem gkQuad_eq_zero_iff {p : ℝ} {ρ : ℂ} {C : ℝ} (hC : max 1 ‖ρ‖ < C) : gkQuad p ρ (C ^ 2) = 0 ↔ C = gk p ρ := by
  have hC1 : 1 < C := lt_of_le_of_lt (le_max_left _ _) hC
  have hρC : ‖ρ‖ < C := lt_of_le_of_lt (le_max_right _ _) hC
  have hn := norm_nonneg ρ
  have hX1 : 1 < C ^ 2 := by nlinarith
  have hXn : ‖ρ‖ ^ 2 < C ^ 2 := by nlinarith
  have hprod : gkRootHi p ρ * gkRootLo p ρ = ‖ρ‖ ^ 2 := by
    have h := gkQuad_factor p ρ 0
    simp only [gkQuad] at h
    linarith
  have hlohi := gkRootLo_le_hi p ρ
  have hlo0 := gkRootLo_nonneg p ρ
  have hg := gk_nonneg p ρ
  rw [gkQuad_factor, mul_eq_zero, sub_eq_zero, sub_eq_zero, ← gk_sq_eq]
  constructor
  · rintro (h | h)
    · nlinarith
    · exfalso
      nlinarith [mul_le_mul_of_nonneg_right hlohi hlo0]
  · intro h; left; rw [h]

/-- c9, Lemma W (sec3_nonreal.tex l.27-29; Section 3 assumes `1 < p`, `p ≠ 2`): for `ρ ≠ 1`, `C = GK_p(ρ)` is the
unique `C > max(1, |ρ|)` at which the window has width `2ψ(C) = 2π/max(p, p')`. (Existence: `gk_gt_max`.) -/
theorem lemma_W {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {ρ : ℂ} (hρ : ρ ≠ 1) {C : ℝ} (hC : max 1 ‖ρ‖ < C) :
    2 * windowHalfAngle C ρ = 2 * Real.pi / max p (p / (p - 1)) ↔ C = gk p ρ := by
  obtain ⟨hψ0, hψ1, hcos⟩ := window_cos_sq hρ hC
  have hm2 := two_lt_max hp hp2
  have hm0 : 0 < max p (p / (p - 1)) := by linarith
  have hθ0 : 0 < Real.pi / max p (p / (p - 1)) := div_pos Real.pi_pos hm0
  have hθ1 : Real.pi / max p (p / (p - 1)) < Real.pi / 2 := div_lt_div_of_pos_left Real.pi_pos two_pos hm2
  have hC1 : 1 < C := lt_of_le_of_lt (le_max_left _ _) hC
  have hX : 0 < C ^ 2 - 1 := by nlinarith
  have hp0 : 0 < p := by linarith
  have hsin : 0 < Real.sin (Real.pi / p) ^ 2 :=
    pow_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by rw [div_lt_iff₀ hp0]; nlinarith [Real.pi_pos])) 2
  have hA : 0 < ‖(C : ℂ) ^ 2 - ρ‖ ^ 2 := by
    have := norm_diskCentre hC1 ρ
    have hc := (window_cos_sq hρ hC).1
    by_contra h0
    have h00 : ‖(C : ℂ) ^ 2 - ρ‖ = 0 := by nlinarith [norm_nonneg ((C : ℂ) ^ 2 - ρ)]
    rw [h00, zero_div] at this
    have : diskCentre C ρ = 0 := norm_eq_zero.1 this
    obtain ⟨-, -, -, hRc⟩ := disk_of_obstacle one_pos ρ hC
    obtain ⟨-, -, hm1, -⟩ := disk_of_obstacle one_pos ρ hC
    have hR : 0 < diskRadiusSq C ρ := lt_of_le_of_lt (sq_nonneg _) (hm1 hρ)
    rw [this, norm_zero] at hRc
    nlinarith
  have e1 : 2 * windowHalfAngle C ρ = 2 * Real.pi / max p (p / (p - 1)) ↔
      windowHalfAngle C ρ = Real.pi / max p (p / (p - 1)) := by
    rw [mul_div_assoc]
    exact ⟨fun h => mul_left_cancel₀ two_ne_zero h, fun h => by rw [h]⟩
  rw [e1, eq_iff_cos_sq_eq hψ0 hψ1 hθ0 hθ1, cos_sq_max hp, hcos, div_eq_iff hA.ne', ← gkQuad_eq_zero_iff hC]
  have key := gkQuad_mul_sin_sq hp ρ C
  constructor
  · intro h
    have : Real.sin (Real.pi / p) ^ 2 * gkQuad p ρ (C ^ 2) = 0 := by rw [key]; linarith
    exact (mul_eq_zero.1 this).resolve_left hsin.ne'
  · intro h
    rw [h, mul_zero] at key
    linarith

end GKSharp
