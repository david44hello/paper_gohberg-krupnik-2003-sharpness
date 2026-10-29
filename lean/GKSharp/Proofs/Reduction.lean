/-
GKSharp/Proofs/Reduction.lean — Proposition (Reduction), short v0.70 sec5_sharp_inequality.tex l.139-163: if `K_f`
decreases strictly on `(0, π)` then `D_C ≥ 0` on `ℂ`, with zeros only at `z_*` and `z̄_*`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.MobiusDict
import GKSharp.Proofs.LemmaI
import GKSharp.Proofs.Contact
import GKSharp.Proofs.Sec5Lambda
import GKSharp.Proofs.GKRoot
import GKSharp.Proofs.GKProps
import GKSharp.Proofs.A1
import GKSharp.Proofs.CircleExtrema
import GKSharp.Proofs.SharpA2
import GKSharp.Proofs.SharpA3
import GKSharp.Proofs.ReductionStep1
import GKSharp.Proofs.ReductionStep2
import GKSharp.Proofs.ReductionStep4

namespace GKSharp.Proofs.Reduction

open GKSharp ComplexConjugate Filter Topology Set

/-! ### Helpers -/

/-- eq:K: `K = 2(1−λ) C s₀^{p−2} c₀^{1−q} (C² + λ)^{q−1} > 0`, as `C = GK_p(λ) > 1`. -/
theorem kConst_pos {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    0 < kConst p lam := by
  have hC : 1 < gk p lam := by
    have hmax := gk_gt_max hp1 hp2.ne (ρ := (lam : ℂ)) (by exact_mod_cast hl1.ne)
    exact lt_of_le_of_lt (le_max_left _ _) hmax
  have hp0 : 0 < p := by linarith
  have hθ0 : 0 < Real.pi / p := div_pos Real.pi_pos hp0
  have hθπ : Real.pi / p < Real.pi := (div_lt_iff₀ hp0).mpr (by nlinarith [Real.pi_pos])
  have hθ2 : Real.pi / 2 < Real.pi / p := div_lt_div_of_pos_left Real.pi_pos hp0 hp2
  have hs : 0 < Real.sin (Real.pi / p) := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hc : 0 < -Real.cos (Real.pi / p) := by
    have := Real.cos_neg_of_pi_div_two_lt_of_lt hθ2 (by linarith [Real.pi_pos])
    linarith
  have hsum : 0 < gk p lam ^ 2 + lam := by nlinarith
  unfold kConst
  have h1 : 0 < 1 - lam := by linarith
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) h1) (by linarith))
    (Real.rpow_pos_of_pos hs _)) (Real.rpow_pos_of_pos hc _)) (Real.rpow_pos_of_pos hsum _)

/-- `z_* = R(θ₀)e^{−iθ₀}` is not `−1` (its imaginary part vanishes only if `R = 0`), nor is its conjugate. -/
theorem curveZ_ne_neg_one {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    curveZ p lam (Real.pi / p) ≠ -1 ∧ conj (curveZ p lam (Real.pi / p)) ≠ -1 := by
  have hp0 : 0 < p := by linarith
  have hθ0 : 0 < Real.pi / p := div_pos Real.pi_pos hp0
  have hθπ : Real.pi / p < Real.pi := (div_lt_iff₀ hp0).mpr (by nlinarith [Real.pi_pos])
  have hs : 0 < Real.sin (Real.pi / p) := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hform : curveZ p lam (Real.pi / p) =
      ((curveR p lam (Real.pi / p) : ℝ) : ℂ) * Complex.exp (((-(Real.pi / p) : ℝ) : ℂ) * Complex.I) := by
    rw [curveZ]; push_cast; ring_nf
  have hne : curveZ p lam (Real.pi / p) ≠ -1 := by
    intro h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    rw [hform, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im] at him
    rw [hform, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at hre
    simp only [Complex.neg_im, Complex.one_im, neg_zero, Real.sin_neg, mul_neg, neg_eq_zero] at him
    simp only [Complex.neg_re, Complex.one_re] at hre
    have hR : curveR p lam (Real.pi / p) = 0 := by
      rcases mul_eq_zero.mp him with h0 | h0
      · exact h0
      · exact absurd h0 hs.ne'
    rw [hR, zero_mul] at hre
    norm_num at hre
  refine ⟨hne, fun h => hne ?_⟩
  have := congrArg conj h
  rwa [Complex.conj_conj, map_neg, map_one] at this

lemma mobW_conj (lam : ℝ) (z : ℂ) : mobW lam (conj z) = conj (mobW lam z) := by
  simp [mobW, map_div₀, Complex.conj_ofReal]

/-- `Φ(w̄) = Φ(w)` (`Q(w̄) = conj Q(w)` and `Re` of a power is conjugation invariant). -/
theorem mobPhi_conj (p C K lam : ℝ) (w : ℂ) : mobPhi p C K lam (conj w) = mobPhi p C K lam w := by
  have hQ : mobQ lam (conj w) = conj (mobQ lam w) := by
    simp [mobQ, map_mul, map_sub, Complex.conj_ofReal]
  simp only [mobPhi, Complex.norm_conj, hQ, Proofs.CircleExtrema.reQPow_conj]

/-- On the circle `|w| = ρ`: `Φ(ρe^{iφ}) = (1−λ)^p (C^p − ρ^p) − K f_ρ(φ)` (sec5_sharp_inequality.tex l.25, l.28). -/
theorem mobPhi_polar (p C K lam : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (φ : ℝ) :
    mobPhi p C K lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) =
      (1 - lam) ^ p * (C ^ p - ρ ^ p) - K * fRho p lam ρ φ := by
  have hn : ‖(ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ = ρ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ]
  simp only [mobPhi, hn, fRho]

/-- The contact value `Φ(w(θ₀)) = (1−λ)^p Λ(θ₀) = 0` (sec5_sharp_inequality.tex l.106-108 with l.95-96). -/
theorem mobPhi_contact_zero {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam (Real.pi / p))) = 0 := by
  have hp0 : 0 < p := by linarith
  have hθ0 : 0 < Real.pi / p := div_pos Real.pi_pos hp0
  have hθπ : Real.pi / p < Real.pi := (div_lt_iff₀ hp0).mpr (by nlinarith [Real.pi_pos])
  have hL := (Proofs.Sec5Lambda.sec5_Lambda_proved (C := gk p lam) (K := kConst p lam)
    hp1 hp2 hl hl1 hθ0 hθπ).2
  rw [contact_Lambda hp1 hp2 hl hl1 _, zero_div] at hL
  exact (div_eq_zero_iff.mp hL).resolve_right (Real.rpow_pos_of_pos (by linarith) _).ne'

/-- Step 3, sec5_sharp_inequality.tex l.155-159, in the `w`-plane, from the facts it uses: (A3) on each circle
(`hA3a` for `ρ > ρ₀`, `hA3b` for `ρ ≤ ρ₀`), Steps 1-2 (`h1`, `h1'`, `h2`) and the contact value `Φ(w(θ₀)) = 0`. -/
theorem reduction_step3_of {p C K lam ρ0 : ℝ} (hK : 0 < K)
    (hA3a : ∀ ρ : ℝ, ρ0 < ρ → ∃ φc θ : ℝ, θ ∈ Ioo 0 Real.pi ∧
      (ρ : ℂ) * Complex.exp ((φc : ℂ) * Complex.I) = mobW lam (curveZ p lam θ) ∧
      ∀ φ ∈ Icc 0 Real.pi, φ ≠ φc → fRho p lam ρ φ < fRho p lam ρ φc)
    (hA3b : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 → (0 < lam → Real.sqrt lam ≤ ρ) →
      ∀ φ ∈ Icc 0 Real.pi, fRho p lam ρ φ ≤ fRho p lam ρ 0)
    (h1 : ∀ θ ∈ Ioo 0 Real.pi, θ ≠ Real.pi / p → 0 < mobPhi p C K lam (mobW lam (curveZ p lam θ)))
    (h1' : 0 < mobPhi p C K lam (ρ0 : ℂ))
    (h2 : ∀ ρ : ℝ, 0 ≤ ρ → (0 < lam → Real.sqrt lam ≤ ρ) → ρ ≤ ρ0 →
      mobPhi p C K lam (ρ0 : ℂ) ≤ mobPhi p C K lam (ρ : ℂ))
    (hstar : mobPhi p C K lam (mobW lam (curveZ p lam (Real.pi / p))) = 0) :
    ∀ w : ℂ, (0 < lam → Real.sqrt lam ≤ ‖w‖) →
      0 ≤ mobPhi p C K lam w ∧
      (mobPhi p C K lam w = 0 →
        w = mobW lam (curveZ p lam (Real.pi / p)) ∨ w = conj (mobW lam (curveZ p lam (Real.pi / p)))) := by
  set wstar := mobW lam (curveZ p lam (Real.pi / p))
  -- the curve values are `≥ 0`, and `= 0` only at `θ₀`
  have hcurve : ∀ θ ∈ Ioo 0 Real.pi, 0 ≤ mobPhi p C K lam (mobW lam (curveZ p lam θ)) ∧
      (mobPhi p C K lam (mobW lam (curveZ p lam θ)) = 0 → mobW lam (curveZ p lam θ) = wstar) := by
    intro θ hθ
    by_cases he : θ = Real.pi / p
    · subst he; exact ⟨hstar.ge, fun _ => rfl⟩
    · exact ⟨(h1 θ hθ he).le, fun h0 => absurd h0 (h1 θ hθ he).ne'⟩
  -- the upper half circle `u = ρe^{iψ}`, `ψ ∈ [0, π]`
  have hupper : ∀ ρ ψ : ℝ, 0 ≤ ρ → ψ ∈ Icc 0 Real.pi → (0 < lam → Real.sqrt lam ≤ ρ) →
      0 ≤ mobPhi p C K lam ((ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) ∧
      (mobPhi p C K lam ((ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) = 0 →
        (ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) = wstar) := by
    intro ρ ψ hρ hψ hlam
    rw [mobPhi_polar p C K lam hρ]
    rcases lt_or_ge ρ0 ρ with hgt | hle
    · obtain ⟨φc, θ, hθ, hpt, hmax⟩ := hA3a ρ hgt
      have hval : mobPhi p C K lam (mobW lam (curveZ p lam θ)) =
          (1 - lam) ^ p * (C ^ p - ρ ^ p) - K * fRho p lam ρ φc := by
        rw [← hpt, mobPhi_polar p C K lam hρ]
      obtain ⟨hc0, hcz⟩ := hcurve θ hθ
      rcases eq_or_ne ψ φc with hψc | hψc
      · subst hψc
        refine ⟨by rw [← hval]; exact hc0, fun h0 => ?_⟩
        rw [hpt]; exact hcz (by rw [hval]; exact h0)
      · have hlt := hmax ψ hψ hψc
        have hstrict : (1 - lam) ^ p * (C ^ p - ρ ^ p) - K * fRho p lam ρ φc <
            (1 - lam) ^ p * (C ^ p - ρ ^ p) - K * fRho p lam ρ ψ := by
          have := mul_lt_mul_of_pos_left hlt hK; linarith
        rw [← hval] at hstrict
        exact ⟨(hc0.trans_lt hstrict).le, fun h0 => absurd h0 (hc0.trans_lt hstrict).ne'⟩
    · have hreal : (1 - lam) ^ p * (C ^ p - ρ ^ p) - K * fRho p lam ρ 0 = mobPhi p C K lam (ρ : ℂ) := by
        rw [← mobPhi_polar p C K lam hρ 0]; simp
      have hpos : 0 < mobPhi p C K lam (ρ : ℂ) := h1'.trans_le (h2 ρ hρ hlam hle)
      rcases eq_or_lt_of_le hρ with hρ0' | hρpos
      · subst hρ0'
        have h00 : (1 - lam) ^ p * (C ^ p - (0 : ℝ) ^ p) - K * fRho p lam 0 ψ =
            mobPhi p C K lam ((0 : ℝ) : ℂ) := by
          rw [← mobPhi_polar p C K lam le_rfl ψ]; simp
        rw [h00]
        exact ⟨hpos.le, fun h0 => absurd h0 hpos.ne'⟩
      · have hle0 := hA3b ρ hρpos hle hlam ψ hψ
        have hge : mobPhi p C K lam (ρ : ℂ) ≤ (1 - lam) ^ p * (C ^ p - ρ ^ p) - K * fRho p lam ρ ψ := by
          rw [← hreal]; have := mul_le_mul_of_nonneg_left hle0 hK.le; linarith
        exact ⟨hpos.le.trans hge, fun h0 => absurd h0 (hpos.trans_le hge).ne'⟩
  -- every `w` is `u` or `ū` for such a `u`
  intro w hw
  have hpolar := Complex.norm_mul_exp_arg_mul_I w
  rcases le_or_gt 0 w.im with him | him
  · have hψ : Complex.arg w ∈ Icc 0 Real.pi := ⟨Complex.arg_nonneg_iff.mpr him, Complex.arg_le_pi w⟩
    obtain ⟨hnn, hz⟩ := hupper ‖w‖ (Complex.arg w) (norm_nonneg w) hψ hw
    rw [hpolar] at hnn hz
    exact ⟨hnn, fun h0 => Or.inl (hz h0)⟩
  · have him' : 0 ≤ (conj w).im := by rw [Complex.conj_im]; linarith
    have hψ : Complex.arg (conj w) ∈ Icc 0 Real.pi :=
      ⟨Complex.arg_nonneg_iff.mpr him', Complex.arg_le_pi _⟩
    have hw' : 0 < lam → Real.sqrt lam ≤ ‖conj w‖ := by rw [Complex.norm_conj]; exact hw
    obtain ⟨hnn, hz⟩ := hupper ‖conj w‖ (Complex.arg (conj w)) (norm_nonneg _) hψ hw'
    rw [Complex.norm_mul_exp_arg_mul_I, mobPhi_conj] at hnn hz
    refine ⟨hnn, fun h0 => Or.inr ?_⟩
    have := congrArg conj (hz h0)
    rwa [Complex.conj_conj] at this

/-- The nonnegative form of Step 3, as used for Theorem C* (sec5e_cstar.tex l.19-22): curve values `≥ 0` and the real
segment `≥ 0` give `Φ ≥ 0` on every circle `|w| = ρ` (`ρ ≥ √λ` if `λ > 0`), by (A3). -/
theorem reduction_step3_nonneg_of {p C K lam ρ0 : ℝ} (hK : 0 < K)
    (hA3a : ∀ ρ : ℝ, ρ0 < ρ → ∃ φc θ : ℝ, θ ∈ Ioo 0 Real.pi ∧
      (ρ : ℂ) * Complex.exp ((φc : ℂ) * Complex.I) = mobW lam (curveZ p lam θ) ∧
      ∀ φ ∈ Icc 0 Real.pi, φ ≠ φc → fRho p lam ρ φ < fRho p lam ρ φc)
    (hA3b : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 → (0 < lam → Real.sqrt lam ≤ ρ) →
      ∀ φ ∈ Icc 0 Real.pi, fRho p lam ρ φ ≤ fRho p lam ρ 0)
    (hcurve : ∀ θ ∈ Ioo 0 Real.pi, 0 ≤ mobPhi p C K lam (mobW lam (curveZ p lam θ)))
    (hreal : ∀ ρ : ℝ, 0 ≤ ρ → (0 < lam → Real.sqrt lam ≤ ρ) → ρ ≤ ρ0 → 0 ≤ mobPhi p C K lam (ρ : ℂ)) :
    ∀ w : ℂ, (0 < lam → Real.sqrt lam ≤ ‖w‖) → 0 ≤ mobPhi p C K lam w := by
  -- the upper half circle `u = ρe^{iψ}`, `ψ ∈ [0, π]`
  have hupper : ∀ ρ ψ : ℝ, 0 ≤ ρ → ψ ∈ Icc 0 Real.pi → (0 < lam → Real.sqrt lam ≤ ρ) →
      0 ≤ mobPhi p C K lam ((ρ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)) := by
    intro ρ ψ hρ hψ hlam
    rw [mobPhi_polar p C K lam hρ]
    rcases lt_or_ge ρ0 ρ with hgt | hle
    · obtain ⟨φc, θ, hθ, hpt, hmax⟩ := hA3a ρ hgt
      have hval : mobPhi p C K lam (mobW lam (curveZ p lam θ)) =
          (1 - lam) ^ p * (C ^ p - ρ ^ p) - K * fRho p lam ρ φc := by
        rw [← hpt, mobPhi_polar p C K lam hρ]
      have hle' : fRho p lam ρ ψ ≤ fRho p lam ρ φc := by
        rcases eq_or_ne ψ φc with h | h
        · rw [h]
        · exact (hmax ψ hψ h).le
      have := mul_le_mul_of_nonneg_left hle' hK.le
      linarith [hcurve θ hθ]
    · have hreal' : (1 - lam) ^ p * (C ^ p - ρ ^ p) - K * fRho p lam ρ 0 = mobPhi p C K lam (ρ : ℂ) := by
        rw [← mobPhi_polar p C K lam hρ 0]; simp
      rcases eq_or_lt_of_le hρ with hρ0' | hρpos
      · subst hρ0'
        have h00 : (1 - lam) ^ p * (C ^ p - (0 : ℝ) ^ p) - K * fRho p lam 0 ψ =
            mobPhi p C K lam ((0 : ℝ) : ℂ) := by
          rw [← mobPhi_polar p C K lam le_rfl ψ]; simp
        rw [h00]
        exact hreal 0 le_rfl hlam hle
      · have hle0 := hA3b ρ hρpos hle hlam ψ hψ
        have := mul_le_mul_of_nonneg_left hle0 hK.le
        linarith [hreal ρ hρ hlam hle]
  -- every `w` is `u` or `ū` for such a `u`
  intro w hw
  rcases le_or_gt 0 w.im with him | him
  · have hψ : Complex.arg w ∈ Icc 0 Real.pi := ⟨Complex.arg_nonneg_iff.mpr him, Complex.arg_le_pi w⟩
    have h := hupper ‖w‖ (Complex.arg w) (norm_nonneg w) hψ hw
    rwa [Complex.norm_mul_exp_arg_mul_I] at h
  · have him' : 0 ≤ (conj w).im := by rw [Complex.conj_im]; linarith
    have hψ : Complex.arg (conj w) ∈ Icc 0 Real.pi :=
      ⟨Complex.arg_nonneg_iff.mpr him', Complex.arg_le_pi _⟩
    have hw' : 0 < lam → Real.sqrt lam ≤ ‖conj w‖ := by rw [Complex.norm_conj]; exact hw
    have h := hupper ‖conj w‖ (Complex.arg (conj w)) (norm_nonneg _) hψ hw'
    rwa [Complex.norm_mul_exp_arg_mul_I, mobPhi_conj] at h

/-- From `Φ ≥ 0` on the circles `|w| ≥ √λ` (`λ > 0`; all `w` if `λ ≤ 0`): `D_C ≥ 0` on `ℂ` (the nonnegative half of
Steps 4-5: (5.1) and the Möbius map off `−1`, Step 4 at `−1`, Lemma I for `|z| > 1/√λ`). -/
theorem critD_nonneg_of_step3 {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hstep3 : ∀ w : ℂ, (0 < lam → Real.sqrt lam ≤ ‖w‖) → 0 ≤ mobPhi p (gk p lam) (kConst p lam) lam w) :
    ∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z := by
  have hnear : ∀ z : ℂ, z ≠ -1 → (0 < lam → ‖z‖ ≤ 1 / Real.sqrt lam) →
      0 ≤ critD p (gk p lam) (kConst p lam) lam z := by
    intro z hz hzl
    have hw : 0 < lam → Real.sqrt lam ≤ ‖mobW lam z‖ := by
      intro hl0
      have hiff := (lemma_I (C := gk p lam) (K := kConst p lam) hp1 hl0 hl1
        (zero_le_one.trans (one_le_gk p _))).2.2.1 z hz
      by_contra hlt
      exact absurd (hiff.mpr (not_le.mp hlt)) (not_lt.mpr (hzl hl0))
    have hfac : 0 ≤ ‖1 + z‖ ^ p / (1 - lam) ^ p := by
      have h2 : 0 < 1 - lam := by linarith
      positivity
    rw [critD_eq_mobPhi p (gk p lam) (kConst p lam) hl1 hz]
    exact mul_nonneg hfac (hstep3 _ hw)
  have hball : ∀ᶠ z in 𝓝 (-1 : ℂ), 0 < lam → ‖z‖ ≤ 1 / Real.sqrt lam := by
    by_cases hl0 : 0 < lam
    · have hgt : ‖(-1 : ℂ)‖ < 1 / Real.sqrt lam := by
        rw [norm_neg, norm_one, lt_div_iff₀ (Real.sqrt_pos.mpr hl0), one_mul]
        exact (Real.sqrt_lt' one_pos).mpr (by linarith)
      filter_upwards [(continuous_norm.tendsto (-1 : ℂ)).eventually (gt_mem_nhds hgt)] with z hz _
      exact hz.le
    · exact Eventually.of_forall fun _ h => absurd h hl0
  have h4 : 0 < critD p (gk p lam) (kConst p lam) lam (-1) := by
    refine reduction_step4 hp1 hp2 hl1 (kConst_pos hp1 hp2 hl hl1) ?_
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hz hz1
    exact hnear z hz1 hz
  have hnear_all : ∀ z : ℂ, (0 < lam → ‖z‖ ≤ 1 / Real.sqrt lam) →
      0 ≤ critD p (gk p lam) (kConst p lam) lam z := by
    intro z hzl
    by_cases hz : z = -1
    · subst hz; exact h4.le
    · exact hnear z hz hzl
  intro z
  by_cases hl0 : 0 < lam
  · rcases le_or_gt ‖z‖ (1 / Real.sqrt lam) with hz | hz
    · exact hnear_all z (fun _ => hz)
    · exact ((lemma_I (C := gk p lam) (K := kConst p lam) hp1 hl0 hl1
        (zero_le_one.trans (one_le_gk p _))).2.2.2.1 (fun u hu => hnear_all u (fun _ => hu)) z hz).le
  · exact hnear_all z (fun h => absurd h hl0)

/-! ### Steps 3-5 from (A2), the limit of `w(θ)` at `0⁺` and Step 1 -/

/-- Step 3 (l.155-159) with its inputs: (A3) from (A1) and (A2) (`sec5_A3_of_A1_A2`), Step 1 (`h1`), Step 2
(`reduction_step2`, which uses the limit `hw`), and the contact value. -/
theorem reduction_step3 {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hdec : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi))
    (hA2 : let r0 := curveRoot lam (1 - p / 2) (p / 2)
      let ρ0 := (1 + lam * r0) / (1 + r0)
      ContinuousOn (fun θ => ‖mobW lam (curveZ p lam θ)‖) (Set.Ioo 0 Real.pi) ∧
      StrictMonoOn (fun θ => ‖mobW lam (curveZ p lam θ)‖) (Set.Ioo 0 Real.pi) ∧
      Tendsto (fun θ => ‖mobW lam (curveZ p lam θ)‖) (𝓝[<] Real.pi) atTop ∧
      Tendsto (fun θ => ‖mobW lam (curveZ p lam θ)‖) (𝓝[>] 0) (𝓝 ρ0) ∧
      0 ≤ ρ0 ∧ ρ0 < 1 ∧
      (∀ θ ∈ Set.Ioo 0 Real.pi, 0 < deriv (fun θ => ‖mobW lam (curveZ p lam θ)‖) θ) ∧
      (0 < lam → (1 + lam) / 2 ≤ ρ0 ∧ Real.sqrt lam < (1 + lam) / 2))
    (hw : Tendsto (fun θ => mobW lam (curveZ p lam θ)) (𝓝[>] 0)
      (𝓝 ((((1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) : ℝ)) : ℂ)))
    (h1 : (∀ θ ∈ Set.Ioo 0 Real.pi, θ ≠ Real.pi / p →
        0 < mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam θ))) ∧
      0 < mobPhi p (gk p lam) (kConst p lam) lam
        ((((1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) : ℝ)) : ℂ)) :
    ∀ w : ℂ, (0 < lam → Real.sqrt lam ≤ ‖w‖) →
      0 ≤ mobPhi p (gk p lam) (kConst p lam) lam w ∧
      (mobPhi p (gk p lam) (kConst p lam) lam w = 0 →
        w = mobW lam (curveZ p lam (Real.pi / p)) ∨ w = conj (mobW lam (curveZ p lam (Real.pi / p)))) := by
  have hρ0 : 0 ≤ (1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) :=
    hA2.2.2.2.2.1
  have hA3 : ∀ ρ : ℝ, 0 < ρ → _ := fun ρ hρ =>
    Proofs.SharpA3.sec5_A3_of_A1_A2 hp1 hp2 hl hl1 hρ (sec5_A1_proved hp1 hp2 hl hl1 hρ) hA2
  refine reduction_step3_of (kConst_pos hp1 hp2 hl hl1) (fun ρ hgt => ?_) (fun ρ hρ hle hlam => ?_)
    h1.1 h1.2 (reduction_step2 hp1 hp2 hl hl1 hdec hw) (mobPhi_contact_zero hp1 hp2 hl hl1)
  · have h := hA3 ρ (hρ0.trans_lt hgt)
    dsimp only at h
    obtain ⟨φc, -, θ, hθ, -, hpt, -, -, hmax⟩ := h.1 hgt
    exact ⟨φc, θ, hθ, hpt, hmax⟩
  · have h := hA3 ρ hρ
    dsimp only at h
    exact (h.2 hle hlam).2

/-- The `z`-plane form of Step 3 (via (5.1) and the Möbius map), on `z ≠ −1` (and `|z| ≤ 1/√λ` if `λ > 0`). -/
lemma reduction_near {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl1 : lam < 1)
    (hstep3 : ∀ w : ℂ, (0 < lam → Real.sqrt lam ≤ ‖w‖) →
      0 ≤ mobPhi p (gk p lam) (kConst p lam) lam w ∧
      (mobPhi p (gk p lam) (kConst p lam) lam w = 0 →
        w = mobW lam (curveZ p lam (Real.pi / p)) ∨ w = conj (mobW lam (curveZ p lam (Real.pi / p)))))
    (z : ℂ) (hz : z ≠ -1) (hzl : 0 < lam → ‖z‖ ≤ 1 / Real.sqrt lam) :
    0 ≤ critD p (gk p lam) (kConst p lam) lam z ∧
    (critD p (gk p lam) (kConst p lam) lam z = 0 →
      z = curveZ p lam (Real.pi / p) ∨ z = conj (curveZ p lam (Real.pi / p))) := by
  have hD := critD_eq_mobPhi p (gk p lam) (kConst p lam) hl1 hz
  have hw : 0 < lam → Real.sqrt lam ≤ ‖mobW lam z‖ := by
    intro hl0
    have hiff := (lemma_I (C := gk p lam) (K := kConst p lam) hp1 hl0 hl1
      (zero_le_one.trans (one_le_gk p _))).2.2.1 z hz
    by_contra hlt
    exact absurd (hiff.mpr (not_le.mp hlt)) (not_lt.mpr (hzl hl0))
  obtain ⟨hnn, hzero⟩ := hstep3 (mobW lam z) hw
  have hfac : 0 < ‖1 + z‖ ^ p / (1 - lam) ^ p := by
    have h1 : 0 < ‖1 + z‖ := norm_pos_iff.mpr (fun h => hz (by linear_combination h))
    have h2 : 0 < 1 - lam := by linarith
    positivity
  refine ⟨by rw [hD]; exact mul_nonneg hfac.le hnn, fun h0 => ?_⟩
  rw [hD] at h0
  have hΦ : mobPhi p (gk p lam) (kConst p lam) lam (mobW lam z) = 0 :=
    (mul_eq_zero.mp h0).resolve_left hfac.ne'
  have hinj := (mobW_bijOn hl1.ne).injOn
  obtain ⟨hs1, hs2⟩ := curveZ_ne_neg_one (lam := lam) hp1 hp2
  rcases hzero hΦ with he | he
  · exact Or.inl (hinj hz hs1 he)
  · exact Or.inr (hinj hz hs2 (by rw [he, mobW_conj]))

/-- Steps 4-5 (l.160-163): from the `w`-plane Step 3, `D_C ≥ 0` on `ℂ` with zeros only at `z_*`, `z̄_*` (Step 4 at
`z = −1`; Lemma I for `|z| > 1/√λ`). -/
theorem prop_reduction_of_step3 {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hstep3 : ∀ w : ℂ, (0 < lam → Real.sqrt lam ≤ ‖w‖) →
      0 ≤ mobPhi p (gk p lam) (kConst p lam) lam w ∧
      (mobPhi p (gk p lam) (kConst p lam) lam w = 0 →
        w = mobW lam (curveZ p lam (Real.pi / p)) ∨ w = conj (mobW lam (curveZ p lam (Real.pi / p))))) :
    (∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) ∧
    ∀ z : ℂ, critD p (gk p lam) (kConst p lam) lam z = 0 →
      z = curveZ p lam (Real.pi / p) ∨ z = conj (curveZ p lam (Real.pi / p)) := by
  have hnear := reduction_near hp1 hp2 hl1 hstep3
  -- Step 4: near `−1` every point has `‖z‖ < 1/√λ` (as `1/√λ > 1` for `0 < λ < 1`).
  have hball : ∀ᶠ z in 𝓝 (-1 : ℂ), 0 < lam → ‖z‖ ≤ 1 / Real.sqrt lam := by
    by_cases hl0 : 0 < lam
    · have hgt : ‖(-1 : ℂ)‖ < 1 / Real.sqrt lam := by
        rw [norm_neg, norm_one, lt_div_iff₀ (Real.sqrt_pos.mpr hl0), one_mul]
        exact (Real.sqrt_lt' one_pos).mpr (by linarith)
      filter_upwards [(continuous_norm.tendsto (-1 : ℂ)).eventually (gt_mem_nhds hgt)] with z hz _
      exact hz.le
    · exact Eventually.of_forall fun _ h => absurd h hl0
  have h4 : 0 < critD p (gk p lam) (kConst p lam) lam (-1) := by
    refine reduction_step4 hp1 hp2 hl1 (kConst_pos hp1 hp2 hl hl1) ?_
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hz hz1
    exact (hnear z hz1 hz).1
  -- `z ≠ −1` near (by `reduction_near`), `z = −1` (Step 4), `|z| > 1/√λ` (Lemma I).
  have hnear_all : ∀ z : ℂ, (0 < lam → ‖z‖ ≤ 1 / Real.sqrt lam) →
      0 ≤ critD p (gk p lam) (kConst p lam) lam z ∧
      (critD p (gk p lam) (kConst p lam) lam z = 0 →
        z = curveZ p lam (Real.pi / p) ∨ z = conj (curveZ p lam (Real.pi / p))) := by
    intro z hzl
    by_cases hz : z = -1
    · subst hz
      exact ⟨h4.le, fun h0 => absurd h0 h4.ne'⟩
    · exact hnear z hz hzl
  by_cases hl0 : 0 < lam
  · have hfar := (lemma_I (C := gk p lam) (K := kConst p lam) hp1 hl0 hl1
      (zero_le_one.trans (one_le_gk p _))).2.2.2.1 (fun u hu => (hnear_all u (fun _ => hu)).1)
    refine ⟨fun z => ?_, fun z h0 => ?_⟩
    · rcases le_or_gt ‖z‖ (1 / Real.sqrt lam) with hz | hz
      · exact (hnear_all z (fun _ => hz)).1
      · exact (hfar z hz).le
    · rcases le_or_gt ‖z‖ (1 / Real.sqrt lam) with hz | hz
      · exact (hnear_all z (fun _ => hz)).2 h0
      · exact absurd h0 (hfar z hz).ne'
  · exact ⟨fun z => (hnear_all z (fun h => absurd h hl0)).1,
      fun z h0 => (hnear_all z (fun h => absurd h hl0)).2 h0⟩

/-- Proposition (Reduction), l.139-163, from Step 1 (l.143-145); (A2) and `w(θ) → ρ₀` are `sec5_A2_proved` and
`curve_w_tendsto_rho0_proved`. -/
theorem prop_reduction_of_step1 {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hdec : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi))
    (h1 : (∀ θ ∈ Set.Ioo 0 Real.pi, θ ≠ Real.pi / p →
        0 < mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam θ))) ∧
      0 < mobPhi p (gk p lam) (kConst p lam) lam
        ((((1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) : ℝ)) : ℂ)) :
    (∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) ∧
    ∀ z : ℂ, critD p (gk p lam) (kConst p lam) lam z = 0 →
      z = curveZ p lam (Real.pi / p) ∨ z = conj (curveZ p lam (Real.pi / p)) :=
  prop_reduction_of_step3 hp1 hp2 hl hl1
    (reduction_step3 hp1 hp2 hl hl1 hdec (sec5_A2_proved hp1 hp2 hl hl1)
      (curve_w_tendsto_rho0_proved hp1 hp2 hl hl1) h1)

/-- Proposition (Reduction), sec5_sharp_inequality.tex l.139-163: if `K_f` is strictly decreasing on `(0, π)`, then
`D_C ≥ 0` on `ℂ` (`C = GK_p(λ)`, `K` of eq:K), with equality exactly at `z_*` and `z̄_*`. -/
theorem prop_reduction_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hdec : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi)) :
    (∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) ∧
    ∀ z : ℂ, critD p (gk p lam) (kConst p lam) lam z = 0 →
      z = curveZ p lam (Real.pi / p) ∨ z = conj (curveZ p lam (Real.pi / p)) :=
  prop_reduction_of_step1 hp1 hp2 hl hl1 hdec
    (ReductionStep1.reduction_step1_of hp1 hp2 hl hl1 hdec (sec5_A2_proved hp1 hp2 hl hl1).2.2.2.2.2.2.1
      (curve_w_tendsto_rho0_proved hp1 hp2 hl hl1))

end GKSharp.Proofs.Reduction

#print axioms GKSharp.Proofs.Reduction.critD_nonneg_of_step3
#print axioms GKSharp.Proofs.Reduction.prop_reduction_proved
