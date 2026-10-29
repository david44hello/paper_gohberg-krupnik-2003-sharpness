/- Theorem C* (sec5e_cstar.tex l.22, short v0.70): "The real segment [√λ, ρ₀] is covered by h ≥ 0 directly":
Φ(ρ) ≥ 0 for real ρ ∈ [√λ, ρ₀]. No cited input.
Copyright (C) Dave Goel 2026--now.

  The text's step. For 0 < λ < 1: λ < √λ ≤ ρ ≤ ρ₀ < 1, so z = (1 - ρ)/(ρ - λ) > 0 is a point of the positive axis with
  w(z) = (1 + λz)/(1 + z) = ρ (the positive z-axis maps onto the real segment (λ, 1)). D_C(z) ≥ 0 by the positive-axis
  lemma (h ≥ 0, CstarCurve.critD_pos_axis_nonneg), and D_C(z) = |1+z|^p/(1-λ)^p Φ(w(z)) (critD_eq_mobPhi). -/
import GKSharp.Proofs.CstarCurve

open Filter Topology Set

namespace GKSharp

namespace CstarSegment

/-- `h ≥ 0` gives `Φ(w(r)) ≥ 0` at every point `r > 0` of the positive axis. -/
theorem mobPhi_mobW_pos_axis_nonneg {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl1 : lam < 1)
    (hh : kConst p lam ≤ obstacle p (gk p lam) (lam : ℂ) 0) {r : ℝ} (hr : 0 < r) :
    0 ≤ mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (r : ℂ)) := by
  have hz : (r : ℂ) ≠ -1 := fun h => by
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.one_re] at this
    linarith
  have hD := CstarCurve.critD_pos_axis_nonneg (KK := kConst p lam) (by linarith)
    (CstarCurve.gk_gt_max_real hp1 hp2 hl1) hh hr
  rw [critD_eq_mobPhi p _ _ hl1 hz] at hD
  have hpos : 0 < ‖1 + (r : ℂ)‖ ^ p / (1 - lam) ^ p :=
    div_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 (one_add_ne_zero hz)) p)
      (Real.rpow_pos_of_pos (by linarith) p)
  exact le_of_mul_le_mul_left (by rwa [mul_zero]) hpos

/-- The positive axis covers the real segment `(λ, 1)`: `w((1 - ρ)/(ρ - λ)) = ρ`. -/
theorem mobW_inverse_real {lam ρ : ℝ} (hl1 : lam < 1) (hρl : lam < ρ) :
    mobW lam (((1 - ρ) / (ρ - lam) : ℝ) : ℂ) = (ρ : ℂ) := by
  have h1 : (ρ : ℂ) - lam ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact Complex.ofReal_ne_zero.mpr (by linarith)
  have h2 : (1 : ℂ) - lam ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]; exact Complex.ofReal_ne_zero.mpr (by linarith)
  unfold mobW
  push_cast
  rw [div_eq_iff (by
    rw [show (1 : ℂ) + (1 - ρ) / (ρ - lam) = (1 - lam) / (ρ - lam) by field_simp; ring]
    exact div_ne_zero h2 h1)]
  field_simp
  ring

/-- **sec5e_cstar.tex l.22** (contract helper cstar_real_segment): `h ≥ 0` gives `Φ(ρ) ≥ 0` on the real segment
`[√λ, ρ₀]` (`0 ≤ ρ`; `√λ ≤ ρ` when `λ > 0`). -/
theorem cstar_real_segment_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hh : kConst p lam ≤ obstacle p (gk p lam) lam 0) :
    ∀ ρ : ℝ, 0 ≤ ρ → (0 < lam → Real.sqrt lam ≤ ρ) →
      ρ ≤ (1 + lam * curveRoot lam (1 - p / 2) (p / 2)) / (1 + curveRoot lam (1 - p / 2) (p / 2)) →
      0 ≤ mobPhi p (gk p lam) (kConst p lam) lam (ρ : ℂ) := by
  intro ρ _ hsq hρ0
  have hr0 : 0 < curveRoot lam (1 - p / 2) (p / 2) := curveRoot_pos (by linarith) hl1 (by linarith) (by linarith)
  have hρ1 : ρ < 1 := by
    refine hρ0.trans_lt ((div_lt_one (by linarith)).mpr ?_)
    nlinarith
  have hlsq : lam < Real.sqrt lam := (Real.lt_sqrt hl0.le).mpr (by nlinarith)
  have hρl : lam < ρ := hlsq.trans_le (hsq hl0)
  have hz : 0 < (1 - ρ) / (ρ - lam) := div_pos (by linarith) (by linarith)
  rw [← mobW_inverse_real hl1 hρl]
  exact mobPhi_mobW_pos_axis_nonneg hp1 hp2 hl1 hh hz

end CstarSegment

end GKSharp
