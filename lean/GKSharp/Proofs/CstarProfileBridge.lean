/-
CstarProfileBridge.lean — critical curve in logarithmic polar contact coordinates.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.Sec5Lambda
import GKSharp.Proofs.Gamma
import GKSharp.Proofs.Contact
import GKSharp.Proofs.ContactRay
import GKSharp.Proofs.ContactK

namespace GKSharp.Proofs.CstarProfileBridge

open GKSharp ComplexConjugate Filter Topology
open scoped ContDiff

noncomputable def curveY (p lam θ : ℝ) : ℝ := -Real.log (curveR p lam θ)
noncomputable def curveScale (p lam θ : ℝ) : ℝ :=
  curveR p lam θ ^ (p / 2) / ‖1 + curveZ p lam θ‖ ^ p

lemma polar_profile (p C K lam r θ : ℝ) (hr : 0 < r) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    let z : ℂ := (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)
    critD p C K lam z = r ^ (p / 2) *
      (Threshold.gamma p C lam (-Real.log r) θ - K * Real.cos (p / 2 * θ)) := by
  intro z
  let ζ : ℂ := ((r⁻¹ : ℝ) : ℂ) * unitPoint θ
  have hzz : z * ζ = 1 := by
    dsimp [z, ζ, unitPoint]
    rw [Complex.ofReal_inv]
    calc
      _ = ((r : ℂ) * (r : ℂ)⁻¹) *
          (Complex.exp (-(θ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I)) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), ← Complex.exp_add]; simp
  have hphase : -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hn : ‖z‖ = r := by
    dsimp [z]
    rw [hphase, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hA : ‖1 + z‖ = r * ‖1 + ζ‖ := by
    rw [← hn, ← norm_mul]
    congr 1
    rw [mul_add, hzz]
    ring
  have hB : ‖1 + (lam : ℂ) * z‖ = r * ‖(lam : ℂ) + ζ‖ := by
    rw [← hn, ← norm_mul]
    congr 1
    rw [mul_add, hzz]
    ring
  have hγ : Threshold.gamma p C lam (-Real.log r) θ = r ^ (p / 2) * obstacleG p C (lam : ℂ) ζ := by
    change GKSharp.gamma p C (lam : ℂ) (-Real.log r) θ = _
    rw [gamma_radial, Real.exp_neg, Real.exp_log hr, Real.inv_rpow hr.le,
      Real.rpow_neg hr.le, inv_inv]
  have hpow : r ^ (p / 2) * r ^ (p / 2) = r ^ p := by rw [← Real.rpow_add hr]; congr 1; ring
  have hγscale : r ^ (p / 2) * Threshold.gamma p C lam (-Real.log r) θ =
      C ^ p * ‖1 + z‖ ^ p - ‖1 + (lam : ℂ) * z‖ ^ p := by
    rw [hγ, ← mul_assoc, hpow, hA, hB, Real.mul_rpow hr.le (norm_nonneg _),
      Real.mul_rpow hr.le (norm_nonneg _)]
    unfold obstacleG
    ring
  have harg : Complex.arg z = -θ := by
    dsimp [z]
    rw [Complex.arg_real_mul _ hr, hphase, Complex.arg_exp_mul_I]
    exact (toIocMod_eq_self Real.two_pi_pos).mpr ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hrep : reQPow z (p / 2) = r ^ (p / 2) * Real.cos (p / 2 * θ) := by
    rw [reQPow, hn, harg, mul_neg, Real.cos_neg]
  unfold critD
  rw [← hγscale, hrep]
  ring

lemma curve_profile {p C K lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    mobPhi p C K lam (mobW lam (curveZ p lam θ)) / (1 - lam) ^ p =
      curveScale p lam θ *
        (Threshold.gamma p C lam (curveY p lam θ) θ - K * Real.cos (p / 2 * θ)) := by
  have hpolar := polar_profile p C K lam (curveR p lam θ) θ
    (curve_root_formula hp1 hp2 hθ0 hθ hl hl1).2.2.1 hθ0 hθ
  change critD p C K lam (curveZ p lam θ) = _ at hpolar
  rw [(GKSharp.Proofs.Sec5Lambda.sec5_Lambda_proved hp1 hp2 hl hl1 hθ0 hθ).2, hpolar]
  unfold curveScale curveY
  ring

lemma contact_height {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) : curveY p lam (Real.pi / p) = Threshold.yContact p lam := by
  have hcos := GKSharp.cos_theta_negative hp1 hp2
  have hcr : Threshold.rContact p lam = contactRadius p lam := by
    rw [(contact_gk_radius p lam hp1 hp2 ⟨hl, hl1⟩).1]
    unfold contactRadius contactKappa Threshold.cs
    rw [abs_of_neg hcos]
    ring
  obtain ⟨hθ0, hθ, _, _⟩ := theta0_bounds hp1 hp2
  have hR := (curve_root_formula hp1 hp2 hθ0 hθ hl.le hl1).2.2.1
  have hn : ‖curveZ p lam (Real.pi / p)‖ = curveR p lam (Real.pi / p) := by
    unfold curveZ
    rw [show -((Real.pi / p : ℝ) : ℂ) * Complex.I = ((-(Real.pi / p) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hr := (contact_point hp1 hp2 hl.le hl1).2
  rw [hn, ← hcr] at hr
  unfold curveY
  rw [hr, one_div, Real.log_inv, neg_neg]
  rfl

lemma smooth_scale {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    ContDiffAt ℝ ω (curveY p lam) θ ∧ ContDiffAt ℝ ∞ (curveScale p lam) θ ∧ 0 < curveScale p lam θ := by
  have hR0 := (curve_root_formula hp1 hp2 hθ0 hθ hl hl1).2.2.1
  have hden : 1 + curveZ p lam θ ≠ 0 := polar_one_add_ne_zero hR0 hθ0 hθ
  have hR : ContDiffAt ℝ ω (curveR p lam) θ :=
    (curve_root_analytic hp1 hp2 hl hl1 hθ0 hθ).contDiffAt
  have hRc : ContDiffAt ℝ ∞ (fun x => (curveR p lam x : ℂ)) θ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp θ (hR.of_le (by simp))
  have hi : ContDiffAt ℝ ∞ (fun x : ℝ => (x : ℂ)) θ := Complex.ofRealCLM.contDiff.contDiffAt
  have hz : ContDiffAt ℝ ∞ (curveZ p lam) θ := hRc.mul (hi.neg.mul contDiffAt_const).cexp
  have hn : ContDiffAt ℝ ∞ (fun x => ‖1 + curveZ p lam x‖) θ :=
    (contDiffAt_const.add hz).norm ℂ hden
  have hn0 : 0 < ‖1 + curveZ p lam θ‖ := norm_pos_iff.mpr hden
  refine ⟨(hR.log hR0.ne').neg, ?_, div_pos (Real.rpow_pos_of_pos hR0 _) (Real.rpow_pos_of_pos hn0 _)⟩
  exact ((hR.of_le (by simp)).rpow_const_of_ne hR0.ne').div
    (hn.rpow_const_of_ne hn0.ne') (ne_of_gt (Real.rpow_pos_of_pos hn0 _))

end GKSharp.Proofs.CstarProfileBridge
