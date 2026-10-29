/-
SharpA3.lean — project019 Section5 (A3), geometric and calculus assembly.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.CriticalClassification
import GKSharp.Proofs.SharpA3Calculus
import GKSharp.Proofs.CircleExtrema
import GKSharp.Proofs.QEnds
import GKSharp.Defs.PolarProfile

namespace GKSharp.Proofs.SharpA3

open GKSharp ComplexConjugate Set Filter Topology
open GKSharp.Proofs.EllipseCalculus GKSharp.Proofs.InverseCritical
open GKSharp.Proofs.CriticalClassification GKSharp.Proofs.SharpA3Calculus

noncomputable abbrev rhoCurve (p lam θ : ℝ) : ℝ := ‖mobW lam (curveZ p lam θ)‖

lemma curve_upper {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hθ : θ ∈ Ioo 0 Real.pi) :
    0 < (mobW lam (curveZ p lam θ)).im := by
  have hR := (curve_root_formula hp1 hp2 hθ.1 hθ.2 hl hl1).2.2.1
  have hden : 0 < Complex.normSq (1 + curveZ p lam θ) :=
    Complex.normSq_pos.mpr (polar_one_add_ne_zero hR hθ.1 hθ.2)
  rw [mobW_im, curveZ, (polar_re_im (curveR p lam θ) θ).2]
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  change 0 < -((1 - lam) * -(curveR p lam θ * Real.sin θ)) /
    Complex.normSq (1 + curveZ p lam θ)
  exact div_pos (by nlinarith [mul_pos (sub_pos.mpr hl1) (mul_pos hR hs)]) hden

lemma strict_above_left_limit {g : ℝ → ℝ} {b v : ℝ}
    (hmono : StrictMonoOn g (Ioo 0 b)) (hlim : Tendsto g (𝓝[>] 0) (𝓝 v))
    {θ : ℝ} (hθ : θ ∈ Ioo 0 b) : v < g θ := by
  have hm : θ / 2 ∈ Ioo 0 b := ⟨by linarith [hθ.1], by linarith [hθ.1, hθ.2]⟩
  have hle : v ≤ g (θ / 2) := by
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT (by linarith [hθ.1] : (0 : ℝ) < θ / 2)] with x hx
    exact (hmono ⟨hx.1, hx.2.trans hm.2⟩ hm hx.2).le
  exact hle.trans_lt (hmono hm hθ (by linarith [hθ.1]))

/-- The A1/A2 inputs here are explicit pending dependencies, not a public proof of A3. -/
theorem sec5_A3_of_A1_A2 {p lam ρ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hρ : 0 < ρ)
    (hA1 : Set.Subsingleton {φ | φ ∈ Set.Ioo 0 Real.pi ∧ deriv (fun x => fRho p lam ρ x) φ = 0})
    (hA2 :
      let r0 := curveRoot lam (1 - p / 2) (p / 2)
      let ρ0 := (1 + lam * r0) / (1 + r0)
      ContinuousOn (rhoCurve p lam) (Set.Ioo 0 Real.pi) ∧ StrictMonoOn (rhoCurve p lam) (Set.Ioo 0 Real.pi) ∧
      Tendsto (rhoCurve p lam) (𝓝[<] Real.pi) atTop ∧ Tendsto (rhoCurve p lam) (𝓝[>] 0) (𝓝 ρ0) ∧
      0 ≤ ρ0 ∧ ρ0 < 1 ∧
      (∀ θ ∈ Set.Ioo 0 Real.pi, 0 < deriv (rhoCurve p lam) θ) ∧
      (0 < lam → (1 + lam) / 2 ≤ ρ0 ∧ Real.sqrt lam < (1 + lam) / 2)) :
    let r0 := curveRoot lam (1 - p / 2) (p / 2)
    let ρ0 := (1 + lam * r0) / (1 + r0)
    (ρ0 < ρ → ∃ φc ∈ Set.Ioo 0 Real.pi, ∃ θ ∈ Set.Ioo 0 Real.pi,
      rhoCurve p lam θ = ρ ∧ (ρ : ℂ) * Complex.exp ((φc : ℂ) * Complex.I) = mobW lam (curveZ p lam θ) ∧
      (∀ φ ∈ Set.Ioo 0 φc, 0 < deriv (fun x => fRho p lam ρ x) φ) ∧
      (∀ φ ∈ Set.Ioo φc Real.pi, deriv (fun x => fRho p lam ρ x) φ < 0) ∧
      ∀ φ ∈ Set.Icc 0 Real.pi, φ ≠ φc → fRho p lam ρ φ < fRho p lam ρ φc) ∧
    (ρ ≤ ρ0 → (0 < lam → Real.sqrt lam ≤ ρ) →
      (MonotoneOn (fun x => fRho p lam ρ x) (Set.Icc 0 Real.pi) ∨
        AntitoneOn (fun x => fRho p lam ρ x) (Set.Icc 0 Real.pi)) ∧
      ∀ φ ∈ Set.Icc 0 Real.pi, fRho p lam ρ φ ≤ fRho p lam ρ 0) := by
  intro r0 ρ0
  obtain ⟨hcontR, hmonoR, hlimpi, hlim0, hρ00, hρ01, hderivR, hposlam⟩ := hA2
  change Tendsto (rhoCurve p lam) (𝓝[>] 0) (𝓝 ρ0) at hlim0
  have hlow (θ : ℝ) (hθ : θ ∈ Ioo 0 Real.pi) : ρ0 < rhoCurve p lam θ :=
    strict_above_left_limit hmonoR hlim0 hθ
  have hdiff (φ : ℝ) (hφ : φ ∈ Ioo 0 Real.pi) : DifferentiableAt ℝ (fRho p lam ρ) φ :=
    (eq_5_3_proved hp1 hp2 hl hl1 hρ hφ.1 hφ.2).2.2.differentiableAt
  have hcont : ContinuousOn (fRho p lam ρ) (Icc 0 Real.pi) := by
    have hpolar : Continuous (fun φ : ℝ => mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))) := by
      unfold mobQ
      fun_prop
    exact ((GKSharp.Proofs.CircleExtrema.continuous_reQPow (by linarith : 0 < p / 2)).comp hpolar).continuousOn
  have hnpolar (φ : ℝ) : ‖(ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ = ρ := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, Complex.norm_exp_ofReal_mul_I]
  constructor
  · intro hρbig
    have hstart : 𝓝[>] (0 : ℝ) ≤ 𝓟 (Ioo 0 Real.pi) := by
      exact le_principal_iff.mpr (Ioo_mem_nhdsGT Real.pi_pos)
    have hfinish : 𝓝[<] Real.pi ≤ 𝓟 (Ioo (0 : ℝ) Real.pi) := by
      exact le_principal_iff.mpr (Ioo_mem_nhdsLT Real.pi_pos)
    obtain ⟨θ, hθ, hnorm⟩ := isPreconnected_Ioo.intermediate_value_Ioi
      hstart hfinish hcontR hlim0 hlimpi hρbig
    let w := mobW lam (curveZ p lam θ)
    have hwi : 0 < w.im := curve_upper hp1 hp2 hl hl1 hθ
    have hφ := arg_range hwi
    have heq : (ρ : ℂ) * Complex.exp (((Complex.arg w) : ℂ) * Complex.I) = w := by
      simpa only [show ‖w‖ = ρ from hnorm] using Complex.norm_mul_exp_arg_mul_I w
    have hcrit : deriv (fRho p lam ρ) (Complex.arg w) = 0 :=
      (sec5_critical_points_proved hp1 hp2 hl hl1 hρ hφ.1 hφ.2).mpr (Or.inl ⟨θ, hθ, heq⟩)
    obtain ⟨hdd, hnegative⟩ := GKSharp.Proofs.CriticalMaximum.eq_5_6_proved hp1 hp2 hl hl1 hρ hφ.1 hφ.2 hcrit
    have hshape := shape_of_unique_critical hφ hcont hdiff hcrit
      (by rw [hdd.deriv]; exact hnegative)
      (fun x hx hz => hA1 ⟨hx, hz⟩ ⟨hφ, hcrit⟩)
    exact ⟨Complex.arg w, hφ, θ, hθ, hnorm, heq, hshape⟩
  · intro hρsmall hρsqrt
    have hno (φ : ℝ) (hφ : φ ∈ Ioo 0 Real.pi) : deriv (fRho p lam ρ) φ ≠ 0 := by
      intro hcrit
      rcases (sec5_critical_points_proved hp1 hp2 hl hl1 hρ hφ.1 hφ.2).mp hcrit with
        ⟨θ, hθ, heq⟩ | ⟨hpos, θ, hθ, heq⟩
      · have hn := congrArg norm heq
        rw [hnpolar] at hn
        have hlower := hlow θ hθ
        change ρ = rhoCurve p lam θ at hn
        linarith
      · have hn := congrArg norm heq
        rw [hnpolar, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, Complex.norm_conj] at hn
        change ρ = lam / rhoCurve p lam θ at hn
        have hbound := hposlam hpos
        change (1 + lam) / 2 ≤ ρ0 ∧ Real.sqrt lam < (1 + lam) / 2 at hbound
        have hlarge : Real.sqrt lam < rhoCurve p lam θ :=
          (hbound.2.trans_le hbound.1).trans (hlow θ hθ)
        have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hpos
        have hr : 0 < rhoCurve p lam θ := hs.trans hlarge
        have hmul : ρ * rhoCurve p lam θ = lam := (eq_div_iff hr.ne').mp hn
        have hsquare := Real.sq_sqrt hpos.le
        have hprod := mul_lt_mul_of_pos_left hlarge hs
        have hprod' := mul_le_mul_of_nonneg_right (hρsqrt hpos) hr.le
        nlinarith
    have hend := (GKSharp.sec5_Q_ends_proved hp1 hp2 hl hl1 hρ).2.2.2.2
    exact shape_of_no_critical Real.pi_pos.le hcont hdiff hno hend

end GKSharp.Proofs.SharpA3

#print axioms GKSharp.Proofs.SharpA3.sec5_A3_of_A1_A2
