/-
CriticalClassification.lean — all interior circle critical points, project019 Section5.1.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.InverseCritical
import GKSharp.Proofs.LemmaI

namespace GKSharp.Proofs.CriticalClassification

open GKSharp ComplexConjugate
open GKSharp.Proofs.EllipseCalculus GKSharp.Proofs.InverseCritical

lemma polar_arg_Q {lam r θ : ℝ} (hl1 : lam < 1) (hr : 0 < r) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    Complex.arg (mobQ lam (mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)))) = θ := by
  have hp := GKSharp.polar_one_add_ne_zero hr hθ0 hθ
  have hz : (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) ≠ -1 := by
    intro hh; apply hp; rw [hh]; ring
  have hc : 0 < (1 - lam) ^ 2 / ‖1 + (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)‖ ^ 2 := by
    have hn := norm_pos_iff.mpr hp
    have hl := sub_pos.mpr hl1
    positivity
  rw [GKSharp.mobQ_mobW lam hz, Complex.arg_real_mul _ hc]
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_neg,
    Complex.conj_ofReal, Complex.conj_I,
    show -(θ : ℂ) * -Complex.I = (θ : ℂ) * Complex.I by ring,
    Complex.arg_real_mul _ hr, Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  constructor <;> linarith [Real.pi_pos]

lemma critical_at_polar {p lam ρ φ r θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hρ : 0 < ρ) (hφ0 : 0 < φ) (hφ : φ < Real.pi)
    (hr : 0 < r) (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hw : (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) =
      mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I))) :
    deriv (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ = 0 ↔
      curveD p lam θ r = 0 := by
  let w : ℂ := (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
  have hQi := (eq_5_3_proved hp1 hp2 hl hl1 hρ hφ0 hφ).1
  change 0 < (mobQ lam w).im at hQi
  have hQne : mobQ lam w ≠ 0 := by intro hh; simpa [hh] using hQi
  have hcoef : -(p / 2) * ‖mobQ lam w‖ ^ (p / 2 - 1) ≠ 0 := by
    apply mul_ne_zero
    · linarith
    · exact ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hQne) _)
  have ha : Complex.arg (mobQ lam w) = θ := by
    change Complex.arg (mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))) = θ
    rw [hw]
    exact polar_arg_Q hl1 hr hθ0 hθ
  have hd := (eq_5_3_proved hp1 hp2 hl hl1 hρ hφ0 hφ).2.2.deriv
  change deriv (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ =
    -(p / 2) * ‖mobQ lam w‖ ^ (p / 2 - 1) * (conj (curveV p lam (Complex.arg (mobQ lam w))) * w).im at hd
  rw [hd, mul_eq_zero]
  simp only [hcoef, false_or]
  rw [ha]
  change (conj (curveV p lam θ) * ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))).im = 0 ↔ _
  rw [hw, GKSharp.cross_curveD, div_eq_zero_iff, mul_eq_zero]
  have hA : ‖1 + (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)‖ ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr (GKSharp.polar_one_add_ne_zero hr hθ0 hθ)))
  simp only [hA, ne_of_gt (sub_pos.mpr hl1), false_or, or_false]

lemma root_options {p lam θ r : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) (hr : 0 < r) (hroot : curveD p lam θ r = 0) :
    r = curveR p lam θ ∨ 0 < lam ∧ r = 1 / (lam * curveR p lam θ) := by
  have hDR := (GKSharp.curve_root_formula hp1 hp2 hθ0 hθ hl hl1).2.2.2.2
  obtain ⟨hs1, hs12, _⟩ := GKSharp.curve_sines hp1 hp2 hθ0 hθ
  rcases lt_trichotomy lam 0 with hneg | heq | hpos
  · exact Or.inl ((GKSharp.curve_root_product hp1 hp2 hθ0 hθ hl hl1 hneg.ne).2.1 hneg r hr hroot)
  · have hd := GKSharp.curveD_sub p lam θ r (curveR p lam θ)
    rw [hroot, hDR] at hd
    have hh : (r - curveR p lam θ) * Real.sin (p / 2 * θ) = 0 := by simpa [heq] using hd.symm
    exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (ne_of_gt (lt_trans hs1 hs12))))
  · have hf := (GKSharp.curve_root_product hp1 hp2 hθ0 hθ hl hl1 hpos.ne').1 r
    rw [hroot] at hf
    have hh : (r - curveR p lam θ) * (r - 1 / (lam * curveR p lam θ)) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (mul_ne_zero (neg_ne_zero.mpr hpos.ne') hs1.ne')
      simpa only [mul_assoc] using hf.symm
    rcases mul_eq_zero.mp hh with hh | hh
    · exact Or.inl (sub_eq_zero.mp hh)
    · exact Or.inr ⟨hpos, sub_eq_zero.mp hh⟩

lemma curve_inversion_map {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    mobW lam (1 / ((lam : ℂ) * conj (curveZ p lam θ))) =
      (lam : ℂ) / conj (mobW lam (curveZ p lam θ)) := by
  have hR := (GKSharp.curve_root_formula hp1 hp2 hθ0 hθ (by linarith) hl1).2.2.1
  have hz : curveZ p lam θ ≠ 0 := by
    unfold curveZ
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
  have hp : (1 : ℂ) + curveZ p lam θ ≠ 0 := GKSharp.polar_one_add_ne_zero hR hθ0 hθ
  have hz1 : curveZ p lam θ ≠ -1 := by intro hh; apply hp; rw [hh]; ring
  have hnum : (1 : ℂ) + (lam : ℂ) * curveZ p lam θ ≠ 0 := by
    intro hh
    have hi := congrArg Complex.im hh
    rw [Complex.add_im, Complex.one_im, Complex.im_ofReal_mul, curveZ,
      (GKSharp.polar_re_im (curveR p lam θ) θ).2, Complex.zero_im] at hi
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
    have hn := mul_pos (mul_pos hl0 hR) hs
    nlinarith
  exact (GKSharp.lemma_I (p := p) (C := 0) (K := 0) hp1 hl0 hl1 le_rfl).2.2.2.2 _ hz hz1 hnum

theorem sec5_critical_points_proved {p lam ρ φ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hρ : 0 < ρ) (hφ0 : 0 < φ) (hφ : φ < Real.pi) :
    deriv (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ = 0 ↔
      (∃ θ ∈ Set.Ioo 0 Real.pi, (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = mobW lam (curveZ p lam θ)) ∨
      (0 < lam ∧ ∃ θ ∈ Set.Ioo 0 Real.pi,
        (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = (lam : ℂ) / conj (mobW lam (curveZ p lam θ))) := by
  constructor
  · intro hcrit
    let w : ℂ := (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
    let θ := Complex.arg (mobQ lam w)
    let z : ℂ := (1 - w) / (w - lam)
    have hwi : 0 < w.im := by
      dsimp [w]
      rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
      exact mul_pos hρ (Real.sin_pos_of_pos_of_lt_pi hφ0 hφ)
    have hwlam : w ≠ (lam : ℂ) := by intro hh; have hi := congrArg Complex.im hh; simp at hi; linarith
    have hw1 : w ≠ 1 := by intro hh; simpa [hh] using hwi
    have hz0 : z ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hw1)) (sub_ne_zero.mpr hwlam)
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    obtain ⟨_, hmap⟩ := inverse_mobW hl1 hwlam
    change mobW lam z = w at hmap
    have hi := (eq_5_3_proved hp1 hp2 hl hl1 hρ hφ0 hφ).1
    obtain ⟨hθ0, hθ⟩ := arg_range hi
    change 0 < θ at hθ0
    change θ < Real.pi at hθ
    obtain ⟨hpolar, _, _, hzero⟩ := eq_5_3_second_proved hp1 hp2 hl hl1 hρ hφ0 hφ
    change z = (‖z‖ : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) at hpolar
    have hDr : curveD p lam θ ‖z‖ = 0 := hzero.mp hcrit
    rcases root_options hp1 hp2 hl hl1 hθ0 hθ hr hDr with hbase | ⟨hpos, hinv⟩
    · left
      refine ⟨θ, ⟨hθ0, hθ⟩, ?_⟩
      change w = mobW lam (curveZ p lam θ)
      rw [← hmap, hpolar, hbase]
      rfl
    · right
      refine ⟨hpos, θ, ⟨hθ0, hθ⟩, ?_⟩
      change w = (lam : ℂ) / conj (mobW lam (curveZ p lam θ))
      have hprod := (GKSharp.curve_root_product hp1 hp2 hθ0 hθ hl hl1 hpos.ne').2.2 hpos
      have hzI : z = 1 / ((lam : ℂ) * conj (curveZ p lam θ)) := by
        rw [hpolar, hinv, ← hprod.2]
      rw [← hmap, hzI]
      exact curve_inversion_map hp1 hp2 hpos hl1 hθ0 hθ
  · rintro (⟨θ, ⟨hθ0, hθ⟩, hw⟩ | ⟨hpos, θ, ⟨hθ0, hθ⟩, hw⟩)
    · obtain ⟨_, _, hR, _, hD⟩ := GKSharp.curve_root_formula hp1 hp2 hθ0 hθ hl hl1
      exact (critical_at_polar hp1 hp2 hl hl1 hρ hφ0 hφ hR hθ0 hθ hw).mpr hD
    · have hR := (GKSharp.curve_root_formula hp1 hp2 hθ0 hθ hl hl1).2.2.1
      have hr : 0 < 1 / (lam * curveR p lam θ) := one_div_pos.mpr (mul_pos hpos hR)
      have hprod := (GKSharp.curve_root_product hp1 hp2 hθ0 hθ hl hl1 hpos.ne').2.2 hpos
      have hwm : (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) =
          mobW lam (((1 / (lam * curveR p lam θ) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)) := by
        calc
          _ = (lam : ℂ) / conj (mobW lam (curveZ p lam θ)) := hw
          _ = mobW lam (1 / ((lam : ℂ) * conj (curveZ p lam θ))) :=
            (curve_inversion_map hp1 hp2 hpos hl1 hθ0 hθ).symm
          _ = _ := congrArg (mobW lam) hprod.2
      exact (critical_at_polar hp1 hp2 hl hl1 hρ hφ0 hφ hr hθ0 hθ hwm).mpr hprod.1

end GKSharp.Proofs.CriticalClassification

#print axioms GKSharp.Proofs.CriticalClassification.sec5_critical_points_proved

