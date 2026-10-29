/- curve regularity and logarithmic level differentiation.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneKfLog
import GKSharp.Proofs.MonotonePartials

namespace GKSharp

theorem curveGamma_differentiableAt {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    DifferentiableAt ℝ (curveGamma p lam) θ := by
  have hb0 : 0 < (p - 1) * (θ / 2) := mul_pos (by linarith) (half_pos hθ0)
  have hbpi : (p - 1) * (θ / 2) < Real.pi / 2 := by nlinarith
  have hc : Real.cos ((p - 1) * (θ / 2)) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hbpi⟩).ne'
  have hlin : DifferentiableAt ℝ (fun x : ℝ => (p - 1) * (x / 2)) θ := by fun_prop
  have hR := (curve_root_analytic hp1 hp2 hl.le hl1 hθ0 hθ).differentiableAt
  have hr1 := (curve_root_unique hp1 hp2 hθ0 hθ hl hl1).2.2.2.2.2.2.1
  have hden : 1 - curveR p lam θ ≠ 0 := by linarith
  have htan := ((Real.hasDerivAt_tan hc).comp θ hlin.hasDerivAt).differentiableAt
  have harg := (htan.mul ((differentiableAt_const (c := (1 : ℝ))).add hR)).div
    ((differentiableAt_const (c := (1 : ℝ))).sub hR) hden
  exact harg.arctan

private theorem logsin_curve {f : ℝ → ℝ} {a d : ℝ} (hd : HasDerivAt f d a)
    (hn : Real.sin (f a) ≠ 0) :
    HasDerivAt (fun t => Real.log (Real.sin (f t))) (d * Real.cot (f a)) a := by
  convert hd.sin.log hn using 1
  rw [Real.cot_eq_cos_div_sin]
  ring

set_option maxHeartbeats 800000 in
theorem monoL_along {G : ℝ → ℝ} {d p a : ℝ} (hG : HasDerivAt G d a)
    (hmb : Real.sin (G a - (p - 1) * a) ≠ 0) (hpb : Real.sin (G a + (p - 1) * a) ≠ 0)
    (hpa : Real.sin (G a + a) ≠ 0) (h2a : Real.sin (2 * a) ≠ 0)
    (h2b : Real.sin (2 * ((p - 1) * a)) ≠ 0) :
    HasDerivAt (fun x => monoLogL p x (G x))
      ((1 - p / 2) * (d - (p - 1)) * Real.cot (G a - (p - 1) * a) +
        (p / 2) * (d + (p - 1)) * Real.cot (G a + (p - 1) * a) +
        2 * (p - 1) * Real.cot (2 * a) - (p - 1) * (d + 1) * Real.cot (G a + a) -
        2 * (p - 1) * Real.cot (2 * ((p - 1) * a))) a := by
  have hm := logsin_curve (hG.sub ((hasDerivAt_id a).const_mul (p - 1))) hmb
  have hp := logsin_curve (hG.add ((hasDerivAt_id a).const_mul (p - 1))) hpb
  have htwo := logsin_curve ((hasDerivAt_id a).const_mul 2) h2a
  have ha := logsin_curve (hG.add (hasDerivAt_id a)) hpa
  have htwob := logsin_curve (((hasDerivAt_id a).const_mul (p - 1)).const_mul 2) h2b
  convert (((((hm.const_mul (1 - p / 2)).add (hp.const_mul (p / 2))).add
    (htwo.const_mul (p - 1))).sub (ha.const_mul (p - 1))).sub htwob) using 1 <;>
    first | (funext x; simp [monoLogL]) | (simp only [Pi.add_apply,Pi.sub_apply,id_eq,mul_one] <;> ring)

set_option maxHeartbeats 800000 in
theorem monoM_along {G : ℝ → ℝ} {d p a : ℝ} (hG : HasDerivAt G d a)
    (hma : Real.sin (G a - a) ≠ 0) (hpa : Real.sin (G a + a) ≠ 0)
    (hmb : Real.sin (G a - (p - 1) * a) ≠ 0) (hpb : Real.sin (G a + (p - 1) * a) ≠ 0) :
    HasDerivAt (fun x => monoLogM p x (G x))
      ((d - 1) * Real.cot (G a - a) + (d + (p - 1)) * Real.cot (G a + (p - 1) * a) -
        (d + 1) * Real.cot (G a + a) - (d - (p - 1)) * Real.cot (G a - (p - 1) * a)) a := by
  have hma' := logsin_curve (hG.sub (hasDerivAt_id a)) hma
  have hpa' := logsin_curve (hG.add (hasDerivAt_id a)) hpa
  have hmb' := logsin_curve (hG.sub ((hasDerivAt_id a).const_mul (p - 1))) hmb
  have hpb' := logsin_curve (hG.add ((hasDerivAt_id a).const_mul (p - 1))) hpb
  convert (((hma'.add hpb').sub hpa').sub hmb') using 1 <;>
    first | (funext x; simp [monoLogM,Real.log_abs]) | (simp only [Pi.add_apply,Pi.sub_apply,id_eq,mul_one] <;> ring)

end GKSharp
