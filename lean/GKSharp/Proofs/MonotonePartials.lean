/- literal logarithmic partial derivatives, frozen sec5d:26-28.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneLogM

namespace GKSharp

private theorem logsin_of_deriv {f : ℝ → ℝ} {x f' : ℝ} (hd : HasDerivAt f f' x)
    (hn : Real.sin (f x) ≠ 0) :
    HasDerivAt (fun t => Real.log (Real.sin (f t))) (f' * Real.cot (f x)) x := by
  convert hd.sin.log hn using 1
  rw [Real.cot_eq_cos_div_sin]
  ring

set_option maxHeartbeats 1200000 in
theorem mono_log_partials (p a g : ℝ)
    (hma : Real.sin (g - a) ≠ 0) (hpa : Real.sin (g + a) ≠ 0)
    (hmb : Real.sin (g - (p - 1) * a) ≠ 0) (hpb : Real.sin (g + (p - 1) * a) ≠ 0)
    (h2a : Real.sin (2 * a) ≠ 0) (h2b : Real.sin (2 * ((p - 1) * a)) ≠ 0) :
    HasDerivAt (fun x => monoLogL p x g)
      (-(1 - p / 2) * (p - 1) * Real.cot (g - (p - 1) * a) +
        (p / 2) * (p - 1) * Real.cot (g + (p - 1) * a) +
        2 * (p - 1) * Real.cot (2 * a) - (p - 1) * Real.cot (g + a) -
        2 * (p - 1) * Real.cot (2 * ((p - 1) * a))) a ∧
    HasDerivAt (monoLogL p a)
      ((1 - p / 2) * Real.cot (g - (p - 1) * a) +
        (p / 2) * Real.cot (g + (p - 1) * a) - (p - 1) * Real.cot (g + a)) g ∧
    HasDerivAt (fun x => monoLogM p x g)
      (-Real.cot (g - a) + (p - 1) * Real.cot (g + (p - 1) * a) -
        Real.cot (g + a) + (p - 1) * Real.cot (g - (p - 1) * a)) a ∧
    HasDerivAt (monoLogM p a)
      (Real.cot (g - a) + Real.cot (g + (p - 1) * a) -
        Real.cot (g + a) - Real.cot (g - (p - 1) * a)) g := by
  let e := p - 1
  have h_am := logsin_of_deriv ((hasDerivAt_const a g).sub ((hasDerivAt_id a).const_mul e)) hmb
  have h_ap := logsin_of_deriv ((hasDerivAt_const a g).add ((hasDerivAt_id a).const_mul e)) hpb
  have h_2a := logsin_of_deriv ((hasDerivAt_id a).const_mul 2) h2a
  have h_aa := logsin_of_deriv ((hasDerivAt_const a g).add (hasDerivAt_id a)) hpa
  have h_2b := logsin_of_deriv (((hasDerivAt_id a).const_mul e).const_mul 2) h2b
  have h_ma := logsin_of_deriv ((hasDerivAt_const a g).sub (hasDerivAt_id a)) hma
  have h_gm := logsin_of_deriv ((hasDerivAt_id g).sub_const (e * a)) hmb
  have h_gp := logsin_of_deriv ((hasDerivAt_id g).add_const (e * a)) hpb
  have h_ga := logsin_of_deriv ((hasDerivAt_id g).add_const a) hpa
  have h_gma := logsin_of_deriv ((hasDerivAt_id g).sub_const a) hma
  refine ⟨?_,?_,?_,?_⟩
  · convert (((((h_am.const_mul (1 - p / 2)).add (h_ap.const_mul (p / 2))).add
      (h_2a.const_mul (p - 1))).sub (h_aa.const_mul (p - 1))).sub h_2b) using 1 <;>
      first | (funext x; simp [monoLogL,e]) | (dsimp [e]; ring)
  · convert (((((h_gm.const_mul (1 - p / 2)).add (h_gp.const_mul (p / 2))).add
      (hasDerivAt_const g ((p - 1) * Real.log (Real.sin (2 * a))))).sub
      (h_ga.const_mul (p - 1))).sub (hasDerivAt_const g (Real.log (Real.sin (2 * ((p - 1) * a)))))) using 1 <;>
      first | (funext x; simp [monoLogL,e]) | (dsimp [e]; ring)
  · convert (((h_ma.add h_ap).sub h_aa).sub h_am) using 1 <;>
      first | (funext x; simp [monoLogM,Real.log_abs,e]) | (dsimp [e]; ring)
  · convert (((h_gma.add h_gp).sub h_ga).sub h_gm) using 1 <;>
      first | (funext x; simp [monoLogM,Real.log_abs,e]) | (dsimp [e]; ring)

end GKSharp
