/- exact angular derivative of the real-ratio obstacle.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.Gamma

namespace GKSharp
open Real

/-- sec2_obstacle.tex:139. Classical derivative at every point with the two printed bases positive. -/
theorem gamma_derivative_real (p C lam y t : ℝ)
    (hA : 0 < 2 * cosh y + 2 * cos t)
    (hB : 0 < exp y + lam ^ 2 * exp (-y) + 2 * lam * cos t) :
    deriv (gamma p C (lam : ℂ) y) t =
      -2 * (p / 2) * sin t *
        (C ^ p * (2 * cosh y + 2 * cos t) ^ (p / 2 - 1) -
          lam * (exp y + lam ^ 2 * exp (-y) + 2 * lam * cos t) ^ (p / 2 - 1)) := by
  have dA : HasDerivAt (fun x : ℝ => 2 * cosh y + 2 * cos x) (-2 * sin t) t := by
    convert (hasDerivAt_const t (2 * cosh y)).add ((Real.hasDerivAt_cos t).const_mul 2) using 1 <;> ring
  have dB : HasDerivAt (fun x : ℝ => exp y + lam ^ 2 * exp (-y) + 2 * lam * cos x)
      (-2 * lam * sin t) t := by
    convert (hasDerivAt_const t (exp y + lam ^ 2 * exp (-y))).add
      ((Real.hasDerivAt_cos t).const_mul (2 * lam)) using 1 <;> ring
  have d := ((dA.rpow_const (p := p / 2) (Or.inl hA.ne')).const_mul (C ^ p)).sub
    (dB.rpow_const (p := p / 2) (Or.inl hB.ne'))
  have he : gamma p C (lam : ℂ) y = fun x : ℝ =>
      C ^ p * (2 * cosh y + 2 * cos x) ^ (p / 2) -
        (exp y + lam ^ 2 * exp (-y) + 2 * lam * cos x) ^ (p / 2) :=
    funext (gamma_real p C lam y)
  rw [he]
  calc
    _ = C ^ p * (-2 * sin t * (p / 2) * (2 * cosh y + 2 * cos t) ^ (p / 2 - 1)) -
        (-2 * lam * sin t * (p / 2) *
          (exp y + lam ^ 2 * exp (-y) + 2 * lam * cos t) ^ (p / 2 - 1)) := d.deriv
    _ = _ := by ring

end GKSharp
