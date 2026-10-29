/- N11, the real-line multiplier norm is at most each circle norm (norm_correspondence.tex l.52-55).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ReverseNormFinal
import GKSharp.Proofs.SchwartzPencilPeriodization
import GKSharp.Proofs.CircleMapNorm

open GKSharp.RealLineFourier

namespace GKSharp.Proofs.ReverseNormCircle

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- The reverse bound for a circle convention `S` that intertwines periodizations like the pencil: if `functionNorm S`
is nonnegative and dominates `S` pointwise, then `‖T_ℝ‖ ≤ functionNorm S`. -/
theorem reverse_bound_of_functionNorm (hp : 1 < p) (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β)
    (S : LpT p → LpT p) (hK : 0 ≤ functionNorm S) (hS : ∀ u : LpT p, ‖S u‖ ≤ functionNorm S * ‖u‖)
    (hinter : ∀ (f g : SchwartzMap ℝ ℂ), HasCompactSupport (paperFourier f) →
      0 ∉ tsupport (paperFourier f) →
      (∀ ξ : ℝ, paperFourier g ξ = (if 0 < ξ then α else β) * paperFourier f ξ) →
      ∀ (N : ℕ), 0 < N → ∀ F G : C(Circ, ℂ),
        (∀ t : ℝ, F (t : Circ) = periodized f N t) →
        (∀ t : ℝ, G (t : Circ) = periodized g N t) →
        S (DensityLp.toLpT p F) = DensityLp.toLpT p G) :
    ‖T.map‖ ≤ functionNorm S :=
  ReverseNorm.opNorm_le_circle_bound SchwartzPencilFinal.density_proved
    (ReverseNormFinal.periodization_limit_proved hp) hp P α β T S hK hS hinter

/-- N11 from the two `functionNorm` facts for `circleMinus` and `circleMid`. -/
theorem slice_N11_of_functionNorm (hp : 1 < p) (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β)
    (hK1 : 0 ≤ functionNorm (circleMinus P α β))
    (hS1 : ∀ u : LpT p, ‖circleMinus P α β u‖ ≤ functionNorm (circleMinus P α β) * ‖u‖)
    (hK2 : 0 ≤ functionNorm (circleMid P α β))
    (hS2 : ∀ u : LpT p, ‖circleMid P α β u‖ ≤ functionNorm (circleMid P α β) * ‖u‖) :
    ‖T.map‖ ≤ ‖pencil P α β‖ ∧ ‖T.map‖ ≤ functionNorm (circleMinus P α β) ∧
      ‖T.map‖ ≤ functionNorm (circleMid P α β) :=
  ⟨ReverseNormFinal.pencil_reverse_bound_proved hp P α β T,
    reverse_bound_of_functionNorm hp P α β T _ hK1 hS1 fun f g hc hz hfg N hN F G hF hG =>
      (SchwartzPencilPeriodization.intertwine_of_fourier P α β f g hc hz hfg N hN F G hF hG).2.1,
    reverse_bound_of_functionNorm hp P α β T _ hK2 hS2 fun f g hc hz hfg N hN F G hF hG =>
      (SchwartzPencilPeriodization.intertwine_of_fourier P α β f g hc hz hfg N hN F G hF hG).2.2⟩

/-- **N11** (norm_correspondence.tex l.52-55): `‖T_ℝ‖` is at most the norm of each circle convention. -/
theorem slice_N11_proved (hp : 1 < p) (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β) :
    ‖T.map‖ ≤ ‖pencil P α β‖ ∧ ‖T.map‖ ≤ functionNorm (circleMinus P α β) ∧
      ‖T.map‖ ≤ functionNorm (circleMid P α β) :=
  slice_N11_of_functionNorm hp P α β T (CircleMapNorm.functionNorm_nonneg _)
    (CircleMapNorm.norm_circleMinus_le_functionNorm P α β) (CircleMapNorm.functionNorm_nonneg _)
    (CircleMapNorm.norm_circleMid_le_functionNorm P α β)

end GKSharp.Proofs.ReverseNormCircle
