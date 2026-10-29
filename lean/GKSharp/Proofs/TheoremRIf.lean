/- Theorem R, the "if" direction, for all 1 < p < ∞ (sec2_obstacle.tex l.62-71), with the in-text steps
O19 (removable origin) and O20 (plurisubharmonic product, domination incl. zw = 0, polynomial sub-mean), the
continuity claim of l.58-60 and the q-subtrigonometric ⇔ trigonometrically convex bridge (review 019_b M6).
Copyright (C) Dave Goel 2026--now.

  Throughout sec2, q = p/2 with 1 < p < ∞ (sec2_obstacle.tex l.10), so q > 1/2: the range of every row here.
  Route = the paper's: S(ζ) = |ζ|^q φ(arg ζ) is continuous with S(0) = 0 and sub-mean on every circle (CompSubmeanGK);
  Ψ(z, w) = S(zw) is sub-mean on every complex line; Ψ ≤ G_C pointwise (Γ factorization + obstacle ≤ Γ, and
  G_C ≥ 0 where zw = 0); for polynomials with w(0) = 0, ∫ G_C ≥ ∫ S(zw) ≥ 2π S(0) = 0; then eq_pairs. -/
import GKSharp.Proofs.CompSubmeanGK
import GKSharp.Proofs.Gamma
import GKSharp.Proofs.ObstacleMinimum
import GKSharp.Proofs.PencilPairs
import GKSharp.Defs.ThresholdAnalysis
import GKSharp.Proofs.Sec4aAngular

open Real Metric Set Filter Topology MeasureTheory

namespace GKSharp

namespace TheoremRIf

open PotentialCoordinates CompSubmeanGK

/-! ### Trigonometric convexity: the bridge to Definition 2.1 and to `Threshold.QTrigConvex` -/

/-- A continuous, `2π`-periodic, trigonometrically `q`-convex `φ` (`q > 0`) makes `|ζ|^q φ(arg ζ)` subharmonic on all of
`ℂ` (every circle, the origin included). -/
theorem isSubharmonic_of_trigConvex {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hper : Function.Periodic φ (2 * π)) (htc : TrigConvex q φ) :
    IsSubharmonic (fun z => (angularPotential q φ z : EReal)) :=
  isSubharmonic_of_submean (angularPotential_continuous hq hc hper)
    (fun c _ hr => comp_submean_of_trigConvex hq hc hper htc differentiable_id c hr)

/-- **q-subtrigonometric ⇔ continuous and trigonometrically q-convex** (`q > 1/2`, `φ` periodic): sec2_obstacle.tex
l.58-60 ("φ is q-subtrigonometric if and only if φ is continuous and φ'' + q²φ ≥ 0", here in the chord form of
trigonometric q-convexity, Levin Lecture 8). -/
theorem qsub_iff_continuous_trigconvex {q : ℝ} (hq0 : 1 / 2 < q) {φ : ℝ → ℝ} :
    QSubtrig q φ ↔ Function.Periodic φ (2 * π) ∧ Continuous φ ∧ TrigConvex q φ := by
  constructor
  · intro hφ
    exact ⟨hφ.1, SectorGK.qsubtrig_continuous hq0 hφ, SectorGK.qsubtrig_trigConvex hq0 hφ⟩
  · rintro ⟨hper, hc, htc⟩
    have hS := isSubharmonic_of_trigConvex (by linarith) hc hper htc
    exact ⟨hper, fun z _ => hS.1 z, hS.2.1.upperSemicontinuousOn _, fun n c r hr _ => hS.2.2 n c r hr⟩

/-- The chord form `TrigConvex q f` is the shared `Threshold.QTrigConvex q f` (`q > 0`): substitute `x ↦ x/q`. -/
theorem trigConvex_iff_qTrigConvex {q : ℝ} (hq : 0 < q) (f : ℝ → ℝ) : TrigConvex q f ↔ Threshold.QTrigConvex q f := by
  have hdiv : ∀ a b : ℝ, q * (a / q - b / q) = a - b := fun a b => by field_simp
  constructor
  · intro h X _ Y _ T _ hXT hTY hlen
    have hs : 0 < Real.sin (Y - X) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hlen
    have h1 := h (X / q) (T / q) (Y / q) (div_lt_div_of_pos_right hXT hq) (div_lt_div_of_pos_right hTY hq)
      (by rw [hdiv]; exact hlen)
    rw [hdiv, hdiv, hdiv] at h1
    show f (T / q) ≤ (f (X / q) * Real.sin (Y - T) + f (Y / q) * Real.sin (T - X)) / Real.sin (Y - X)
    rw [le_div_iff₀ hs]
    exact h1
  · intro h x t y hxt hty hlen
    have hs : 0 < sin (q * (y - x)) := sin_pos_of_pos_of_lt_pi (mul_pos hq (by linarith)) hlen
    have h1 := h (q * x) (mem_univ _) (q * y) (mem_univ _) (q * t) (mem_univ _)
      (mul_lt_mul_of_pos_left hxt hq) (mul_lt_mul_of_pos_left hty hq) (by rw [← mul_sub]; exact hlen)
    simp only [mul_div_cancel_left₀ _ hq.ne'] at h1
    rw [← mul_sub, ← mul_sub, ← mul_sub, le_div_iff₀ hs] at h1
    exact h1

/-- Review 019_b M6 (the bridge type): q-subtrigonometric ⇒ continuous and `QTrigConvex` (q > 1/2). -/
theorem qsub_continuous_trigconvex_proved (qq : ℝ) (hq : 1 / 2 < qq) (phi : ℝ → ℝ) (hphi : QSubtrig qq phi) :
    Continuous phi ∧ Threshold.QTrigConvex qq phi :=
  ⟨SectorGK.qsubtrig_continuous hq hphi,
    (trigConvex_iff_qTrigConvex (by linarith) phi).mp (SectorGK.qsubtrig_trigConvex hq hphi)⟩

/-- sec4a_criterion.tex l.22: "K cos(q|t|) is q-subtrigonometric" (the cosine wrapped to (-π, π], K ≥ 0, 1 < p < 2),
from the installed wrapped_cosine_trigconvex row and the bridge. -/
theorem sec4_cosine_qsub_proved (p KK : ℝ) (hp : 1 < p) (hp2 : p < 2) (hK : 0 ≤ KK) :
    QSubtrig (Threshold.q p) (fun t : ℝ => KK * Real.cos
      (Threshold.q p * Complex.arg (Complex.exp (Complex.I * (t : ℂ))))) := by
  have hq0 : 1 / 2 < Threshold.q p := by unfold Threshold.q; linarith
  obtain ⟨hc, hper, htc⟩ := wrapped_cosine_trigconvex_proved (Threshold.q p) KK
    ⟨by linarith, by unfold Threshold.q; linarith⟩ hK
  exact (qsub_iff_continuous_trigconvex hq0).mpr ⟨hper, hc, (trigConvex_iff_qTrigConvex (by linarith) _).mpr htc⟩

/-! ### O19: the removable origin -/

/-- **O19** (sec2_obstacle.tex l.67-68: "S(ζ) = |ζ|^q φ(arg ζ) is subharmonic on ℂ \ {0} and tends to 0 at 0 (φ is
bounded), so it extends subharmonically to ℂ with S(0) = 0"). Range: q > 1/2 (l.10: q = p/2, 1 < p < ∞). -/
theorem removable_origin {q : ℝ} (hq0 : 1 / 2 < q) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) :
    Continuous (angularPotential q φ) ∧ angularPotential q φ 0 = 0 ∧
      IsSubharmonic (fun z => (angularPotential q φ z : EReal)) := by
  have hq : 0 < q := by linarith
  have hc := SectorGK.qsubtrig_continuous hq0 hφ
  exact ⟨angularPotential_continuous hq hc hφ.1, angularPotential_zero hq φ,
    isSubharmonic_of_trigConvex hq hc hφ.1 (SectorGK.qsubtrig_trigConvex hq0 hφ)⟩

/-! ### O20: Ψ(z, w) = S(zw) -/

/-- **O20 (a)** (l.68: "Ψ(z, w) = S(zw) is plurisubharmonic"). -/
theorem isPSH_product {q : ℝ} (hq0 : 1 / 2 < q) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) :
    IsPSH (fun zw : ℂ × ℂ => (angularPotential q φ (zw.1 * zw.2) : EReal)) := by
  have hq : 0 < q := by linarith
  have hS := angularPotential_continuous hq (SectorGK.qsubtrig_continuous hq0 hφ) hφ.1
  refine ⟨fun _ => EReal.coe_ne_top _,
    (continuous_coe_real_ereal.comp (hS.comp (continuous_fst.mul continuous_snd))).upperSemicontinuous,
    fun a b => ?_⟩
  set h : ℂ → ℂ := fun l => (a + l • b).1 * (a + l • b).2 with hh
  have hhd : Differentiable ℂ h := by
    have : h = fun l => (a.1 + l * b.1) * (a.2 + l * b.2) := by funext l; simp [hh]
    rw [this]; fun_prop
  exact isSubharmonic_of_submean (hS.comp hhd.continuous) (fun c r hr => comp_submean hq0 hφ hhd c hr)

/-- **O20 (b)** (l.68-70: "Ψ ≤ G_C: where zw ≠ 0, Ψ = |zw|^q φ(t) ≤ |zw|^q m_C(t) ≤ G_C; where zw = 0, Ψ = 0 ≤ G_C"). -/
theorem product_le_pairObstacle {p C : ℝ} (hp : 1 < p) {ρ : ℂ} (hC : max 1 ‖ρ‖ < C) {φ : ℝ → ℝ}
    (hle : ∀ t, φ t ≤ obstacle p C ρ t) (z w : ℂ) :
    angularPotential (p / 2) φ (z * w) ≤ pairObstacle p C ρ z w := by
  by_cases hzw : z * w = 0
  · rw [hzw, angularPotential_zero (by linarith)]
    exact pairObstacle_nonneg_zero_product (by linarith) ρ z w hC hzw
  · rw [pair_gamma_factor p C ρ z w hzw]
    unfold angularPotential
    have hbdd := (slice_O12_proved hp C ρ hC).2.1 (Complex.arg (z * w))
    have h1 : obstacle p C ρ (Complex.arg (z * w)) ≤ gamma p C ρ (log (‖z‖ / ‖w‖)) (Complex.arg (z * w)) :=
      csInf_le hbdd ⟨_, rfl⟩
    exact mul_le_mul_of_nonneg_left ((hle _).trans h1) (rpow_nonneg (norm_nonneg _) _)

/-- `G_C(z, w)` is continuous in `(z, w)` (`p > 0`). -/
theorem continuous_pairObstacle {p : ℝ} (hp : 0 < p) (C : ℝ) (ρ : ℂ) :
    Continuous (fun x : ℂ × ℂ => pairObstacle p C ρ x.1 x.2) := by
  unfold pairObstacle
  have h1 : Continuous (fun x : ℂ × ℂ => ‖x.1 + star x.2‖) :=
    (continuous_fst.add (continuous_star.comp continuous_snd)).norm
  have h2 : Continuous (fun x : ℂ × ℂ => ‖x.1 + ρ * star x.2‖) :=
    (continuous_fst.add (continuous_const.mul (continuous_star.comp continuous_snd))).norm
  exact (continuous_const.mul (h1.rpow_const fun _ => Or.inr hp.le)).sub (h2.rpow_const fun _ => Or.inr hp.le)

theorem continuous_unitPoint : Continuous unitPoint :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

/-- **O20 (c)** (l.70-71: "For polynomials with w(0) = 0 the sub-mean value property of Ψ(z, w) on the disc gives
∫_T G_C(z, w) ≥ ∫_T Ψ(z, w) ≥ Ψ(z(0), 0) = 0"), i.e. (eq:pairs). -/
theorem polynomialPairBound_of_qsubtrig {p C : ℝ} (hp : 1 < p) {ρ : ℂ} (hC : max 1 ‖ρ‖ < C) {φ : ℝ → ℝ}
    (hφ : QSubtrig (p / 2) φ) (hle : ∀ t, φ t ≤ obstacle p C ρ t) : PolynomialPairBound p C ρ := by
  intro z w hw0
  have hq0 : 1 / 2 < p / 2 := by linarith
  have hq : 0 < p / 2 := by linarith
  have hS := angularPotential_continuous hq (SectorGK.qsubtrig_continuous hq0 hφ) hφ.1
  have hg0 : (z * w).eval 0 = 0 := by rw [Polynomial.eval_mul, hw0, mul_zero]
  have hsub := comp_submean hq0 hφ (z * w).differentiable 0 one_pos
  rw [hg0, angularPotential_zero hq, circleAverage_def, smul_eq_mul] at hsub
  have hcm : ∀ θ : ℝ, circleMap 0 1 θ = unitPoint θ := fun θ => by simp [circleMap, unitPoint]
  simp only [hcm] at hsub
  have hI : 0 ≤ ∫ θ in (0 : ℝ)..(2 * π), angularPotential (p / 2) φ ((z * w).eval (unitPoint θ)) :=
    (mul_nonneg_iff_of_pos_left (inv_pos.mpr two_pi_pos)).mp hsub
  refine hI.trans (intervalIntegral.integral_mono_on two_pi_pos.le ?_ ?_ fun θ _ => ?_)
  · exact (hS.comp ((z * w).continuous.comp continuous_unitPoint)).intervalIntegrable _ _
  · exact ((continuous_pairObstacle (by linarith) C ρ).comp
      ((z.continuous.comp continuous_unitPoint).prodMk (w.continuous.comp continuous_unitPoint))).intervalIntegrable _ _
  · rw [Polynomial.eval_mul]
    exact product_le_pairObstacle hp hC hle _ _

/-- **O20** (l.68-71), all three claims together, in the proposal's form. -/
theorem slice_O20_proved {p : ℝ} (hp : 1 < p) (C : ℝ) (ρ : ℂ) (hC : max 1 ‖ρ‖ < C)
    (φ : ℝ → ℝ) (hφ : QSubtrig (p / 2) φ) (hle : ∀ t, φ t ≤ obstacle p C ρ t) :
    IsPSH (fun zw => (angularPotential (p / 2) φ (zw.1 * zw.2) : EReal)) ∧
    (∀ z w : ℂ, angularPotential (p / 2) φ (z * w) ≤ pairObstacle p C ρ z w) ∧
    PolynomialPairBound p C ρ :=
  ⟨isPSH_product (by linarith) hφ, product_le_pairObstacle hp hC hle, polynomialPairBound_of_qsubtrig hp hC hφ hle⟩

/-! ### Theorem R, "if" -/

/-- **Theorem R, "if"** (sec2_obstacle.tex l.62-63, proof l.67-71): for 1 < p < ∞, ρ ∈ ℂ and C > max(1, |ρ|), if some
q-subtrigonometric φ (q = p/2) satisfies φ ≤ m_C on ℝ, then N_p(ρ) ≤ C. -/
theorem thmR_if {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) (ρ : ℂ) {C : ℝ}
    (hC : max 1 ‖ρ‖ < C) (hex : ∃ φ : ℝ → ℝ, QSubtrig (p / 2) φ ∧ ∀ t, φ t ≤ obstacle p C ρ t) :
    pencilNorm P ρ ≤ C := by
  obtain ⟨φ, hφ, hle⟩ := hex
  have hC0 : 0 ≤ C := le_trans zero_le_one ((le_max_left _ _).trans hC.le)
  exact (norm_iff_polynomial_pairs hp P ρ C hC0).mpr (polynomialPairBound_of_qsubtrig hp hC hφ hle)

end TheoremRIf

end GKSharp
