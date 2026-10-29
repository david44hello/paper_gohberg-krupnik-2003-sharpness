/- reverse real-line/circle norm transference using the genuine periodization limit and density.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.SchwartzPencil
import GKSharp.Proofs.PeriodizationNormLimit

namespace GKSharp.Proofs.ReverseNorm

open GKSharp.RealLineFourier GKSharp.Proofs.RealLineUnique
open GKSharp.Proofs.NormTransference GKSharp.Proofs.PeriodizationNormLimit
open MeasureTheory Filter Topology Set

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

def N09At (p : ℝ) : Prop := ∀ f : SchwartzMap ℝ ℂ,
  Tendsto (fun N : ℕ => (2 * Real.pi * N) * circlePower p (periodized f N)) atTop
    (𝓝 (∫ x : ℝ, ‖f x‖ ^ p))

theorem norm_bound_on_separated (hN10 : N10Prop) (hN09 : N09At p) (hp : 1 < p)
    (_P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β)
    (C : LpT p → LpT p) {K : ℝ} (hK : 0 ≤ K)
    (hC : ∀ u : LpT p, ‖C u‖ ≤ K * ‖u‖)
    (hinter : ∀ (f g : SchwartzMap ℝ ℂ), HasCompactSupport (paperFourier f) →
      0 ∉ tsupport (paperFourier f) →
      (∀ ξ : ℝ, paperFourier g ξ = (if 0 < ξ then α else β) * paperFourier f ξ) →
      ∀ (N : ℕ), 0 < N → ∀ F G : C(Circ, ℂ),
        (∀ t : ℝ, F (t : Circ) = periodized f N t) →
        (∀ t : ℝ, G (t : Circ) = periodized g N t) →
        C (DensityLp.toLpT p F) = DensityLp.toLpT p G)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (paperFourier f))
    (hz : 0 ∉ tsupport (paperFourier f)) :
    ‖T.map (f.toLp (ENNReal.ofReal p) volume)‖ ≤ K * ‖f.toLp (ENNReal.ofReal p) volume‖ := by
  obtain ⟨g, hmap, hpaper⟩ := SchwartzPencil.output_of_N10 hN10 hp α β T f hc hz
  obtain ⟨hgc, hgz⟩ := SchwartzPencilPeriodization.output_support α β f g hc hz hpaper
  rw [hmap]
  apply schwartz_norm_le_of_periodization (by linarith) f g hK hN09
  intro N hN
  obtain ⟨F, hF, _, _, _⟩ := SchwartzPeriodizationMain.slice_N07_proved f hc hz N hN
  obtain ⟨G, hG, _, _, _⟩ := SchwartzPeriodizationMain.slice_N07_proved g hgc hgz N hN
  refine ⟨F, G, hF, hG, ?_⟩
  rw [← hinter f g hc hz hpaper N hN F G hF hG]
  exact hC _

theorem opNorm_le_circle_bound (hN10 : N10Prop) (hN09 : N09At p) (hp : 1 < p)
    (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β)
    (C : LpT p → LpT p) {K : ℝ} (hK : 0 ≤ K)
    (hC : ∀ u : LpT p, ‖C u‖ ≤ K * ‖u‖)
    (hinter : ∀ (f g : SchwartzMap ℝ ℂ), HasCompactSupport (paperFourier f) →
      0 ∉ tsupport (paperFourier f) →
      (∀ ξ : ℝ, paperFourier g ξ = (if 0 < ξ then α else β) * paperFourier f ξ) →
      ∀ (N : ℕ), 0 < N → ∀ F G : C(Circ, ℂ),
        (∀ t : ℝ, F (t : Circ) = periodized f N t) →
        (∀ t : ℝ, G (t : Circ) = periodized g N t) →
        C (DensityLp.toLpT p F) = DensityLp.toLpT p G) : ‖T.map‖ ≤ K := by
  apply opNorm_le_of_separated_tests T.map hK (hN10 p hp)
  exact norm_bound_on_separated hN10 hN09 hp P α β T C hK hC hinter

theorem pencil_reverse_bound (hN10 : N10Prop) (hN09 : N09At p) (hp : 1 < p)
    (P : RieszProjection p) (α β : ℂ) (T : RealLinePencil p α β) :
    ‖T.map‖ ≤ ‖pencil P α β‖ := by
  apply opNorm_le_circle_bound hN10 hN09 hp P α β T (pencil P α β)
    (norm_nonneg _) (pencil P α β).le_opNorm
  intro f g hc hz hfg N hN F G hF hG
  exact (SchwartzPencilPeriodization.intertwine_of_fourier P α β f g hc hz hfg N hN F G hF hG).1

end GKSharp.Proofs.ReverseNorm

#print axioms GKSharp.Proofs.ReverseNorm.pencil_reverse_bound
