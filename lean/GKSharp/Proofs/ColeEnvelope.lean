/- Cole existence combined with the internal envelope/dilation proof.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ColeHom
import GKSharp.Cited.HKV21

namespace GKSharp
open Real Metric Set Filter Topology MeasureTheory

/-- sec2_obstacle.tex (short v0.40):96–99. Only existence uses the external
Cole input; regularization, largest-minorant property and dilation are proved internally. -/
theorem cole_largest_homogeneous {F : ℂ → ℝ} (hFc : Continuous F) {q : ℝ}
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → F ((r : ℂ) * z) = r ^ q * F z)
    (hdisc : PolynomialDiscBound F) :
    ∃ V : ℂ → EReal, IsSubharmonic V ∧ (∀ z, V z ≤ (F z : EReal)) ∧ 0 ≤ V 0 ∧
      (∀ (t : ℝ) (z : ℂ), 0 < t → V ((t : ℂ) * z) = ((t ^ q : ℝ) : EReal) * V z) ∧
      (∀ u : ℂ → EReal, IsSubharmonic u → (∀ z, u z ≤ (F z : EReal)) → ∀ z, u z ≤ V z) := by
  apply ColeHom.largest_homogeneous_minorant hFc hhom
  let Fe : ℂ → EReal := fun z => (F z : EReal)
  have hFusc : UpperSemicontinuous Fe :=
    (continuous_coe_real_ereal.comp hFc).upperSemicontinuous
  have h21 : ∀ g : Polynomial ℂ, g.eval 0 ∈ ({0} : Set ℂ) → ∀ n : ℕ,
      0 ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), potentialTrunc n (Fe (g.eval (unitPoint t))) := by
    intro g hg n
    have hcont : Continuous (fun t : ℝ => F (g.eval (unitPoint t))) := by
      apply hFc.comp
      apply g.continuous.comp
      unfold unitPoint
      fun_prop
    have hcont' : Continuous (fun t : ℝ => potentialTrunc n (Fe (g.eval (unitPoint t)))) := by
      simp only [Fe, SubharmonicBasic.trunc_coe]
      exact hcont.max continuous_const
    have hg0 : g.eval 0 = 0 := mem_singleton_iff.mp hg
    exact (hdisc g hg0).trans
      (intervalIntegral.integral_mono_on two_pi_pos.le (hcont.intervalIntegrable _ _)
        (hcont'.intervalIntegrable _ _) (fun t _ => by
          simp only [Fe, SubharmonicBasic.trunc_coe]
          exact le_max_left _ _))
  obtain ⟨v, hv, hvF, hv0⟩ := Cited.hkv_thm21 Fe hFusc
    (fun z => EReal.coe_ne_top _) {0} (singleton_nonempty 0) h21
  exact ⟨v, hv, hvF, hv0 0 rfl⟩

/-- Exact corrected proposal O26, with all mathematical premises preserved. -/
theorem slice_O26_proved (q : ℝ) (M : ℂ → ℝ) (hM : Continuous M)
    (hhom : ∀ t : ℝ, 0 < t → ∀ z : ℂ, M ((t : ℂ) * z) = t ^ q * M z)
    (hdisc : PolynomialDiscBound M) :
    ∃ V : ℂ → EReal, IsSubharmonic V ∧ (∀ z, V z ≤ (M z : EReal)) ∧ 0 ≤ V 0 ∧
      (∀ (t : ℝ) (z : ℂ), 0 < t → V ((t : ℂ) * z) = ((t ^ q : ℝ) : EReal) * V z) ∧
      (∀ u : ℂ → EReal, IsSubharmonic u → (∀ z, u z ≤ (M z : EReal)) → ∀ z, u z ≤ V z) :=
  cole_largest_homogeneous hM (fun r z hr => hhom r hr z) hdisc

end GKSharp
