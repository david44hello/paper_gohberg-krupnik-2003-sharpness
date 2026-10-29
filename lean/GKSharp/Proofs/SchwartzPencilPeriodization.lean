/- periodization intertwining from the actual real-line Fourier identity.
Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.SchwartzPencilOutput
import GKSharp.Proofs.SchwartzPeriodizationMain
import GKSharp.Proofs.PencilModes

namespace GKSharp.Proofs.SchwartzPencilPeriodization

open GKSharp.RealLineFourier MeasureTheory Filter Topology Set
open scoped FourierTransform

theorem output_support (α β : ℂ) (f g : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (paperFourier f)) (hz : 0 ∉ tsupport (paperFourier f))
    (hfg : ∀ ξ : ℝ, paperFourier g ξ = (if 0 < ξ then α else β) * paperFourier f ξ) :
    HasCompactSupport (paperFourier g) ∧ 0 ∉ tsupport (paperFourier g) := by
  have he : paperFourier g = fun ξ : ℝ => (if 0 < ξ then α else β) * paperFourier f ξ :=
    funext hfg
  rw [he]
  exact ⟨hc.mul_left, fun hh => hz (tsupport_mul_subset_right hh)⟩

theorem periodization_coeff (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (paperFourier f)) (hz : 0 ∉ tsupport (paperFourier f))
    (N : ℕ) (hN : 0 < N) (F : C(Circ, ℂ))
    (hF : ∀ t : ℝ, F (t : Circ) = periodized f N t) :
    (∀ n : ℤ, fourierCoeff (⇑F) n =
      ((2 * Real.pi * N : ℝ)⁻¹ : ℂ) * paperFourier f ((n : ℝ) / N)) ∧
      fourierCoeff (⇑F) 0 = 0 := by
  obtain ⟨F₀, hF₀, hcoeff, _, hzero⟩ :=
    SchwartzPeriodizationMain.slice_N07_proved f hc hz N hN
  have he : F = F₀ := by
    ext t
    refine QuotientAddGroup.induction_on t (fun θ => ?_)
    exact (hF θ).trans (hF₀ θ).symm
  subst F
  exact ⟨hcoeff, hzero⟩

theorem intertwine_of_fourier {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (P : RieszProjection p) (α β : ℂ) (f g : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (paperFourier f)) (hz : 0 ∉ tsupport (paperFourier f))
    (hfg : ∀ ξ : ℝ, paperFourier g ξ = (if 0 < ξ then α else β) * paperFourier f ξ)
    (N : ℕ) (hN : 0 < N) (F G : C(Circ, ℂ))
    (hF : ∀ t : ℝ, F (t : Circ) = periodized f N t)
    (hG : ∀ t : ℝ, G (t : Circ) = periodized g N t) :
    pencil P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G ∧
    circleMinus P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G ∧
    circleMid P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G := by
  obtain ⟨hgc, hgz⟩ := output_support α β f g hc hz hfg
  obtain ⟨hFc, hFz⟩ := periodization_coeff f hc hz N hN F hF
  obtain ⟨hGc, _⟩ := periodization_coeff g hgc hgz N hN G hG
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmap : pencil P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G := by
    apply DensityLp.fourier_ext
    intro n
    rw [coeff_pencil, DensityLp.coeff_toLpT, DensityLp.coeff_toLpT, hFc, hGc, hfg]
    by_cases hn : n = 0
    · subst n
      simp [SchwartzPeriodization.paperFourier_zero_of_separated f hz]
    · have hs : ((0 : ℝ) < (n : ℝ) / N) ↔ (0 : ℤ) ≤ n := by
        rw [div_pos_iff_of_pos_right hNr]
        exact_mod_cast (show (0 : ℤ) < n ↔ 0 ≤ n by omega)
      simp only [hs]
      ring
  have hzLp : zeroPart p (DensityLp.toLpT p F) = 0 := by
    unfold zeroPart
    rw [DensityLp.coeff_toLpT, hFz]
    change (ContinuousMap.toLp (E := ℂ) (ENNReal.ofReal p) (volume : Measure Circ) ℂ) 0 = 0
    exact map_zero _
  have hminus : circleMinus P α β (DensityLp.toLpT p F) = DensityLp.toLpT p G := by
    simp [circleMinus, hzLp, hmap]
  refine ⟨hmap, hminus, ?_⟩
  rw [circleMid, hmap, hminus, ← two_smul ℂ _]
  simp [smul_smul]

end GKSharp.Proofs.SchwartzPencilPeriodization

#print axioms GKSharp.Proofs.SchwartzPencilPeriodization.intertwine_of_fourier
