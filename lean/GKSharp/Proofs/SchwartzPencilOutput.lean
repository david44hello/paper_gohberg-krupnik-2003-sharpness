/- the genuine Schwartz output of a two-half-line Fourier multiplier.
Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Defs.RealLineFourier
import GKSharp.Proofs.BandLimitedSchwartz

namespace GKSharp.Proofs.SchwartzPencilOutput

open GKSharp.RealLineFourier MeasureTheory Filter Topology Set
open scoped FourierTransform ContDiff

theorem paperFourier_eq (f : ℝ → ℂ) (ξ : ℝ) :
    paperFourier f ξ = 𝓕 f (ξ / (2 * Real.pi)) :=
  BandLimitedSchwartz.paper_transform_eq f ξ

theorem normalized_fourier_eq (f : SchwartzMap ℝ ℂ) :
    (fun ξ : ℝ => paperFourier f (2 * Real.pi * ξ)) = (𝓕 f : SchwartzMap ℝ ℂ) := by
  funext ξ
  rw [paperFourier_eq]
  have hs : 2 * Real.pi * ξ / (2 * Real.pi) = ξ := by field_simp
  rw [hs]
  exact (congrFun (SchwartzMap.fourier_coe f) ξ).symm

theorem normalized_support (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (paperFourier f)) (hz : 0 ∉ tsupport (paperFourier f)) :
    HasCompactSupport (𝓕 f : SchwartzMap ℝ ℂ) ∧
      0 ∉ tsupport (𝓕 f : SchwartzMap ℝ ℂ) := by
  have hscale : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have he := normalized_fourier_eq f
  constructor
  · rw [← he]
    exact hc.comp_isClosedEmbedding (Homeomorph.mulLeft₀ (2 * Real.pi) hscale).isClosedEmbedding
  · rw [← he]
    intro hh
    have hsub := tsupport_comp_subset_preimage (paperFourier f)
      (show Continuous (fun ξ : ℝ => 2 * Real.pi * ξ) by fun_prop)
    exact hz (by simpa using hsub hh)

noncomputable def masked (α β : ℂ) (F : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (if 0 < ξ then α else β) * F ξ

theorem masked_smooth (α β : ℂ) (F : SchwartzMap ℝ ℂ)
    (hz : 0 ∉ tsupport F) : ContDiff ℝ ∞ (masked α β F) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro ξ
  rcases lt_trichotomy 0 ξ with hpos | hzero | hneg
  · apply ((contDiff_const.mul (F.smooth (⊤ : ℕ∞))).contDiffAt :
      ContDiffAt ℝ ∞ (fun x => α * F x) ξ).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hpos] with x hx
    have hx' : 0 < x := hx
    simp [masked, hx']
  · subst ξ
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) 0).congr_of_eventuallyEq
    filter_upwards [((isClosed_tsupport F).isOpen_compl.mem_nhds hz)] with x hx
    simp only [mem_compl_iff] at hx
    simp [masked, image_eq_zero_of_notMem_tsupport hx]
  · apply ((contDiff_const.mul (F.smooth (⊤ : ℕ∞))).contDiffAt :
      ContDiffAt ℝ ∞ (fun x => β * F x) ξ).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hneg] with x hx
    have hx' : x < 0 := hx
    simp [masked, not_lt.mpr hx'.le]

noncomputable def maskedSchwartz (α β : ℂ) (F : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport F) (hz : 0 ∉ tsupport F) : SchwartzMap ℝ ℂ :=
  (hc.mul_left (f := fun ξ : ℝ => if 0 < ξ then α else β)).toSchwartzMap
    (masked_smooth α β F hz)

@[simp] theorem maskedSchwartz_apply (α β : ℂ) (F : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport F) (hz : 0 ∉ tsupport F) (ξ : ℝ) :
    maskedSchwartz α β F hc hz ξ = (if 0 < ξ then α else β) * F ξ := rfl

theorem exists_output (α β : ℂ) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (paperFourier f)) (hz : 0 ∉ tsupport (paperFourier f)) :
    ∃ g : SchwartzMap ℝ ℂ,
      (∀ ξ : ℝ, (𝓕 g) ξ = (if 0 < ξ then α else β) * (𝓕 f) ξ) ∧
      (∀ ξ : ℝ, paperFourier g ξ = (if 0 < ξ then α else β) * paperFourier f ξ) := by
  classical
  obtain ⟨hfc, hfz⟩ := normalized_support f hc hz
  let H := maskedSchwartz α β (𝓕 f) hfc hfz
  let g : SchwartzMap ℝ ℂ := 𝓕⁻ H
  have hg : (𝓕 g : SchwartzMap ℝ ℂ) = H := FourierTransform.fourier_fourierInv_eq H
  refine ⟨g, ?_, ?_⟩
  · intro ξ
    rw [hg]
    rfl
  · intro ξ
    rw [paperFourier_eq, paperFourier_eq]
    change (𝓕 g : SchwartzMap ℝ ℂ) (ξ / (2 * Real.pi)) = _
    rw [hg]
    simp only [H, maskedSchwartz_apply]
    simp only [← SchwartzMap.fourier_coe,
      div_pos_iff_of_pos_right (by positivity : 0 < 2 * Real.pi)]

end GKSharp.Proofs.SchwartzPencilOutput

#print axioms GKSharp.Proofs.SchwartzPencilOutput.exists_output
