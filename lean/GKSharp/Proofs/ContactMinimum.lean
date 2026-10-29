/- GKSharp/Proofs/ContactMinimum.lean — stability of the global minimum.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactSmooth
import GKSharp.Proofs.ObstacleMinimum

namespace GKSharp.ContactSmooth
open GKSharp.Threshold Set Filter
open scoped Topology ContDiff

/-- On a compact set, a strict unique minimum keeps every nearby minimizer
inside any prescribed neighborhood of the original minimum. -/
lemma minimum_localizes {F : ℝ × ℝ → ℝ} {K : Set ℝ} {t y : ℝ}
    (hF : Continuous F) (hK : IsCompact K)
    (hstrict : ∀ v : ℝ, v ≠ y → F (t, y) < F (t, v))
    {V : Set ℝ} (hV : V ∈ 𝓝 y) :
    ∀ᶠ s in 𝓝 t, ∀ v ∈ K, F (s, v) ≤ F (s, y) → v ∈ V := by
  obtain ⟨W, hWV, hW, hyW⟩ := mem_nhds_iff.mp hV
  apply hK.eventually_forall_of_forall_eventually
  intro v _
  by_cases hv : v ∈ W
  · have hh : ∀ᶠ u : ℝ × ℝ in 𝓝 (t, v), u.2 ∈ W :=
      continuous_snd.continuousAt.preimage_mem_nhds (hW.mem_nhds hv)
    filter_upwards [hh] with u hu
    exact fun _ => hWV hu
  · have hne : v ≠ y := by rintro rfl; exact hv hyW
    have hleft : Continuous (fun u : ℝ × ℝ => F (u.1, y)) :=
      hF.comp (continuous_fst.prodMk continuous_const)
    have hh : ∀ᶠ u : ℝ × ℝ in 𝓝 (t, v), F (u.1, y) < F u :=
      (isOpen_lt hleft hF).mem_nhds (hstrict v hne)
    filter_upwards [hh] with u hu
    exact fun hle => False.elim (not_le_of_gt hu hle)

/-- A nondegenerate local critical branch is the only global minimizer nearby
when all minimizers have a common compact bound and the contact minimum is unique. -/
lemma minimum_eq_branch {f : ℝ → ℝ → ℝ} {branch : ℝ → ℝ} {K : Set ℝ} {t y : ℝ}
    (hF : Continuous (fun u : ℝ × ℝ => f u.2 u.1)) (hK : IsCompact K)
    (hstrict : ∀ v : ℝ, v ≠ y → f y t < f v t)
    (hlocal : ∀ᶠ u : ℝ × ℝ in 𝓝 (t, y), dy f u.2 u.1 = 0 ↔ branch u.1 = u.2) :
    ∀ᶠ s in 𝓝 t, ∀ v ∈ K, (∀ w : ℝ, f v s ≤ f w s) → branch s = v := by
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hlocal
  have hmin := minimum_localizes hF hK hstrict hV
  filter_upwards [hU, hmin] with s hs hmins
  intro v hv hglobal
  have hvV := hmins v hv (hglobal y)
  apply (hUV (show (s, v) ∈ U ×ˢ V from ⟨hs, hvV⟩)).mp
  have hlocalmin : IsLocalMin (fun w => f w s) v :=
    Filter.Eventually.of_forall hglobal
  exact hlocalmin.deriv_eq_zero

end GKSharp.ContactSmooth
