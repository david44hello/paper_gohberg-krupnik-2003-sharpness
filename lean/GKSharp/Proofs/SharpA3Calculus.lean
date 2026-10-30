/-
SharpA3Calculus.lean — calculus consequences used in Section5 (A3).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.CriticalMaximum
import Mathlib.Analysis.Calculus.Darboux

namespace GKSharp.Proofs.SharpA3Calculus

open Set Filter Topology

lemma derivative_sign_alternative {f : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hn : ∀ x ∈ Ioo a b, deriv f x ≠ 0) :
    (∀ x ∈ Ioo a b, deriv f x < 0) ∨ (∀ x ∈ Ioo a b, 0 < deriv f x) := by
  exact hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_Ioo a b)
    (fun x hx => (hd x hx).hasDerivAt.hasDerivWithinAt) hn

theorem shape_of_unique_critical {f : ℝ → ℝ} {a b c : ℝ}
    (hc : c ∈ Ioo a b) (hcont : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hzero : deriv f c = 0) (hsecond : deriv (deriv f) c < 0)
    (hunique : ∀ x ∈ Ioo a b, deriv f x = 0 → x = c) :
    (∀ x ∈ Ioo a c, 0 < deriv f x) ∧
    (∀ x ∈ Ioo c b, deriv f x < 0) ∧
    ∀ x ∈ Icc a b, x ≠ c → f x < f c := by
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hsecond hzero
  have hleft := deriv_pos_left_of_sign_deriv (nhdsWithin_le_nhds hsign)
  have hright := deriv_neg_right_of_sign_deriv (nhdsWithin_le_nhds hsign)
  have hpos : ∀ x ∈ Ioo a c, 0 < deriv f x := by
    rcases derivative_sign_alternative
      (fun x hx => hd x ⟨hx.1, hx.2.trans hc.2⟩)
      (fun x hx hh => ne_of_lt hx.2 (hunique x ⟨hx.1, hx.2.trans hc.2⟩ hh)) with hn | hp
    · obtain ⟨x, hxpos, hx⟩ := (hleft.and (Ioo_mem_nhdsLT hc.1)).exists
      exact False.elim (lt_asymm (hn x hx) hxpos)
    · exact hp
  have hneg : ∀ x ∈ Ioo c b, deriv f x < 0 := by
    rcases derivative_sign_alternative
      (fun x hx => hd x ⟨hc.1.trans hx.1, hx.2⟩)
      (fun x hx hh => ne_of_gt hx.1 (hunique x ⟨hc.1.trans hx.1, hx.2⟩ hh)) with hn | hp
    · exact hn
    · obtain ⟨x, hxneg, hx⟩ := (hright.and (Ioo_mem_nhdsGT hc.2)).exists
      exact False.elim (lt_asymm (hp x hx) hxneg)
  refine ⟨hpos, hneg, ?_⟩
  have hmono : StrictMonoOn f (Icc a c) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a c)
    · exact hcont.mono (Icc_subset_Icc le_rfl hc.2.le)
    · simpa only [interior_Icc] using hpos
  have hanti : StrictAntiOn f (Icc c b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc c b)
    · exact hcont.mono (Icc_subset_Icc hc.1.le le_rfl)
    · simpa only [interior_Icc] using hneg
  intro x hx hxc
  rcases lt_or_gt_of_ne hxc with hlt | hgt
  · exact hmono ⟨hx.1, hlt.le⟩ ⟨hc.1.le, le_rfl⟩ hlt
  · exact hanti ⟨le_rfl, hc.2.le⟩ ⟨hgt.le, hx.2⟩ hgt

theorem shape_of_no_critical {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hn : ∀ x ∈ Ioo a b, deriv f x ≠ 0) (hend : f b ≤ f a) :
    (MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)) ∧
    ∀ x ∈ Icc a b, f x ≤ f a := by
  rcases derivative_sign_alternative hd hn with hneg | hpos
  · have hanti : AntitoneOn f (Icc a b) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont
      · intro x hx
        rw [interior_Icc] at hx
        exact (hd x hx).differentiableWithinAt
      · simpa only [interior_Icc] using fun x hx => (hneg x hx).le
    exact ⟨Or.inr hanti, fun x hx => hanti ⟨le_rfl, hab⟩ hx hx.1⟩
  · have hmono : MonotoneOn f (Icc a b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont
      · intro x hx
        rw [interior_Icc] at hx
        exact (hd x hx).differentiableWithinAt
      · simpa only [interior_Icc] using fun x hx => (hpos x hx).le
    exact ⟨Or.inl hmono, fun x hx => (hmono hx ⟨hab, le_rfl⟩ hx.2).trans hend⟩

end GKSharp.Proofs.SharpA3Calculus

#print axioms GKSharp.Proofs.SharpA3Calculus.shape_of_unique_critical
#print axioms GKSharp.Proofs.SharpA3Calculus.shape_of_no_critical
