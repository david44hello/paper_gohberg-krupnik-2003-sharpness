/- elementary truncation inequalities for extended-real subharmonic functions.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Potential
namespace GKSharp.SubharmonicBasic

/-- `potentialTrunc n x ≥ -n` for `x ≠ ⊤`. -/
theorem trunc_ge {x : EReal} (hx : x ≠ ⊤) (n : ℕ) : -(n : ℝ) ≤ potentialTrunc n x := by
  unfold potentialTrunc
  have hm : -(n : EReal) ≤ max x (-(n : EReal)) := le_max_right _ _
  have hne : max x (-(n : EReal)) ≠ ⊤ := max_ne_top hx (by simp)
  have hnb : max x (-(n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hm
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hne hnb]
  simp only [EReal.coe_neg, EReal.coe_natCast]; exact hm

/-- `x ≤ potentialTrunc n x` (as `EReal`) for `x ≠ ⊤`. -/
theorem le_trunc {x : EReal} (hx : x ≠ ⊤) (n : ℕ) : x ≤ ((potentialTrunc n x : ℝ) : EReal) := by
  unfold potentialTrunc
  have hm : -(n : EReal) ≤ max x (-(n : EReal)) := le_max_right _ _
  have hne : max x (-(n : EReal)) ≠ ⊤ := max_ne_top hx (by simp)
  have hnb : max x (-(n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hm
  rw [EReal.coe_toReal hne hnb]
  exact le_max_left _ _


/-- `x ≤ B` ⇒ `r x ≤ r B` in `EReal`, for `r > 0`. -/
theorem ereal_mul_le {r : ℝ} (hr : 0 < r) {X : EReal} {B : ℝ} (h : X ≤ (B : EReal)) :
    (r : EReal) * X ≤ ((r * B : ℝ) : EReal) := by
  induction X using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hr]; exact bot_le
  | coe x =>
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
    exact mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp h) hr.le
  | top => exact absurd h (by simp)

/-- `potentialTrunc n X ≤ Y` when `X ≤ Y` and `-n ≤ Y`. -/
theorem trunc_le {X : EReal} (hX : X ≠ ⊤) {Y : ℝ} (h : X ≤ (Y : EReal)) (n : ℕ) (hn : -(n : ℝ) ≤ Y) : potentialTrunc n X ≤ Y := by
  have hn' : -(n : EReal) ≤ (Y : EReal) := by
    rw [show (-(n : EReal)) = ((-(n : ℝ) : ℝ) : EReal) by simp]; exact EReal.coe_le_coe_iff.mpr hn
  have hm : max X (-(n : EReal)) ≤ (Y : EReal) := max_le h hn'
  have hne : max X (-(n : EReal)) ≠ ⊤ := max_ne_top hX (by simp)
  have hnb : max X (-(n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (le_max_right _ _)
  unfold potentialTrunc
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hne hnb]
  exact hm



theorem trunc_coe (n : ℕ) (x : ℝ) : potentialTrunc n (x : EReal) = max x (-(n : ℝ)) := by
  unfold potentialTrunc
  have hn : (-(n : EReal)) = ((-(n : ℝ) : ℝ) : EReal) := by simp
  rcases le_total x (-(n : ℝ)) with h | h
  · have h' : (x : EReal) ≤ -(n : EReal) := by rw [hn]; exact EReal.coe_le_coe_iff.mpr h
    rw [max_eq_right h', max_eq_right h, hn, EReal.toReal_coe]
  · have h' : -(n : EReal) ≤ (x : EReal) := by rw [hn]; exact EReal.coe_le_coe_iff.mpr h
    rw [max_eq_left h', max_eq_left h, EReal.toReal_coe]

end GKSharp.SubharmonicBasic
