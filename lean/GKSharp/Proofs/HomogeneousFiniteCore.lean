/- finite angular values from sector comparison, with no q<1 restriction.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ObstacleMinimum
import GKSharp.Proofs.SubharmonicBasic

open Real Metric Set Filter Topology
namespace GKSharp.ProfileCore

/-- The ordinary angular sector comparison conclusion, kept as an internal modular interface. -/
def AngularComparison (q : ℝ) (V : ℂ → EReal) : Prop :=
  ∀ {x y a b : ℝ}, x < y → q * (y - x) < π →
    V (unitPoint x) ≤ (a : EReal) → V (unitPoint y) ≤ (b : EReal) →
    ∀ t : ℝ, x < t → t < y → V (unitPoint t) ≤
      (((a * sin (q * (y - t)) + b * sin (q * (t - x))) / sin (q * (y - x)) : ℝ) : EReal)

theorem exists_bound_sphere {V : ℂ → EReal} (hV : IsSubharmonic V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ sphere (0 : ℂ) 1, V z ≤ B := by
  obtain ⟨z0, hz0, hmax⟩ := (hV.2.1.upperSemicontinuousOn (sphere (0 : ℂ) 1)).exists_isMaxOn
    ⟨1, by simp⟩ (isCompact_sphere 0 1)
  refine ⟨max (V z0).toReal 0, le_max_right _ _, fun z hz => ?_⟩
  refine le_trans (hmax hz) ?_
  induction h : V z0 using EReal.rec with
  | bot => exact bot_le
  | coe v => simp
  | top => exact absurd h (hV.1 z0)

theorem unitPoint_mem_sphere (t : ℝ) : unitPoint t ∈ sphere (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm]
  exact norm_unitPoint t

theorem sin_len_pos {q x y : ℝ} (hq : 0 < q) (hxy : x < y) (hlen : q * (y - x) < π) :
    0 < sin (q * (y - x)) := sin_pos_of_pos_of_lt_pi (mul_pos hq (sub_pos.mpr hxy)) hlen

theorem bot_spread_right {q : ℝ} (hq : 0 < q) {V : ℂ → EReal} (hV : IsSubharmonic V)
    (hCmp : AngularComparison q V) {t0 : ℝ} (hbot : V (unitPoint t0) = ⊥)
    {t : ℝ} (ht : t0 < t) (ht' : t < t0 + π / q) : V (unitPoint t) = ⊥ := by
  obtain ⟨Bv, _, hBv⟩ := exists_bound_sphere hV
  let y := (t + (t0 + π / q)) / 2
  have hty : t < y := by dsimp [y]; linarith
  have hlen : q * (y - t0) < π := by
    have : y - t0 < π / q := by dsimp [y]; linarith
    rwa [lt_div_iff₀ hq, mul_comm] at this
  have hs1 : 0 < sin (q * (y - t)) := sin_len_pos hq hty (by nlinarith)
  have hs2 : 0 < sin (q * (y - t0)) := sin_len_pos hq (ht.trans hty) hlen
  rw [EReal.eq_bot_iff_forall_lt]
  intro M
  let N := ((M - 1) * sin (q * (y - t0)) - Bv * sin (q * (t - t0))) / sin (q * (y - t))
  have h := hCmp (ht.trans hty) hlen (a := N) (b := Bv) (by rw [hbot]; exact bot_le)
    (hBv _ (unitPoint_mem_sphere y)) t ht hty
  have heq : (N * sin (q * (y - t)) + Bv * sin (q * (t - t0))) / sin (q * (y - t0)) = M - 1 := by
    dsimp [N]
    field_simp
    ring
  rw [heq] at h
  exact lt_of_le_of_lt h (EReal.coe_lt_coe_iff.mpr (by linarith))

theorem bot_spread_left {q : ℝ} (hq : 0 < q) {V : ℂ → EReal} (hV : IsSubharmonic V)
    (hCmp : AngularComparison q V) {t0 : ℝ} (hbot : V (unitPoint t0) = ⊥)
    {t : ℝ} (ht : t0 - π / q < t) (ht' : t < t0) : V (unitPoint t) = ⊥ := by
  obtain ⟨Bv, _, hBv⟩ := exists_bound_sphere hV
  let x := ((t0 - π / q) + t) / 2
  have hxt : x < t := by dsimp [x]; linarith
  have hlen : q * (t0 - x) < π := by
    have : t0 - x < π / q := by dsimp [x]; linarith
    rwa [lt_div_iff₀ hq, mul_comm] at this
  have hs1 : 0 < sin (q * (t - x)) := sin_len_pos hq hxt (by nlinarith)
  have hs2 : 0 < sin (q * (t0 - x)) := sin_len_pos hq (hxt.trans ht') hlen
  rw [EReal.eq_bot_iff_forall_lt]
  intro M
  let N := ((M - 1) * sin (q * (t0 - x)) - Bv * sin (q * (t0 - t))) / sin (q * (t - x))
  have h := hCmp (hxt.trans ht') hlen (a := Bv) (b := N) (hBv _ (unitPoint_mem_sphere x))
    (by rw [hbot]; exact bot_le) t hxt ht'
  have heq : (Bv * sin (q * (t0 - t)) + N * sin (q * (t - x))) / sin (q * (t0 - x)) = M - 1 := by
    dsimp [N]
    field_simp
    ring
  rw [heq] at h
  exact lt_of_le_of_lt h (EReal.coe_lt_coe_iff.mpr (by linarith))

/-- The bottom-value set is clopen using a uniform spreading radius; connectedness replaces the old q<1 shortcut. -/
theorem homogeneous_finite_of_comparison {q : ℝ} (hq : 0 < q) {V : ℂ → EReal}
    (hV : IsSubharmonic V) (h0 : 0 ≤ V 0)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z)
    (hCmp : AngularComparison q V) : ∀ t : ℝ, V (unitPoint t) ≠ ⊥ := by
  intro t0 hbot
  let S : Set ℝ := {t | V (unitPoint t) = ⊥}
  have hδ : 0 < π / q := div_pos pi_pos hq
  have hlocal : ∀ x ∈ S, ∀ y : ℝ, |y - x| < π / q → y ∈ S := by
    intro x hx y hy
    rcases lt_trichotomy y x with h | rfl | h
    · exact bot_spread_left hq hV hCmp hx (by linarith [(abs_lt.mp hy).1]) h
    · exact hx
    · exact bot_spread_right hq hV hCmp hx h (by linarith [(abs_lt.mp hy).2])
  have ho : IsOpen S := Metric.isOpen_iff.mpr (by
    intro x hx
    refine ⟨π / q, hδ, fun y hy => hlocal x hx y ?_⟩
    simpa only [Metric.mem_ball, Real.dist_eq] using hy)
  have hco : IsOpen Sᶜ := Metric.isOpen_iff.mpr (by
    intro x hx
    refine ⟨π / q, hδ, fun y hy hys => hx (hlocal y hys x ?_)⟩
    simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hy)
  have hSuniv : S = univ := IsClopen.eq_univ ⟨isOpen_compl_iff.mp hco, ho⟩ ⟨t0, hbot⟩
  have hcirc : ∀ t : ℝ, V (unitPoint t) = ⊥ := by
    intro t
    have : t ∈ S := by rw [hSuniv]; trivial
    exact this
  have hoff : ∀ z : ℂ, z ≠ 0 → V z = ⊥ := by
    intro z hz
    have hrep : z = (‖z‖ : ℂ) * unitPoint (Complex.arg z) := (Complex.norm_mul_exp_arg_mul_I z).symm
    rw [hrep, hhom _ _ (norm_pos_iff.mpr hz), hcirc,
      EReal.coe_mul_bot_of_pos (rpow_pos_of_pos (norm_pos_iff.mpr hz) q)]
  have hsub := hV.2.2 1 0 1 one_pos
  have hconst : circleAverage (fun z => potentialTrunc 1 (V z)) 0 1 = -1 := by
    have heq : Set.EqOn (fun z => potentialTrunc 1 (V z)) (fun _ => (-1 : ℝ)) (sphere 0 |1|) := by
      intro z hz
      have hz0 : z ≠ 0 := by rintro rfl; simp at hz
      simp only [hoff z hz0, potentialTrunc, max_eq_right (bot_le : (⊥ : EReal) ≤ -((1 : ℕ) : EReal))]
      simp
    rw [circleAverage_congr_sphere heq, circleAverage_const]
  have hpos : 0 ≤ potentialTrunc 1 (V 0) := by
    have hm : max (V 0) (-((1 : ℕ) : EReal)) = V 0 := max_eq_left (le_trans (by simp) h0)
    unfold potentialTrunc
    rw [hm]
    exact EReal.toReal_nonneg h0
  rw [hconst] at hsub
  linarith

/-- Positive homogeneity and a nonnegative value at0 force the actual value at0 to be0. -/
theorem homogeneous_zero {q : ℝ} (hq : 0 < q) {V : ℂ → EReal} (hVt : ∀ z, V z ≠ ⊤)
    (h0 : 0 ≤ V 0)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z) :
    V 0 = 0 := by
  have h := hhom 2 0 (by norm_num)
  rw [mul_zero] at h
  induction h' : V 0 using EReal.rec with
  | bot => simp [h'] at h0
  | coe v =>
    rw [h', ← EReal.coe_mul, EReal.coe_eq_coe_iff] at h
    have h2 : (2 : ℝ) ^ q - 1 ≠ 0 := by
      have : (1 : ℝ) < 2 ^ q := Real.one_lt_rpow (by norm_num) hq
      linarith
    have h3 : ((2 : ℝ) ^ q - 1) * v = 0 := by rw [sub_mul, one_mul]; linarith
    have hv : v = 0 := (mul_eq_zero.mp h3).resolve_left h2
    simp [hv]
  | top => exact absurd h' (hVt 0)

/-- Build the actual real angular profile, including the value at0; continuity is supplied by the separate QSubtrig theorem. -/
theorem profile_of_comparison {q : ℝ} (hq : 0 < q) {V : ℂ → EReal}
    (hV : IsSubharmonic V) (h0 : 0 ≤ V 0)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z)
    (hCmp : AngularComparison q V) :
    ∃ phi : ℝ → ℝ, QSubtrig q phi ∧
      (∀ z : ℂ, V z = (angularPotential q phi z : EReal)) ∧
      IsSubharmonic (fun z => (angularPotential q phi z : EReal)) := by
  have hfin := homogeneous_finite_of_comparison hq hV h0 hhom hCmp
  let phi : ℝ → ℝ := fun t => (V (unitPoint t)).toReal
  have hcoe : ∀ t : ℝ, V (unitPoint t) = ((phi t : ℝ) : EReal) :=
    fun t => (EReal.coe_toReal (hV.1 _) (hfin t)).symm
  have hrep : ∀ z : ℂ, V z = (angularPotential q phi z : EReal) := by
    intro z
    by_cases hz : z = 0
    · subst z
      rw [homogeneous_zero hq hV.1 h0 hhom]
      simp [angularPotential, Real.zero_rpow hq.ne']
    · have hzrep : z = (‖z‖ : ℂ) * unitPoint (Complex.arg z) := (Complex.norm_mul_exp_arg_mul_I z).symm
      change V z = ((‖z‖ ^ q * phi (Complex.arg z) : ℝ) : EReal)
      conv_lhs => rw [hzrep, hhom _ _ (norm_pos_iff.mpr hz), hcoe]
      rw [← EReal.coe_mul]
  have hfull : IsSubharmonic (fun z => (angularPotential q phi z : EReal)) := by
    have heq : (fun z => (angularPotential q phi z : EReal)) = V := funext fun z => (hrep z).symm
    rw [heq]
    exact hV
  refine ⟨phi, ⟨?_, ?_⟩, hrep, hfull⟩
  · intro t
    dsimp [phi]
    rw [unitPoint_periodic t]
  · exact ⟨fun z _ => hfull.1 z, hfull.2.1.upperSemicontinuousOn _,
      fun n c r hr _ => hfull.2.2 n c r hr⟩

end GKSharp.ProfileCore

#print axioms GKSharp.ProfileCore.homogeneous_finite_of_comparison
#print axioms GKSharp.ProfileCore.profile_of_comparison
