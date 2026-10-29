/-
GKSharp/Proofs/ContactHarmonic.lean — paper 019 (sec4b_failure.tex l. 39-43): row `contact_harmonic_derivatives`,
with the exact type of the statement draft (v1.00), for the actual canonical objects.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Route: `log‖e^{y+it} + c‖ = ½ log Q_c`, `Q_c = e^{2y} + 2c e^y cos t + c²`, so explicit slice partials (generic
`SliceDerivs` calculus: closed under constants, sums, `log`, `exp(p·)`, transported through `EventuallyEq`). Near the
contact (`Q_1, Q_λ > 0`): `L = log C - χ + log‖ζ+1‖` and `G = C^p e^{p log‖ζ+1‖} - e^{pχ}`. At the contact
(`e^y = r`, `cos t = -cs`, `sin t = sn`): `C² Q_1 = Q_λ` (contact_gk_radius + B12) gives `L = 0` and `C^p e^{p a} = P`;
`cs(r²+λ) = (1+λ) r` gives `L_y = 0`; `Q_yy Q - Q_y² + Q_tt Q - Q_t² = 0` (sin² + cos² = 1) gives `L_tt = -L_yy`;
the four G identities are then algebra.
-/
import GKSharp.Defs.ThresholdAnalysis
import GKSharp.Proofs.ContactScalar
import GKSharp.Proofs.ContactRay

open Set Filter Topology

namespace GKSharp

open Threshold

namespace ContactCalc

/-- Closed-form slice partials of a two-variable function on a region `S`. -/
def SliceDerivs (S : ℝ → ℝ → Prop) (f fy ft fyy ftt fyt : ℝ → ℝ → ℝ) : Prop :=
  ∀ y t, S y t →
    HasDerivAt (fun x => f x t) (fy y t) y ∧ HasDerivAt (fun s => f y s) (ft y t) t ∧
    HasDerivAt (fun x => fy x t) (fyy y t) y ∧ HasDerivAt (fun s => ft y s) (ftt y t) t ∧
    HasDerivAt (fun s => fy y s) (fyt y t) t

/-- `S` is open in each variable separately. -/
def SliceOpen (S : ℝ → ℝ → Prop) : Prop :=
  ∀ y t, S y t → (∀ᶠ x in 𝓝 y, S x t) ∧ (∀ᶠ s in 𝓝 t, S y s)

lemma values {S : ℝ → ℝ → Prop} {f fy ft fyy ftt fyt : ℝ → ℝ → ℝ} (hS : SliceOpen S)
    (hf : SliceDerivs S f fy ft fyy ftt fyt) {y t : ℝ} (hyt : S y t) :
    dy f y t = fy y t ∧ dt f y t = ft y t ∧ dyy f y t = fyy y t ∧ dtt f y t = ftt y t ∧
      dty f y t = fyt y t := by
  have hdy : ∀ y t, S y t → dy f y t = fy y t := fun y t h => (hf y t h).1.deriv
  have hdt : ∀ y t, S y t → dt f y t = ft y t := fun y t h => (hf y t h).2.1.deriv
  obtain ⟨hSx, hSs⟩ := hS y t hyt
  obtain ⟨-, -, h3, h4, h5⟩ := hf y t hyt
  refine ⟨hdy y t hyt, hdt y t hyt, ?_, ?_, ?_⟩
  · show deriv (fun x => dy f x t) y = fyy y t
    rw [Filter.EventuallyEq.deriv_eq (hSx.mono fun x hx => hdy x t hx)]
    exact h3.deriv
  · show deriv (fun s => dt f y s) t = ftt y t
    rw [Filter.EventuallyEq.deriv_eq (hSs.mono fun s hs => hdt y s hs)]
    exact h4.deriv
  · show deriv (fun s => dy f y s) t = fyt y t
    rw [Filter.EventuallyEq.deriv_eq (hSs.mono fun s hs => hdy y s hs)]
    exact h5.deriv

lemma congr {S : ℝ → ℝ → Prop} {f g fy ft fyy ftt fyt : ℝ → ℝ → ℝ} (hS : SliceOpen S)
    (heq : ∀ y t, S y t → f y t = g y t) (hg : SliceDerivs S g fy ft fyy ftt fyt) :
    SliceDerivs S f fy ft fyy ftt fyt := by
  intro y t hyt
  obtain ⟨h1, h2, h3, h4, h5⟩ := hg y t hyt
  obtain ⟨hSx, hSs⟩ := hS y t hyt
  exact ⟨h1.congr_of_eventuallyEq (hSx.mono fun x hx => heq x t hx),
    h2.congr_of_eventuallyEq (hSs.mono fun s hs => heq y s hs), h3, h4, h5⟩

lemma mono {S T : ℝ → ℝ → Prop} {f fy ft fyy ftt fyt : ℝ → ℝ → ℝ} (hST : ∀ y t, T y t → S y t)
    (hf : SliceDerivs S f fy ft fyy ftt fyt) : SliceDerivs T f fy ft fyy ftt fyt :=
  fun y t h => hf y t (hST y t h)

lemma add {S : ℝ → ℝ → Prop} {f fy ft fyy ftt fyt g gy gt gyy gtt gyt : ℝ → ℝ → ℝ}
    (hf : SliceDerivs S f fy ft fyy ftt fyt) (hg : SliceDerivs S g gy gt gyy gtt gyt) :
    SliceDerivs S (fun y t => f y t + g y t) (fun y t => fy y t + gy y t) (fun y t => ft y t + gt y t)
      (fun y t => fyy y t + gyy y t) (fun y t => ftt y t + gtt y t) (fun y t => fyt y t + gyt y t) := by
  intro y t hyt
  obtain ⟨f1, f2, f3, f4, f5⟩ := hf y t hyt
  obtain ⟨g1, g2, g3, g4, g5⟩ := hg y t hyt
  exact ⟨f1.add g1, f2.add g2, f3.add g3, f4.add g4, f5.add g5⟩

lemma const_mul (a : ℝ) {S : ℝ → ℝ → Prop} {f fy ft fyy ftt fyt : ℝ → ℝ → ℝ}
    (hf : SliceDerivs S f fy ft fyy ftt fyt) :
    SliceDerivs S (fun y t => a * f y t) (fun y t => a * fy y t) (fun y t => a * ft y t)
      (fun y t => a * fyy y t) (fun y t => a * ftt y t) (fun y t => a * fyt y t) := by
  intro y t hyt
  obtain ⟨f1, f2, f3, f4, f5⟩ := hf y t hyt
  exact ⟨f1.const_mul a, f2.const_mul a, f3.const_mul a, f4.const_mul a, f5.const_mul a⟩

lemma const_add (k : ℝ) {S : ℝ → ℝ → Prop} {f fy ft fyy ftt fyt : ℝ → ℝ → ℝ}
    (hf : SliceDerivs S f fy ft fyy ftt fyt) :
    SliceDerivs S (fun y t => k + f y t) fy ft fyy ftt fyt := by
  intro y t hyt
  obtain ⟨f1, f2, f3, f4, f5⟩ := hf y t hyt
  exact ⟨f1.const_add k, f2.const_add k, f3, f4, f5⟩

lemma exp_mul (p : ℝ) {S : ℝ → ℝ → Prop} {f fy ft fyy ftt fyt : ℝ → ℝ → ℝ}
    (hf : SliceDerivs S f fy ft fyy ftt fyt) :
    SliceDerivs S (fun y t => Real.exp (p * f y t)) (fun y t => p * fy y t * Real.exp (p * f y t))
      (fun y t => p * ft y t * Real.exp (p * f y t))
      (fun y t => (p * fyy y t + p ^ 2 * fy y t ^ 2) * Real.exp (p * f y t))
      (fun y t => (p * ftt y t + p ^ 2 * ft y t ^ 2) * Real.exp (p * f y t))
      (fun y t => (p * fyt y t + p ^ 2 * fy y t * ft y t) * Real.exp (p * f y t)) := by
  intro y t hyt
  obtain ⟨f1, f2, f3, f4, f5⟩ := hf y t hyt
  have e1 := (f1.const_mul p).exp
  have e2 := (f2.const_mul p).exp
  refine ⟨e1.congr_deriv (by ring), e2.congr_deriv (by ring), ((f3.const_mul p).mul e1).congr_deriv (by ring),
    ((f4.const_mul p).mul e2).congr_deriv (by ring), ((f5.const_mul p).mul e2).congr_deriv (by ring)⟩

lemma log {S : ℝ → ℝ → Prop} {f fy ft fyy ftt fyt : ℝ → ℝ → ℝ} (hpos : ∀ y t, S y t → 0 < f y t)
    (hf : SliceDerivs S f fy ft fyy ftt fyt) :
    SliceDerivs S (fun y t => Real.log (f y t)) (fun y t => fy y t / f y t) (fun y t => ft y t / f y t)
      (fun y t => (fyy y t * f y t - fy y t ^ 2) / f y t ^ 2)
      (fun y t => (ftt y t * f y t - ft y t ^ 2) / f y t ^ 2)
      (fun y t => (fyt y t * f y t - fy y t * ft y t) / f y t ^ 2) := by
  intro y t hyt
  obtain ⟨f1, f2, f3, f4, f5⟩ := hf y t hyt
  have hne := (hpos y t hyt).ne'
  exact ⟨f1.log hne, f2.log hne, (f3.div f1 hne).congr_deriv (by ring), (f4.div f2 hne).congr_deriv (by ring),
    (f5.div f2 hne).congr_deriv (by ring)⟩

/-- `‖e^{y+it} + c‖² = Q c y t`. -/
noncomputable def Q (c y t : ℝ) : ℝ := Real.exp y ^ 2 + 2 * c * Real.exp y * Real.cos t + c ^ 2
noncomputable def Qy (c y t : ℝ) : ℝ := 2 * Real.exp y ^ 2 + 2 * c * Real.exp y * Real.cos t
noncomputable def Qt (c y t : ℝ) : ℝ := -(2 * c * Real.exp y * Real.sin t)
noncomputable def Qyy (c y t : ℝ) : ℝ := 4 * Real.exp y ^ 2 + 2 * c * Real.exp y * Real.cos t
noncomputable def Qtt (c y t : ℝ) : ℝ := -(2 * c * Real.exp y * Real.cos t)
noncomputable def Qyt (c y t : ℝ) : ℝ := -(2 * c * Real.exp y * Real.sin t)

lemma Q_derivs (c : ℝ) : SliceDerivs (fun _ _ => True) (Q c) (Qy c) (Qt c) (Qyy c) (Qtt c) (Qyt c) := by
  intro y t _
  have hE := Real.hasDerivAt_exp y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (((hE.pow 2).add ((hE.const_mul (2 * c)).mul_const (Real.cos t))).add_const (c ^ 2)).congr_deriv
      (by simp only [Qy]; push_cast; ring)
  · exact ((((Real.hasDerivAt_cos t).const_mul (2 * c * Real.exp y)).const_add (Real.exp y ^ 2)).add_const
      (c ^ 2)).congr_deriv (by simp only [Qt]; ring)
  · exact (((hE.pow 2).const_mul 2).add ((hE.const_mul (2 * c)).mul_const (Real.cos t))).congr_deriv
      (by simp only [Qyy]; push_cast; ring)
  · exact ((Real.hasDerivAt_sin t).const_mul (2 * c * Real.exp y)).neg.congr_deriv (by simp only [Qtt])
  · exact (((Real.hasDerivAt_cos t).const_mul (2 * c * Real.exp y)).const_add
      (2 * Real.exp y ^ 2)).congr_deriv (by simp only [Qyt]; ring)

lemma Q_sos (c y t : ℝ) : Q c y t = (Real.exp y * Real.cos t + c) ^ 2 + (Real.exp y * Real.sin t) ^ 2 := by
  unfold Q
  linear_combination (-(Real.exp y) ^ 2) * Real.sin_sq_add_cos_sq t

/-- Harmonicity of `log Q`: `(Q_yy Q - Q_y²) + (Q_tt Q - Q_t²) = 0`. -/
lemma Q_harm (c y t : ℝ) :
    Qyy c y t * Q c y t - Qy c y t ^ 2 + (Qtt c y t * Q c y t - Qt c y t ^ 2) = 0 := by
  unfold Qyy Q Qy Qtt Qt
  linear_combination (-4 * c ^ 2 * Real.exp y ^ 2) * Real.sin_sq_add_cos_sq t

lemma norm_sq_zeta_add (c y t : ℝ) : ‖zeta y t + (c : ℂ)‖ ^ 2 = Q c y t := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [zeta, Complex.exp_re, Complex.exp_im]
  unfold Q
  linear_combination (Real.exp y ^ 2) * Real.sin_sq_add_cos_sq t

lemma norm_pos_of_Q {c y t : ℝ} (h : 0 < Q c y t) : 0 < ‖zeta y t + (c : ℂ)‖ := by
  have hsq := norm_sq_zeta_add c y t
  exact lt_of_le_of_ne (norm_nonneg _) (fun h0 => by rw [← h0] at hsq; nlinarith)

lemma chi_eq (c y t : ℝ) : chi c y t = 1 / 2 * Real.log (Q c y t) := by
  rw [chi, ← norm_sq_zeta_add, Real.log_pow]
  push_cast
  ring

lemma Q_open (c : ℝ) : SliceOpen (fun y t => 0 < Q c y t) := by
  intro y t h
  have hx : Continuous fun x => Q c x t := by unfold Q; fun_prop
  have hs : Continuous fun s => Q c y s := by unfold Q; fun_prop
  exact ⟨(hx.tendsto y).eventually (lt_mem_nhds h), (hs.tendsto t).eventually (lt_mem_nhds h)⟩

/-- Slice partials of `χ_c = log‖ζ + c‖` where `Q_c > 0`. -/
lemma chi_derivs (c : ℝ) :
    SliceDerivs (fun y t => 0 < Q c y t) (chi c)
      (fun y t => 1 / 2 * (Qy c y t / Q c y t)) (fun y t => 1 / 2 * (Qt c y t / Q c y t))
      (fun y t => 1 / 2 * ((Qyy c y t * Q c y t - Qy c y t ^ 2) / Q c y t ^ 2))
      (fun y t => 1 / 2 * ((Qtt c y t * Q c y t - Qt c y t ^ 2) / Q c y t ^ 2))
      (fun y t => 1 / 2 * ((Qyt c y t * Q c y t - Qy c y t * Qt c y t) / Q c y t ^ 2)) :=
  congr (Q_open c) (fun y t _ => chi_eq c y t)
    (const_mul (1 / 2) (log (fun _ _ h => h) (mono (fun _ _ _ => trivial) (Q_derivs c))))

end ContactCalc

open ContactCalc in
/-- B:39–43, row `contact_harmonic_derivatives`: actual contact values, harmonicity and the four G derivatives. -/
theorem contact_harmonic_derivatives_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let t := theta p
    let LL := logGap p lam
    let PP := weightP p lam y t
    let GG := fun y t => bigG p (gk p lam) lam (zeta y t)
    LL y t = 0 ∧ dy LL y t = 0 ∧ dtt LL y t = -dyy LL y t ∧
    dt GG y t = p * PP * dt LL y t ∧
    dyy GG y t = p * PP * dyy LL y t ∧
    dty GG y t = p * PP * (dty LL y t + p * dy (chi lam) y t * dt LL y t) ∧
    dtt GG y t = p * PP * (dtt LL y t + p * dt LL y t ^ 2 +
      2 * p * dt (chi lam) y t * dt LL y t) := by
  dsimp only
  -- contact data
  obtain ⟨hr1, -, -, -⟩ := contact_root_properties hp hp2 hlam
  obtain ⟨hcs, -, -⟩ := contact_rational_identities_proved p lam hp hp2 hlam
  have hgk := (contact_gk_radius p lam hp hp2 hlam).2
  have hy0 : Real.exp (yContact p lam) = rContact p lam := by
    unfold yContact
    exact Real.exp_log (by linarith)
  obtain ⟨r, hr⟩ : ∃ x, x = rContact p lam := ⟨_, rfl⟩
  rw [← hr] at hr1 hcs hgk hy0
  have hcos : Real.cos (theta p) = -cs p := by unfold theta cs; ring
  have hsin : Real.sin (theta p) = sn p := rfl
  have hsn : 0 < sn p :=
    Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hp)
  have hC1 : 1 < gk p lam :=
    lt_of_le_of_lt (le_max_left _ _) (gk_gt_max hp (ne_of_lt hp2) (ρ := (lam : ℂ)) (fun hh => by
      have : lam = 1 := by exact_mod_cast hh
      linarith [hlam.2]))
  have hC0 : 0 < gk p lam := by linarith
  have hQpos : ∀ c, 0 < Q c (yContact p lam) (theta p) := by
    intro c
    rw [Q_sos, hy0, hsin]
    have hrs : 0 < r * sn p := mul_pos (by linarith) hsn
    nlinarith [sq_nonneg (r * Real.cos (theta p) + c), sq_pos_of_pos hrs]
  have hS0 : 0 < Q 1 (yContact p lam) (theta p) ∧ 0 < Q lam (yContact p lam) (theta p) :=
    ⟨hQpos 1, hQpos lam⟩
  -- the contact algebra: `C² Q_1 = Q_λ` and `Q_y,1 Q_λ = Q_y,λ Q_1`
  have hr2 : r ^ 2 - 1 ≠ 0 := (show (0 : ℝ) < r ^ 2 - 1 by nlinarith).ne'
  have hden : r ^ 2 + lam ≠ 0 := (show (0 : ℝ) < r ^ 2 + lam by nlinarith [hlam.1]).ne'
  have h1 : gk p lam ^ 2 * (r ^ 2 - 1) = r ^ 2 - lam ^ 2 := by rw [hgk]; field_simp
  have h2 : cs p * (r ^ 2 + lam) = (1 + lam) * r := by rw [hcs]; field_simp
  have hK1 : gk p lam ^ 2 * Q 1 (yContact p lam) (theta p) = Q lam (yContact p lam) (theta p) := by
    have hmul : (r ^ 2 + lam) * (gk p lam ^ 2 * Q 1 (yContact p lam) (theta p) -
        Q lam (yContact p lam) (theta p)) = 0 := by
      unfold Q
      rw [hy0, hcos]
      linear_combination (r ^ 2 - lam) * h1 + 2 * r * (lam - gk p lam ^ 2) * h2
    rcases mul_eq_zero.1 hmul with h | h
    · exact absurd h hden
    · linarith
  have hK2 : Qy 1 (yContact p lam) (theta p) * Q lam (yContact p lam) (theta p) =
      Qy lam (yContact p lam) (theta p) * Q 1 (yContact p lam) (theta p) := by
    unfold Qy Q
    rw [hy0, hcos]
    linear_combination (2 * r * (1 - lam)) * h2
  have hFy : 1 / 2 * (Qy 1 (yContact p lam) (theta p) / Q 1 (yContact p lam) (theta p)) =
      1 / 2 * (Qy lam (yContact p lam) (theta p) / Q lam (yContact p lam) (theta p)) := by
    have hq : Qy 1 (yContact p lam) (theta p) / Q 1 (yContact p lam) (theta p) =
        Qy lam (yContact p lam) (theta p) / Q lam (yContact p lam) (theta p) := by
      rw [div_eq_div_iff (hQpos 1).ne' (hQpos lam).ne']
      linear_combination hK2
    rw [hq]
  have hH : ∀ c, 1 / 2 * ((Qyy c (yContact p lam) (theta p) * Q c (yContact p lam) (theta p) -
        Qy c (yContact p lam) (theta p) ^ 2) / Q c (yContact p lam) (theta p) ^ 2) +
      1 / 2 * ((Qtt c (yContact p lam) (theta p) * Q c (yContact p lam) (theta p) -
        Qt c (yContact p lam) (theta p) ^ 2) / Q c (yContact p lam) (theta p) ^ 2) = 0 := by
    intro c
    have hh := Q_harm c (yContact p lam) (theta p)
    calc _ = 1 / 2 * ((Qyy c (yContact p lam) (theta p) * Q c (yContact p lam) (theta p) -
          Qy c (yContact p lam) (theta p) ^ 2 + (Qtt c (yContact p lam) (theta p) *
          Q c (yContact p lam) (theta p) - Qt c (yContact p lam) (theta p) ^ 2)) /
          Q c (yContact p lam) (theta p) ^ 2) := by ring
      _ = 0 := by rw [hh]; simp
  have hlogK : Real.log (Q lam (yContact p lam) (theta p)) =
      2 * Real.log (gk p lam) + Real.log (Q 1 (yContact p lam) (theta p)) := by
    rw [← hK1, Real.log_mul (pow_ne_zero 2 hC0.ne') (hQpos 1).ne', Real.log_pow]
    push_cast
    ring
  have hchi1 := chi_eq 1 (yContact p lam) (theta p)
  have hchil := chi_eq lam (yContact p lam) (theta p)
  have hB : gk p lam ^ p * Real.exp (p * chi 1 (yContact p lam) (theta p)) =
      Real.exp (p * chi lam (yContact p lam) (theta p)) := by
    have hdiff : chi lam (yContact p lam) (theta p) = Real.log (gk p lam) + chi 1 (yContact p lam) (theta p) := by
      rw [hchi1, hchil, hlogK]
      ring
    rw [hdiff, Real.rpow_def_of_pos hC0, mul_add, Real.exp_add, mul_comm (Real.log (gk p lam)) p]
  -- the region `Q_1 > 0, Q_λ > 0` and the slice partials there
  have hSopen : SliceOpen (fun y t => 0 < Q 1 y t ∧ 0 < Q lam y t) := by
    intro y t h
    obtain ⟨a1, a2⟩ := Q_open 1 y t h.1
    obtain ⟨b1, b2⟩ := Q_open lam y t h.2
    exact ⟨a1.and b1, a2.and b2⟩
  have hc1 := mono (T := fun y t => 0 < Q 1 y t ∧ 0 < Q lam y t) (fun _ _ h => h.1) (chi_derivs 1)
  have hcl := mono (T := fun y t => 0 < Q 1 y t ∧ 0 < Q lam y t) (fun _ _ h => h.2) (chi_derivs lam)
  have heqL : ∀ y t, (0 < Q 1 y t ∧ 0 < Q lam y t) →
      logGap p lam y t = Real.log (gk p lam) + (-1 * chi lam y t + chi 1 y t) := by
    intro y t h
    have h1 := norm_pos_of_Q h.1
    have hl := norm_pos_of_Q h.2
    rw [Complex.ofReal_one] at h1
    simp only [logGap, mobContact, chi, Complex.ofReal_one, norm_div]
    rw [Real.log_div hl.ne' h1.ne']
    ring
  have heqG : ∀ y t, (0 < Q 1 y t ∧ 0 < Q lam y t) →
      bigG p (gk p lam) lam (zeta y t) =
        gk p lam ^ p * Real.exp (p * chi 1 y t) + -1 * Real.exp (p * chi lam y t) := by
    intro y t h
    have h1 := norm_pos_of_Q h.1
    have hl := norm_pos_of_Q h.2
    rw [Complex.ofReal_one] at h1
    simp only [bigG, GKSharp.obstacleG, chi, Complex.ofReal_one]
    rw [add_comm (1 : ℂ), add_comm ((lam : ℝ) : ℂ), Real.rpow_def_of_pos h1, Real.rpow_def_of_pos hl,
      mul_comm (Real.log ‖zeta y t + 1‖) p, mul_comm (Real.log ‖zeta y t + (lam : ℂ)‖) p]
    ring
  have hLval : logGap p lam (yContact p lam) (theta p) = 0 := by
    rw [heqL _ _ hS0, hchi1, hchil, hlogK]
    ring
  have hLd := congr hSopen heqL (const_add (Real.log (gk p lam)) (add (const_mul (-1) hcl) hc1))
  have hGd := congr hSopen heqG
    (add (const_mul (gk p lam ^ p) (exp_mul p hc1)) (const_mul (-1) (exp_mul p hcl)))
  obtain ⟨hL1, hL2, hL3, hL4, hL5⟩ := values hSopen hLd hS0
  obtain ⟨-, hG2, hG3, hG4, hG5⟩ := values hSopen hGd hS0
  obtain ⟨hX1, hX2, -, -, -⟩ := values (Q_open lam) (chi_derivs lam) (hQpos lam)
  unfold weightP
  rw [hL2, hL3, hL4, hL5, hG2, hG3, hG4, hG5, hX1, hX2, hL1]
  set A := Real.exp (p * chi 1 (yContact p lam) (theta p))
  set B := Real.exp (p * chi lam (yContact p lam) (theta p))
  set ay1 := 1 / 2 * (Qy 1 (yContact p lam) (theta p) / Q 1 (yContact p lam) (theta p))
  set ayl := 1 / 2 * (Qy lam (yContact p lam) (theta p) / Q lam (yContact p lam) (theta p))
  set at1 := 1 / 2 * (Qt 1 (yContact p lam) (theta p) / Q 1 (yContact p lam) (theta p))
  set atl := 1 / 2 * (Qt lam (yContact p lam) (theta p) / Q lam (yContact p lam) (theta p))
  set ayy1 := 1 / 2 * ((Qyy 1 (yContact p lam) (theta p) * Q 1 (yContact p lam) (theta p) -
    Qy 1 (yContact p lam) (theta p) ^ 2) / Q 1 (yContact p lam) (theta p) ^ 2)
  set ayyl := 1 / 2 * ((Qyy lam (yContact p lam) (theta p) * Q lam (yContact p lam) (theta p) -
    Qy lam (yContact p lam) (theta p) ^ 2) / Q lam (yContact p lam) (theta p) ^ 2)
  set att1 := 1 / 2 * ((Qtt 1 (yContact p lam) (theta p) * Q 1 (yContact p lam) (theta p) -
    Qt 1 (yContact p lam) (theta p) ^ 2) / Q 1 (yContact p lam) (theta p) ^ 2)
  set attl := 1 / 2 * ((Qtt lam (yContact p lam) (theta p) * Q lam (yContact p lam) (theta p) -
    Qt lam (yContact p lam) (theta p) ^ 2) / Q lam (yContact p lam) (theta p) ^ 2)
  set ayt1 := 1 / 2 * ((Qyt 1 (yContact p lam) (theta p) * Q 1 (yContact p lam) (theta p) -
    Qy 1 (yContact p lam) (theta p) * Qt 1 (yContact p lam) (theta p)) / Q 1 (yContact p lam) (theta p) ^ 2)
  set aytl := 1 / 2 * ((Qyt lam (yContact p lam) (theta p) * Q lam (yContact p lam) (theta p) -
    Qy lam (yContact p lam) (theta p) * Qt lam (yContact p lam) (theta p)) /
      Q lam (yContact p lam) (theta p) ^ 2)
  have hH1 := hH 1
  have hHl := hH lam
  refine ⟨hLval, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination hFy
  · linear_combination hH1 - hHl
  · linear_combination (p * at1) * hB
  · linear_combination (p * ayy1 + p ^ 2 * ay1 ^ 2) * hB + p ^ 2 * B * (ay1 + ayl) * hFy
  · linear_combination (p * ayt1 + p ^ 2 * ay1 * at1) * hB + p ^ 2 * B * at1 * hFy
  · linear_combination (p * att1 + p ^ 2 * at1 ^ 2) * hB

end GKSharp
