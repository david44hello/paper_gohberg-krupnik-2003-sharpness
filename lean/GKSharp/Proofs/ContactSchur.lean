/- GKSharp/Proofs/ContactSchur.lean — actual normalized Schur identity.
Frozen source: short_v0.70/sec4b_failure.tex:38; former v0.40:43.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.ContactScaling

namespace GKSharp
open Threshold Set

theorem contact_schur_identity_proved (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let t := theta p
    let LL := logGap p lam
    Real.exp (q p * y) * muSecond p lam / (p * weightP p lam y t) =
      (dyy LL y t * (2 * p * dt (chi lam) y t * dt LL y t + p * dt LL y t ^ 2) -
        dyy LL y t ^ 2 - (dty LL y t + dt LL y t * (p * dy (chi lam) y t - q p)) ^ 2) /
        dyy LL y t := by
  dsimp only
  let yy := yContact p lam
  let tt := theta p
  let LL := logGap p lam
  let PP := weightP p lam yy tt
  let AA := Real.exp (q p * yy)
  have hAA : AA ≠ 0 := Real.exp_ne_zero _
  have hp0 : p ≠ 0 := by linarith
  have hPP : PP ≠ 0 := Real.exp_ne_zero _
  obtain ⟨_, _, hLtt, hGt, hGyy, hGty, hGtt⟩ :=
    contact_harmonic_derivatives_proved p lam hp hp2 hlam
  obtain ⟨hSTT, hSYY, hSTY⟩ := contact_gamma_scaling_proved p lam hp hp2 hlam
  have hYY : dyy (gammaGK p lam) yy tt = p * PP * dyy LL yy tt / AA := by
    apply (eq_div_iff hAA).mpr
    rw [hGyy] at hSYY
    linear_combination hSYY
  have hTY : dty (gammaGK p lam) yy tt =
      p * PP * (dty LL yy tt + dt LL yy tt * (p * dy (chi lam) yy tt - q p)) / AA := by
    apply (eq_div_iff hAA).mpr
    rw [hGty, hGt] at hSTY
    linear_combination hSTY
  have hTT : dtt (gammaGK p lam) yy tt =
      p * PP * (-dyy LL yy tt + p * dt LL yy tt ^ 2 +
        2 * p * dt (chi lam) yy tt * dt LL yy tt) / AA := by
    apply (eq_div_iff hAA).mpr
    rw [hGtt, hLtt] at hSTT
    linear_combination hSTT
  obtain ⟨_, _, _, _, _, _, hpositive⟩ := contact_spec_proved p lam hp hp2 hlam
  have hLyy : dyy LL yy tt ≠ 0 := by
    intro hh
    have hzero := hYY
    rw [hh, mul_zero, zero_div] at hzero
    exact (ne_of_gt hpositive) hzero
  unfold muSecond
  change AA * (dtt (gammaGK p lam) yy tt -
    dty (gammaGK p lam) yy tt ^ 2 / dyy (gammaGK p lam) yy tt) / (p * PP) =
    (dyy LL yy tt * (2 * p * dt (chi lam) yy tt * dt LL yy tt + p * dt LL yy tt ^ 2) -
      dyy LL yy tt ^ 2 - (dty LL yy tt + dt LL yy tt * (p * dy (chi lam) yy tt - q p)) ^ 2) /
      dyy LL yy tt
  rw [hYY, hTY, hTT]
  field_simp [hAA, hp0, hPP, hLyy]
  <;> ring

end GKSharp

#print axioms GKSharp.contact_schur_identity_proved

