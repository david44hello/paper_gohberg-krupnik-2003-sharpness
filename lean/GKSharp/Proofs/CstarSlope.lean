/-
CstarSlope.lean — Section5e, positive Lambda curvature and negative Kf slope.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.CstarLambdaSecond
import GKSharp.Proofs.CstarContactCurvature
import GKSharp.Proofs.CstarProfileBridge
import GKSharp.Proofs.ContactDtGamma

namespace GKSharp.Proofs.CstarSlope

open GKSharp Threshold ComplexConjugate Filter Topology
open GKSharp.Proofs.CstarLambdaSecond GKSharp.Proofs.CstarContactCurvature GKSharp.Proofs.CstarProfileBridge
open scoped ContDiff

theorem sec5e_Kf_slope_proved {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hh : kConst p lam ≤ obstacle p (gk p lam) lam 0) (hloc : lam < Threshold.lambdaLoc p) :
    0 < deriv (deriv (lamCurve p (gk p lam) (kConst p lam) lam)) (Real.pi / p) ∧
    deriv (curveKf p lam) (Real.pi / p) < 0 := by
  let t := Real.pi / p
  let B := curveY p lam
  let G : ℝ → ℝ := fun s => gammaGK p lam (B s) s
  let Cc : ℝ → ℝ := fun s => kConst p lam * Real.cos (p / 2 * s)
  let H : ℝ → ℝ := fun s => G s - Cc s
  have hl : -1 ≤ lam := by linarith
  have hll : -1 < lam := by linarith
  have ht0 : 0 < t := div_pos Real.pi_pos (by linarith)
  have ht : t < Real.pi := div_lt_self Real.pi_pos hp1
  have hpoint : B t = yContact p lam := contact_height hp1 hp2 hll hl1
  obtain ⟨hB, hS, hSpos⟩ := smooth_scale hp1 hp2 hl hl1 ht0 ht
  change ContDiffAt ℝ ω B t at hB
  have hγ : ContDiffAt ℝ ω (fun u : ℝ × ℝ => gammaGK p lam u.2 u.1) (t, B t) := by
    rw [hpoint]
    exact ContactSmooth.gamma_contDiffAt p lam _ _ hp1 (ContactSmooth.contact_positiveBases p lam hp1 hp2 ⟨hll, hl1⟩)
  have hG : ContDiffAt ℝ ω G t := by
    have hmap : ContDiffAt ℝ ω (fun s : ℝ => (s, B s)) t := contDiffAt_id.prodMk hB
    change ContDiffAt ℝ ω ((fun u : ℝ × ℝ => gammaGK p lam u.2 u.1) ∘ (fun s => (s, B s))) t
    exact hγ.comp t hmap
  have hCc : ContDiff ℝ ∞ Cc := by dsimp [Cc]; fun_prop
  have hH : ContDiffAt ℝ ∞ H t := (hG.of_le (by simp)).sub hCc.contDiffAt
  obtain ⟨_, _, _, _, hval, hdy, hyy⟩ := contact_spec_proved p lam hp1 hp2 ⟨hll, hl1⟩
  change gammaGK p lam (yContact p lam) t = 0 at hval
  change dy (gammaGK p lam) (yContact p lam) t = 0 at hdy
  change 0 < dyy (gammaGK p lam) (yContact p lam) t at hyy
  have hdt := contact_dt_gamma p lam hp1 hp2 ⟨hll, hl1⟩
  change dt (gammaGK p lam) (yContact p lam) t = -(p / 2) * kConst p lam at hdt
  have hp0 : p ≠ 0 := by linarith
  have hphase : p / 2 * t = Real.pi / 2 := by dsimp [t]; field_simp [hp0]
  have hcos : Real.cos (p / 2 * t) = 0 := by rw [hphase, Real.cos_pi_div_two]
  have hsin : Real.sin (p / 2 * t) = 1 := by rw [hphase, Real.sin_pi_div_two]
  have hC1 (s : ℝ) : HasDerivAt Cc (-kConst p lam * (p / 2) * Real.sin (p / 2 * s)) s := by
    have hd := (((hasDerivAt_id s).const_mul (p / 2)).cos.const_mul (kConst p lam))
    simp only [id_eq, mul_one] at hd
    exact hd.congr_deriv (by ring)
  have hCeq : deriv Cc = fun s => -kConst p lam * (p / 2) * Real.sin (p / 2 * s) :=
    funext fun s => (hC1 s).deriv
  have hC2 : HasDerivAt (deriv Cc) 0 t := by
    rw [hCeq]
    have hd := (((hasDerivAt_id t).const_mul (p / 2)).sin.const_mul (-kConst p lam * (p / 2)))
    simp only [id_eq, mul_one] at hd
    exact hd.congr_deriv (by rw [hcos]; ring)
  have hGd := (hG.differentiableAt (by simp)).hasDerivAt
  change HasDerivAt G (deriv (fun s => gammaGK p lam (B s) s) t) t at hGd
  rw [ContactSmooth.chain_deriv (hγ.differentiableAt (by simp)) (hB.differentiableAt (by simp))] at hGd
  have hHd : HasDerivAt H 0 t := by
    convert hGd.sub (hC1 t) using 1
    rw [hpoint, hdy, hdt, hsin]
    ring
  have hH0 : H t = 0 := by
    change gammaGK p lam (B t) t - kConst p lam * Real.cos (p / 2 * t) = 0
    rw [hpoint, hval, hcos]
    ring
  let A := dtt (gammaGK p lam) (B t) t +
    2 * dty (gammaGK p lam) (B t) t * deriv B t +
    dyy (gammaGK p lam) (B t) t * deriv B t ^ 2
  have hG2 : HasDerivAt (deriv G) A t :=
    second_along_graph hγ hB (by rw [hpoint]; exact hdy)
  have heqH : deriv H =ᶠ[𝓝 t] (fun s => deriv G s - deriv Cc s) := by
    filter_upwards [hG.eventually (by simp)] with s hGs
    change deriv (fun x => G x - Cc x) s = _
    exact deriv_sub (hGs.differentiableAt (by simp)) (hC1 s).differentiableAt
  have hH2 : HasDerivAt (deriv H) A t := by
    simpa only [sub_zero] using (hG2.sub hC2).congr_of_eventuallyEq heqH
  have hmu := muSecond_pos_below_local hp1 hp2 hl0 hl1 hloc
  have hApos : 0 < A := by
    apply positive_quadratic_of_schur
    · simpa only [hpoint] using hyy
    · simpa only [hpoint, muSecond, Threshold.theta, t] using hmu
  have hscaled := second_scaled_at_zero hS hH hH0 hHd.deriv hH2
  have heqΛ : lamCurve p (gk p lam) (kConst p lam) lam =ᶠ[𝓝 t]
      (fun s => curveScale p lam s * H s) := by
    filter_upwards [Ioo_mem_nhds ht0 ht] with s hs
    exact curve_profile hp1 hp2 hl hl1 hs.1 hs.2
  have hΛ2 := hscaled.congr_of_eventuallyEq heqΛ.deriv
  have hΛpos : 0 < deriv (deriv (lamCurve p (gk p lam) (kConst p lam) lam)) t := by
    rw [hΛ2.deriv]
    exact mul_pos hSpos hApos
  obtain ⟨hsecond, hF⟩ := sec5e_Lambda_second_proved hp1 hp2 hl0 hl1
  have hprod := hΛpos
  change 0 < deriv (deriv (lamCurve p (gk p lam) (kConst p lam) lam)) (Real.pi / p) at hprod
  rw [hsecond.deriv] at hprod
  have hneg : deriv (curveKf p lam) t < 0 := by
    by_contra hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hF.le (neg_nonpos.mpr (le_of_not_gt hnot))
    exact (not_lt_of_ge hnonpos) hprod
  exact ⟨hΛpos, hneg⟩

end GKSharp.Proofs.CstarSlope

#print axioms GKSharp.Proofs.CstarSlope.sec5e_Kf_slope_proved
