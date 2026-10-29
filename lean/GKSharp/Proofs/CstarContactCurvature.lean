/-
CstarContactCurvature.lean — project019 local contact curvature for Theorem C*.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Proofs.ContactSign
import GKSharp.Proofs.ContactEnvelope
import GKSharp.Proofs.Sec4bLocal

namespace GKSharp.Proofs.CstarContactCurvature

open GKSharp Threshold Set Filter Topology
open scoped ContDiff

lemma localTest_lt_one_below_local {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl0 : 0 < lam) (hl1 : lam < 1) (hloc : lam < lambdaLoc p) : localTest p lam < 1 := by
  let b := (lam + min (lambdaLoc p) 1) / 2
  have hlm : lam < min (lambdaLoc p) 1 := lt_min hloc hl1
  have hb : lam < b := by dsimp [b]; linarith
  have hbm : b < min (lambdaLoc p) 1 := by dsimp [b]; linarith
  have hb0 : 0 < b := hl0.trans hb
  have hb1 : b < 1 := hbm.trans_le (min_le_right _ _)
  have hbloc : b < lambdaLoc p := hbm.trans_le (min_le_left _ _)
  have hble : localTest p b ≤ 1 := by
    apply not_lt.mp
    intro hh
    exact lt_asymm hbloc ((local_threshold_iff_proved p b hp1 hp2 ⟨hb0, hb1⟩).mp hh)
  have ha : 1 + lam ≠ 0 := by linarith
  have hbb : 1 + b ≠ 0 := by linarith
  have hdiff : localTest p b - localTest p lam =
      4 * cs p ^ 4 * (b - lam) * (1 - lam * b) / ((1 + lam) ^ 2 * (1 + b) ^ 2) := by
    unfold localTest
    field_simp [ha, hbb]
    <;> ring
  have hc : 0 < cs p := neg_pos.mpr (cos_theta_negative hp1 hp2)
  have hab : 0 < 1 - lam * b := by nlinarith [mul_pos hl0 (sub_pos.mpr hb1)]
  have hpositive : 0 < localTest p b - localTest p lam := by
    rw [hdiff]
    exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hc 4)) (sub_pos.mpr hb)) hab)
      (mul_pos (sq_pos_of_pos (by linarith)) (sq_pos_of_pos (by linarith)))
  linarith

theorem muSecond_pos_below_local {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl0 : 0 < lam) (hl1 : lam < 1) (hloc : lam < lambdaLoc p) : 0 < muSecond p lam := by
  have htest := localTest_lt_one_below_local hp1 hp2 hl0 hl1 hloc
  have hpm : p - 1 ≠ 0 := by linarith
  have hld : 1 + lam ≠ 0 := by linarith
  have hid : signBracket p lam = (p - 1) * (1 - localTest p lam) := by
    unfold signBracket localTest dual
    field_simp [hpm, hld]
    <;> ring
  have hbr : 0 < signBracket p lam := by rw [hid]; exact mul_pos (by linarith) (by linarith)
  obtain ⟨hb, hnorm, _⟩ := contact_sign_factorization_proved p lam hp1 hp2 ⟨by linarith, hl1⟩
  have hn : 0 < Real.exp (q p * yContact p lam) * muSecond p lam /
      (p * weightP p lam (yContact p lam) (theta p)) := by
    rw [hnorm]
    exact mul_pos hb hbr
  by_contra hh
  have hP : 0 < p * weightP p lam (yContact p lam) (theta p) :=
    mul_pos (by linarith) (Real.exp_pos _)
  have hnonpos := div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (q p * yContact p lam)).le (le_of_not_gt hh)) hP.le
  exact (not_lt_of_ge hnonpos) hn

lemma positive_quadratic_of_schur {a b c v : ℝ} (ha : 0 < a) (hschur : 0 < c - b ^ 2 / a) :
    0 < c + 2 * b * v + a * v ^ 2 := by
  have hid : c + 2 * b * v + a * v ^ 2 = (c - b ^ 2 / a) + (a * v + b) ^ 2 / a := by
    field_simp [ha.ne']
    <;> ring
  rw [hid]
  exact add_pos_of_pos_of_nonneg hschur (div_nonneg (sq_nonneg _) ha.le)

lemma second_along_graph {f : ℝ → ℝ → ℝ} {branch : ℝ → ℝ} {t : ℝ}
    (hf : ContDiffAt ℝ ω (fun u : ℝ × ℝ => f u.2 u.1) (t, branch t))
    (hb : ContDiffAt ℝ ω branch t) (hzero : dy f (branch t) t = 0) :
    HasDerivAt (deriv (fun s => f (branch s) s))
      (dtt f (branch t) t + 2 * dty f (branch t) t * deriv branch t +
        dyy f (branch t) t * deriv branch t ^ 2) t := by
  have hbd := hb.differentiableAt (by simp)
  have hdt := ContactSmooth.dt_contDiffAt hf
  have hdy := ContactSmooth.dy_contDiffAt hf
  have hmap : DifferentiableAt ℝ (fun s => (s, branch s)) t := differentiableAt_id.prodMk hbd
  have hDt := ((hdt.differentiableAt (by simp)).comp t hmap).hasDerivAt
  have hDy := ((hdy.differentiableAt (by simp)).comp t hmap).hasDerivAt
  change HasDerivAt (fun s => dt f (branch s) s) (deriv (fun s => dt f (branch s) s) t) t at hDt
  change HasDerivAt (fun s => dy f (branch s) s) (deriv (fun s => dy f (branch s) s) t) t at hDy
  rw [ContactSmooth.chain_deriv (hdt.differentiableAt (by simp)) hbd] at hDt
  rw [ContactSmooth.chain_deriv (hdy.differentiableAt (by simp)) hbd] at hDy
  have hBp := ((hb.derivWithin (m := ω) (by simp)).differentiableAt (by simp)).hasDerivAt
  have heq : deriv (fun s => f (branch s) s) =ᶠ[𝓝 t]
      (fun s => dt f (branch s) s + dy f (branch s) s * deriv branch s) := by
    have htend : Tendsto (fun s => (s, branch s)) (𝓝 t) (𝓝 (t, branch t)) :=
      continuousAt_id.prodMk hb.continuousAt
    filter_upwards [htend.eventually (hf.eventually (by simp)), hb.eventually (by simp)] with s hfs hbs
    exact ContactSmooth.chain_deriv (hfs.differentiableAt (by simp)) (hbs.differentiableAt (by simp))
  have hD := (hDt.add (hDy.mul hBp)).congr_of_eventuallyEq heq
  convert hD using 1
  rw [ContactSmooth.mixed_partials hf, hzero]
  simp only [zero_mul, add_zero]
  unfold dtt dty dyy
  ring

lemma second_scaled_at_zero {S H : ℝ → ℝ} {t a : ℝ}
    (hS : ContDiffAt ℝ ∞ S t) (hH : ContDiffAt ℝ ∞ H t)
    (hzero : H t = 0) (hcritical : deriv H t = 0) (hsecond : HasDerivAt (deriv H) a t) :
    HasDerivAt (deriv (fun s => S s * H s)) (S t * a) t := by
  have hSd := hS.differentiableAt (by simp)
  have hHd := hH.differentiableAt (by simp)
  have hSp := ((hS.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have heq : deriv (fun s => S s * H s) =ᶠ[𝓝 t]
      (fun s => deriv S s * H s + S s * deriv H s) := by
    have hS1 : ContDiffAt ℝ 1 S t := hS.of_le (by simp)
    have hH1 : ContDiffAt ℝ 1 H t := hH.of_le (by simp)
    filter_upwards [hS1.eventually (by simp), hH1.eventually (by simp)] with s hss hhs
    exact ((hss.differentiableAt (by simp)).hasDerivAt.mul
      (hhs.differentiableAt (by simp)).hasDerivAt).deriv
  have hh := ((hSp.mul hHd.hasDerivAt).add (hSd.hasDerivAt.mul hsecond)).congr_of_eventuallyEq heq
  convert hh using 1
  simp only [hzero, hcritical, mul_zero, zero_add, add_zero]

end GKSharp.Proofs.CstarContactCurvature

#print axioms GKSharp.Proofs.CstarContactCurvature.muSecond_pos_below_local
#print axioms GKSharp.Proofs.CstarContactCurvature.second_along_graph
