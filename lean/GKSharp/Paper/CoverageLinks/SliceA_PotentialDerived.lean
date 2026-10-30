/- Coverage links for the approved targets of slice SliceA_PotentialDerived: each target type verbatim, proved from installed
results. Generated from the frozen snapshot with md5 eb4fed10b0defe69fc42fba2af020460; do not edit. -/
import GKSharp.Defs.Potential
import GKSharp.Proofs.GKRoot
import GKSharp.Proofs.Pencil
import GKSharp.Paper.Statements

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace GKSharp.CoverageLinks.SliceA_PotentialDerived

open Real MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator ContDiff
namespace GKSharp

def FiniteBlaschke (B : ℂ → ℂ) : Prop :=
  ∃ (phase : ℂ) (roots : List ℂ), ‖phase‖ = 1 ∧
    (∀ a ∈ roots, ‖a‖ < 1) ∧
    ∀ z : ℂ, B z = phase * (roots.map fun a => (z - a) / (1 - star a * z)).prod

noncomputable def polarLaplacian (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  deriv (deriv fun x : ℝ => u ((x : ℂ) + (z.im : ℂ) * Complex.I)) z.re +
    deriv (deriv fun y : ℝ => u ((z.re : ℂ) + (y : ℂ) * Complex.I)) z.im

noncomputable def fejerMean (u : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    ((1 - (n.natAbs : ℝ) / (N + 1) : ℝ) : ℂ) *
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      (∫ s in (0 : ℝ)..(2 * Real.pi), (u s : ℂ) * unitPoint (-(n : ℝ) * s)) *
      unitPoint ((n : ℝ) * t)).re

namespace Paper
variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- Coverage link (derived (sec3_disk at rho = lam: diskCentre = -contactKappa, diskRadiusSq = (C(1-lam)/(C^2-1))^2; squares of nonnegatives)): the approved target `slice_O32` of slice SliceA_PotentialDerived, from installed rows. Paper place: sec4a_criterion.tex:15–17 (short v3.40): "is negative exactly on the open disc $U_C = \{|\zeta + \lambda| > C|\zeta + 1|\} = \{|\zeta + \kappa| < R\}$ ... so that $R = C(1-\lambda)/(C^2-1)$". -/
theorem cover_slice_O32 : ∀ (hp : 1 < p) (hp2 : p < 2) (C lam : ℝ) (hC : 1 < C)
    (hlam : -1 ≤ lam ∧ lam < 1),
    0 < contactKappa C lam ∧
    contactKappa C lam ^ 2 - (C * (1 - lam) / (C ^ 2 - 1)) ^ 2 =
      (C ^ 2 - lam ^ 2) / (C ^ 2 - 1) ∧
    0 < (C ^ 2 - lam ^ 2) / (C ^ 2 - 1) ∧
    ∀ z : ℂ, obstacleG p C (lam : ℂ) z < 0 ↔
      ‖z + (contactKappa C lam : ℂ)‖ < C * (1 - lam) / (C ^ 2 - 1) :=
  by intro hp hp2 C lam hC hlam; obtain ⟨hl1, hl2⟩ := hlam; have hC2 : 1 < C ^ 2 := (by nlinarith); have hden : 0 < C ^ 2 - 1 := (by linarith); have hlsq : lam ^ 2 ≤ 1 := (by nlinarith); have hk : 0 < contactKappa C lam := (by unfold contactKappa; exact div_pos (by linarith) hden); have hid : contactKappa C lam ^ 2 - (C * (1 - lam) / (C ^ 2 - 1)) ^ 2 = (C ^ 2 - lam ^ 2) / (C ^ 2 - 1) := (by unfold contactKappa; field_simp; ring); refine ⟨hk, hid, div_pos (by linarith) hden, ?_⟩; intro z; have hmax : max 1 ‖(lam : ℂ)‖ < C := (by rw [Complex.norm_real, Real.norm_eq_abs]; exact max_lt hC (by rw [abs_lt]; constructor <;> linarith)); obtain ⟨h1, h2, -, -⟩ := GKSharp.Paper.sec3_disk (by linarith : (0 : ℝ) < p) (lam : ℂ) hmax; have hc : diskCentre C (lam : ℂ) = -((contactKappa C lam : ℝ) : ℂ) := (by unfold diskCentre contactKappa; push_cast; ring); have hR : diskRadiusSq C (lam : ℂ) = (C * (1 - lam) / (C ^ 2 - 1)) ^ 2 := (by unfold diskRadiusSq; rw [hc]; simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]; linarith [hid]); have hRnn : 0 ≤ C * (1 - lam) / (C ^ 2 - 1) := div_nonneg (mul_nonneg (by linarith) (by linarith)) hden.le; rw [h1 z, h2 z, hR, hc, sub_neg_eq_add]; exact pow_lt_pow_iff_left₀ (norm_nonneg _) hRnn two_ne_zero

/-- Coverage link (derived (eq_GK + sec3_gk_gt_max: kappa^2 s^2 - R^2 = s^2 gkQuad(C^2)/(C^2-1)^2, Vieta second root; sec3_radial_limits with r^(-p/2) g = g / r^(p/2) for r > 0)): the approved target `slice_O34` of slice SliceA_PotentialDerived, from installed rows. Paper place: sec4a_criterion.tex:26–30 (short v3.40). -/
theorem cover_slice_O34 : ∀ (hp : 1 < p) (hp2 : p < 2) (C lam : ℝ) (hC : 1 < C)
    (hlam : -1 ≤ lam ∧ lam < 1),
    (contactKappa C lam ^ 2 * sin (Real.pi / p) ^ 2 = (C * (1 - lam) / (C ^ 2 - 1)) ^ 2 ↔
      gkQuad p (lam : ℂ) (C ^ 2) = 0) ∧
    lam ^ 2 / gk p (lam : ℂ) ^ 2 < 1 ∧
    gkQuad p (lam : ℂ) (lam ^ 2 / gk p (lam : ℂ) ^ 2) = 0 ∧
    Tendsto (fun r : ℝ => r ^ (-(p / 2)) * obstacleG p C (lam : ℂ) ((r : ℂ) * unitPoint (Real.pi / p)))
      (nhdsWithin 0 (Set.Ioi 0)) atTop ∧
    Tendsto (fun r : ℝ => r ^ (-(p / 2)) * obstacleG p C (lam : ℂ) ((r : ℂ) * unitPoint (Real.pi / p)))
      atTop atTop :=
  by intro hp hp2 C lam hC hlam; obtain ⟨hl1, hl2⟩ := hlam; have hden : 0 < C ^ 2 - 1 := (by nlinarith); have hθ2 : Real.pi / p < Real.pi := (by rw [div_lt_iff₀ (by linarith)]; nlinarith [Real.pi_pos]); have hs : 0 < sin (Real.pi / p) := Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by linarith)) hθ2; have hn0 : ‖(lam : ℂ)‖ ^ 2 = lam ^ 2 := (by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]); have hn1 : ‖(1 : ℂ) - (lam : ℂ)‖ ^ 2 = (1 - lam) ^ 2 := (by rw [show (1 : ℂ) - (lam : ℂ) = ((1 - lam : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, sq_abs]); have hq : ∀ X : ℝ, gkQuad p (lam : ℂ) X = X ^ 2 - (1 + lam ^ 2 + (1 - lam) ^ 2 * ((1 - sin (Real.pi / p) ^ 2) / sin (Real.pi / p) ^ 2)) * X + lam ^ 2 := (by intro X; unfold gkQuad gkMid; rw [hn0, hn1, Real.cot_eq_cos_div_sin, div_pow, Real.cos_sq']); have hkey : contactKappa C lam ^ 2 * sin (Real.pi / p) ^ 2 - (C * (1 - lam) / (C ^ 2 - 1)) ^ 2 = sin (Real.pi / p) ^ 2 * gkQuad p (lam : ℂ) (C ^ 2) / (C ^ 2 - 1) ^ 2 := (by rw [hq]; unfold contactKappa; field_simp; ring); have hne : (lam : ℂ) ≠ 1 := (by intro h; have h' := congrArg Complex.re h; simp at h'; linarith); have hg := GKSharp.Paper.sec3_gk_gt_max hp (ne_of_lt hp2) hne; have hg0 : 0 < gk p (lam : ℂ) := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hg.le); have hgl : |lam| < gk p (lam : ℂ) := (by have h := lt_of_le_of_lt (le_max_right _ _) hg; rwa [Complex.norm_real, Real.norm_eq_abs] at h); have hmax : max 1 ‖(lam : ℂ)‖ < C := (by rw [Complex.norm_real, Real.norm_eq_abs]; exact max_lt hC (by rw [abs_lt]; constructor <;> linarith)); have hL := GKSharp.Paper.sec3_radial_limits hp hmax (Real.pi / p); refine ⟨?_, ?_, ?_, hL.1.congr' ?_, hL.2.congr' ?_⟩; rw [← sub_eq_zero, hkey]; constructor; intro h; exact (mul_eq_zero.1 ((div_eq_zero_iff.1 h).resolve_right (pow_ne_zero 2 hden.ne'))).resolve_left (pow_ne_zero 2 hs.ne'); intro h; rw [h, mul_zero, zero_div]; rw [div_lt_one (by positivity)]; have h2 := pow_lt_pow_left₀ hgl (abs_nonneg lam) two_ne_zero; rwa [sq_abs] at h2; have hX : gkQuad p (lam : ℂ) (lam ^ 2 / gk p (lam : ℂ) ^ 2) = lam ^ 2 / (gk p (lam : ℂ) ^ 2) ^ 2 * gkQuad p (lam : ℂ) (gk p (lam : ℂ) ^ 2) := (by unfold gkQuad; rw [hn0]; field_simp; ring); rw [hX, (GKSharp.Paper.eq_GK p (lam : ℂ)).1, mul_zero]; filter_upwards [self_mem_nhdsWithin] with r hr; rw [Real.rpow_neg (le_of_lt hr), div_eq_inv_mul]; filter_upwards [Filter.eventually_gt_atTop 0] with r hr; rw [Real.rpow_neg hr.le, div_eq_inv_mul]

/-- Coverage link (derived (sec3_disk: the set is inside the open ball(-kappa, R), closure inside the closed ball, and R < kappa)): the approved target `contact_disk_origin_excluded` of slice SliceA_PotentialDerived, from installed rows. Paper place: sec4a_criterion.tex:17 (short v3.40). -/
theorem cover_contact_disk_origin_excluded : ∀ (hp : 1 < p) (hp2 : p < 2) (C lam : ℝ)
    (hC : 1 < C) (hlam : -1 ≤ lam ∧ lam < 1),
    (0 : ℂ) ∉ closure {z : ℂ | obstacleG p C (lam : ℂ) z < 0} :=
  by intro hp hp2 C lam hC hlam; obtain ⟨hl1, hl2⟩ := hlam; have hC2 : 1 < C ^ 2 := (by nlinarith); have hden : 0 < C ^ 2 - 1 := (by linarith); have hmax : max 1 ‖(lam : ℂ)‖ < C := (by rw [Complex.norm_real, Real.norm_eq_abs]; exact max_lt hC (by rw [abs_lt]; constructor <;> linarith)); obtain ⟨h1, h2, -, -⟩ := GKSharp.Paper.sec3_disk (by linarith : (0 : ℝ) < p) (lam : ℂ) hmax; have hc : diskCentre C (lam : ℂ) = -((contactKappa C lam : ℝ) : ℂ) := (by unfold diskCentre contactKappa; push_cast; ring); have hid : contactKappa C lam ^ 2 - (C * (1 - lam) / (C ^ 2 - 1)) ^ 2 = (C ^ 2 - lam ^ 2) / (C ^ 2 - 1) := (by unfold contactKappa; field_simp; ring); have hR : diskRadiusSq C (lam : ℂ) = (C * (1 - lam) / (C ^ 2 - 1)) ^ 2 := (by unfold diskRadiusSq; rw [hc]; simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]; linarith [hid]); have hRnn : 0 ≤ C * (1 - lam) / (C ^ 2 - 1) := div_nonneg (mul_nonneg (by linarith) (by linarith)) hden.le; have hsub : {z : ℂ | obstacleG p C (lam : ℂ) z < 0} ⊆ Metric.ball (-((contactKappa C lam : ℝ) : ℂ)) (C * (1 - lam) / (C ^ 2 - 1)) := (by intro z hz; have hz' := (h2 z).1 ((h1 z).1 hz); rw [hR, hc, sub_neg_eq_add] at hz'; rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add]; exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hRnn two_ne_zero).1 hz'); have hgap : C * (1 - lam) / (C ^ 2 - 1) < contactKappa C lam := (by unfold contactKappa; rw [div_lt_div_iff_of_pos_right hden]; nlinarith [mul_pos (sub_pos.2 hC) (by linarith : (0 : ℝ) < C + lam)]); have hk : 0 < contactKappa C lam := lt_of_le_of_lt hRnn hgap; intro h0; have h0' := ((closure_mono hsub).trans Metric.closure_ball_subset_closedBall) h0; rw [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add, zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk] at h0'; linarith

/-- Coverage link (derived (|r u + kappa|^2 = (r + kappa cos)^2 + (kappa sin)^2 with cos(pi/p) < 0 < sin(pi/p); definitions only)): the approved target `contact_ray_meets_iff` of slice SliceA_PotentialDerived, from installed rows. Paper place: sec4a_criterion.tex:27–28 (short v3.40). -/
theorem cover_contact_ray_meets_iff : ∀ (hp : 1 < p) (hp2 : p < 2) (C lam : ℝ)
    (hC : 1 < C) (hlam : -1 ≤ lam ∧ lam < 1),
    (∃ r : ℝ, 0 < r ∧
      ‖(r : ℂ) * unitPoint (Real.pi / p) + (contactKappa C lam : ℂ)‖ <
        C * (1 - lam) / (C ^ 2 - 1)) ↔
      contactKappa C lam * sin (Real.pi / p) < C * (1 - lam) / (C ^ 2 - 1) :=
  by intro hp hp2 C lam hC hlam; obtain ⟨hl1, hl2⟩ := hlam; have hden : 0 < C ^ 2 - 1 := (by nlinarith); have hk : 0 < contactKappa C lam := (by unfold contactKappa; exact div_pos (by nlinarith) hden); have hRnn : 0 ≤ C * (1 - lam) / (C ^ 2 - 1) := div_nonneg (mul_nonneg (by linarith) (by linarith)) hden.le; have hθ1 : Real.pi / 2 < Real.pi / p := (by rw [div_lt_div_iff₀ two_pos (by linarith)]; nlinarith [Real.pi_pos]); have hθ2 : Real.pi / p < Real.pi := (by rw [div_lt_iff₀ (by linarith)]; nlinarith [Real.pi_pos]); have hcos : cos (Real.pi / p) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hθ1 (by linarith [Real.pi_pos]); have hsin : 0 < sin (Real.pi / p) := Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by linarith)) hθ2; have hn : ∀ r : ℝ, ‖(r : ℂ) * unitPoint (Real.pi / p) + (contactKappa C lam : ℂ)‖ ^ 2 = (r + contactKappa C lam * cos (Real.pi / p)) ^ 2 + (contactKappa C lam * sin (Real.pi / p)) ^ 2 := (by intro r; rw [Complex.sq_norm, Complex.normSq_apply]; simp only [unitPoint, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]; linear_combination (r ^ 2 - contactKappa C lam ^ 2) * sin_sq_add_cos_sq (Real.pi / p)); refine ⟨fun ⟨r, _, hr⟩ => ?_, fun h => ?_⟩; have h2 := (pow_lt_pow_iff_left₀ (norm_nonneg _) hRnn two_ne_zero).2 hr; rw [hn r] at h2; have h3 : (contactKappa C lam * sin (Real.pi / p)) ^ 2 < (C * (1 - lam) / (C ^ 2 - 1)) ^ 2 := (by nlinarith [sq_nonneg (r + contactKappa C lam * cos (Real.pi / p))]); exact (pow_lt_pow_iff_left₀ (mul_pos hk hsin).le hRnn two_ne_zero).1 h3; refine ⟨-(contactKappa C lam * cos (Real.pi / p)), (by nlinarith [mul_pos hk (neg_pos.2 hcos)]), ?_⟩; refine (pow_lt_pow_iff_left₀ (norm_nonneg _) hRnn two_ne_zero).1 ?_; rw [hn, neg_add_cancel]; have h4 := pow_lt_pow_left₀ h (mul_pos hk hsin).le two_ne_zero; nlinarith

/-- Coverage link (derived (sec3_gk_gt_max gives gk > 1 so kappa > 0; |cos(pi/p)| = -cos(pi/p))): the approved target `contact_perpendicular_foot` of slice SliceA_PotentialDerived, from installed rows. Paper place: sec4a_criterion.tex:32–34 (short v3.40). -/
theorem cover_contact_perpendicular_foot : ∀ (hp : 1 < p) (hp2 : p < 2) (lam : ℝ)
    (hlam : -1 ≤ lam ∧ lam < 1),
    0 < contactRadius p lam ∧
    (-(contactKappa (gk p (lam : ℂ)) lam : ℂ) * (cos (Real.pi / p) : ℂ) *
      unitPoint (Real.pi / p) = (contactRadius p lam : ℂ) * unitPoint (Real.pi / p)) ∧
    cos (Real.pi / p) = -contactRadius p lam / contactKappa (gk p (lam : ℂ)) lam :=
  by intro hp hp2 lam hlam; obtain ⟨hl1, hl2⟩ := hlam; have hne : (lam : ℂ) ≠ 1 := (by intro h; have h' := congrArg Complex.re h; simp at h'; linarith); have hg := GKSharp.Paper.sec3_gk_gt_max hp (ne_of_lt hp2) hne; have hg1 : 1 < gk p (lam : ℂ) := lt_of_le_of_lt (le_max_left _ _) hg; have hden : 0 < gk p (lam : ℂ) ^ 2 - 1 := (by nlinarith); have hk : 0 < contactKappa (gk p (lam : ℂ)) lam := (by unfold contactKappa; exact div_pos (by nlinarith) hden); have hθ1 : Real.pi / 2 < Real.pi / p := (by rw [div_lt_div_iff₀ two_pos (by linarith)]; nlinarith [Real.pi_pos]); have hθ2 : Real.pi / p < Real.pi := (by rw [div_lt_iff₀ (by linarith)]; nlinarith [Real.pi_pos]); have hcos : cos (Real.pi / p) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hθ1 (by linarith [Real.pi_pos]); refine ⟨(by unfold contactRadius; exact mul_pos hk (abs_pos.2 hcos.ne)), (by unfold contactRadius; rw [abs_of_neg hcos]; push_cast; ring), (by unfold contactRadius; rw [abs_of_neg hcos]; field_simp)⟩

end Paper
end GKSharp

end GKSharp.CoverageLinks.SliceA_PotentialDerived
