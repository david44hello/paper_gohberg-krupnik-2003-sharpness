/- GKSharp/Proofs/GKLowerAll.lean — all-complex Gohberg–Krupnik lower bound.
Frozen source: short_v0.70/sec2_obstacle.tex:35; approved slice_O04 type unchanged.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GKLowerReal
import GKSharp.Proofs.Sec3Geom
import GKSharp.Proofs.ChordGK
import GKSharp.Proofs.NormReduce
import GKSharp.Proofs.GKSymm
import GKSharp.Proofs.PencilL2

namespace GKSharp
open Set

namespace LowerAssembly

private theorem arch {q : ℝ} (hq : 1 / 2 < q) {phi : ℝ → ℝ} (hphi : QSubtrig q phi) (t : ℝ) :
    0 ≤ phi t + phi (t + Real.pi / q) :=
  Sec3Geom.sec3_arch_given @ChordGK.slice_O30_proved hq hphi t

private theorem pair_failure {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    (P : RieszProjection p) (rho : ℂ) {C : ℝ} (hC : max 1 ‖rho‖ < C)
    (hpair : ∃ t : ℝ, obstacle p C rho t + obstacle p C rho (t + 2 * Real.pi / p) < 0) :
    C < pencilNorm P rho :=
  Sec3Geom.eq_3_2_given @slice_O18_proved @arch hp P rho hC hpair

private theorem nonreal_lower {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p ≠ 2)
    (P : RieszProjection p) {rho : ℂ} (him : rho.im ≠ 0) : gk p rho ≤ pencilNorm P rho :=
  (Sec3Geom.thm_A_given @pair_failure hp hp2 P him).le

end LowerAssembly

/-- The full original O04 target: every complex ratio and every exponent p>1.
The existing HKV Cole and HV projection-existence inputs remain visible in its inventory. -/
theorem slice_O04_proved {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (P : RieszProjection p) (rho : ℂ) : gk p rho ≤ pencilNorm P rho := by
  obtain ⟨qq, hqq, Q, r, s, _, hq1, hq2, _, hr, hs, hN, hG⟩ := pencil_and_gk_reduce hp P rho
  letI : Fact (1 ≤ ENNReal.ofReal qq) := hqq
  have hsmall : gk qq r ≤ pencilNorm Q r := by
    rcases hq2.lt_or_eq with hq2 | hq2
    · by_cases him : r.im = 0
      · have hre : (r.re : ℂ) = r := Complex.ext rfl (by simpa only [Complex.ofReal_im] using him.symm)
        by_cases hone : r.re = 1
        · have heq : r = 1 := by rw [← hre, hone]; simp
          rw [heq, gk_one, pencilNorm_one]
        · have hn : ‖(r.re : ℂ)‖ ≤ 1 := by rw [hre]; exact hr
          have habs : |r.re| ≤ 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hn
          have hlt : r.re < 1 := by
            by_contra hh
            exact hone (le_antisymm (abs_le.mp habs).2 (le_of_not_gt hh))
          have hh := gk_le_pencilNorm_real qq Q hq1 hq2 r.re ⟨(abs_le.mp habs).1, hlt⟩
          simpa only [hre] using hh
      · exact LowerAssembly.nonreal_lower hq1 (ne_of_lt hq2) Q him
    · subst qq
      change gkPair 2 1 r ≤ ‖pencil Q 1 r‖
      rw [gkPair_two, norm_pencil_two rfl Q]
  rw [hN, hG]
  exact mul_le_mul_of_nonneg_left hsmall (by rw [hs]; exact zero_le_one.trans (le_max_left _ _))

end GKSharp

#print axioms GKSharp.slice_O04_proved
