/- unique local-threshold equation in endpoint coordinates.
Frozen source: short_v0.70/endpoint_estimate.tex:9–14.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.EndpointEnclosure

namespace GKSharp
open Real Threshold

theorem endpoint_threshold_equation {p : ℝ} (hp : 1 < p)
    (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1) :
    (p * (p / (p - 1)) / 4 * sin (Real.pi / p) ^ 2 +
      4 * lam * cos (Real.pi / p) ^ 4 / (1 + lam) ^ 2 = 1 ↔ lam = endpointLambda p) := by
  have hhi : p ≤ (1000001 : ℝ) / 1000000 := by norm_num at hp1; linarith
  have hp2 : p < 2 := by linarith
  let d := endpointD p
  let u := (1 - lam) / (1 + lam)
  have hd : 0 < d := (endpoint_d_basic hp hp1).1
  have hu : 0 ≤ u := div_nonneg (by linarith) (by linarith)
  have hden : 1 + lam ≠ 0 := by linarith
  have hd2 : d ^ 2 = localD2 p := by
    dsimp only [d]
    rw [endpointD_eq_sqrt_localD2 hp, sq_sqrt
      (sec4b_localD2_pos hp hp2 (localF_positive_endpoint hp hhi)).le]
  have hc4 : 0 < cs p ^ 4 := pow_pos (sec4b_cs_pos hp hp2) _
  have hD : cs p ^ 4 * d ^ 2 = p * dual p / 4 * sn p ^ 2 + cs p ^ 4 - 1 := by
    rw [hd2, sec4b_localD2_eq', mul_div_cancel₀ _ hc4.ne']
  have hid : 4 * lam / (1 + lam) ^ 2 = 1 - u ^ 2 := by
    dsimp only [u]
    field_simp
    <;> ring
  have hlocal : p * (p / (p - 1)) / 4 * sin (Real.pi / p) ^ 2 +
      4 * lam * cos (Real.pi / p) ^ 4 / (1 + lam) ^ 2 =
        p * dual p / 4 * sn p ^ 2 + cs p ^ 4 * (1 - u ^ 2) := by
    rw [← hid]
    unfold dual sn cs
    ring
  have hkey : (p * (p / (p - 1)) / 4 * sin (Real.pi / p) ^ 2 +
      4 * lam * cos (Real.pi / p) ^ 4 / (1 + lam) ^ 2 = 1 ↔ u = d) := by
    rw [hlocal]
    constructor
    · intro hh
      have hs : cs p ^ 4 * (d ^ 2 - u ^ 2) = 0 := by linear_combination hD + hh
      have hs' : d ^ 2 = u ^ 2 := sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left hc4.ne')
      nlinarith
    · intro hh
      rw [hh]
      nlinarith
  rw [hkey]
  change (1 - lam) / (1 + lam) = d ↔ lam = (1 - d) / (1 + d)
  rw [div_eq_iff hden, eq_div_iff (by linarith : 1 + d ≠ 0)]
  constructor <;> intro hh <;> nlinarith

end GKSharp

#print axioms GKSharp.endpoint_threshold_equation
