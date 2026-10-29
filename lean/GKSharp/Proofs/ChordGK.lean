/- the angular chord inequality (sec2_obstacle.tex l.99-102, Lemma "Chord inequality"): a q-subtrigonometric
φ has φ(c - s) + φ(c + s) ≥ 2 cos(qs) φ(c) for 0 < s ≤ π/q (q > 1/2: the paper's standing range q = p/2, p > 1).
Copyright (C) Dave Goel 2026--now.

  Route (differs from the text, which pairs the positive distribution φ'' + q²φ with a tent function ν): φ is continuous
  and trigonometrically q-convex (SectorGK, q > 1/2).
  (i) Short chords, 2qs < π: the three-point inequality at c - s < c < c + s, sin(2qs) = 2 sin(qs) cos(qs), divide by
      sin(qs) > 0.
  (ii) Chords with qs < π: put u = s/2; add (i) at the centres c - u and c + u to 2cos(qu) ≥ 0 times (i) at c, and use
      cos(qs) = 2cos²(qu) - 1.
  (iii) s = π/q: the limit s → π/q from below (φ is continuous). -/
import GKSharp.Proofs.SectorGK

open Real Set Filter Topology

namespace GKSharp

namespace ChordGK

variable {q : ℝ} {φ : ℝ → ℝ}

/-- (i) Short chords, `2qs < π`. -/
theorem chord_short (htc : TrigConvex q φ) (hq : 0 < q) (c : ℝ) {s : ℝ} (hs : 0 < s) (hs2 : q * (2 * s) < π) :
    2 * cos (q * s) * φ c ≤ φ (c - s) + φ (c + s) := by
  have h := htc (c - s) c (c + s) (by linarith) (by linarith)
    (by rw [show c + s - (c - s) = 2 * s by ring]; exact hs2)
  rw [show c + s - (c - s) = 2 * s by ring, show c + s - c = s by ring, show c - (c - s) = s by ring,
    show q * (2 * s) = 2 * (q * s) by ring, sin_two_mul] at h
  have hsin : 0 < sin (q * s) := sin_pos_of_pos_of_lt_pi (mul_pos hq hs) (by linarith [mul_pos hq hs])
  have h' : (2 * cos (q * s) * φ c) * sin (q * s) ≤ (φ (c - s) + φ (c + s)) * sin (q * s) := by
    linear_combination h
  exact le_of_mul_le_mul_right h' hsin

/-- (ii) Every chord with `qs < π`, by one doubling step from (i). -/
theorem chord_lt (htc : TrigConvex q φ) (hq : 0 < q) (c : ℝ) {s : ℝ} (hs : 0 < s) (hs2 : q * s < π) :
    2 * cos (q * s) * φ c ≤ φ (c - s) + φ (c + s) := by
  have hu0 : 0 < s / 2 := by positivity
  have hu2 : q * (2 * (s / 2)) < π := by rw [show 2 * (s / 2) = s by ring]; exact hs2
  have h0 := chord_short htc hq c hu0 hu2
  have h1 := chord_short htc hq (c - s / 2) hu0 hu2
  have h2 := chord_short htc hq (c + s / 2) hu0 hu2
  rw [show c - s / 2 - s / 2 = c - s by ring, show c - s / 2 + s / 2 = c by ring] at h1
  rw [show c + s / 2 - s / 2 = c by ring, show c + s / 2 + s / 2 = c + s by ring] at h2
  have hC : 0 ≤ 2 * cos (q * (s / 2)) :=
    mul_nonneg zero_le_two (cos_nonneg_of_mem_Icc ⟨by linarith [mul_pos hq hu0, pi_pos], by linarith⟩)
  have hcos : cos (q * s) = 2 * cos (q * (s / 2)) ^ 2 - 1 := by
    rw [← cos_two_mul, show 2 * (q * (s / 2)) = q * s by ring]
  rw [hcos]
  nlinarith [mul_le_mul_of_nonneg_left h0 hC]

/-- **Row slice_O30** (sec2_obstacle.tex l.99-102, Lemma "Chord inequality"), for `q > 1/2`: every chord
`0 < s ≤ π/q`. -/
theorem slice_O30_proved (q : ℝ) (hq : 1 / 2 < q) (φ : ℝ → ℝ) (hφ : QSubtrig q φ)
    (c s : ℝ) (hs : 0 < s ∧ s ≤ Real.pi / q) :
    2 * cos (q * s) * φ c ≤ φ (c - s) + φ (c + s) := by
  have hq0 : 0 < q := by linarith
  have htc := SectorGK.qsubtrig_trigConvex hq hφ
  have hcont := SectorGK.qsubtrig_continuous hq hφ
  rcases hs.2.lt_or_eq with hlt | heq
  · exact chord_lt htc hq0 c hs.1 (by rwa [lt_div_iff₀ hq0, mul_comm] at hlt)
  · subst heq
    let F : ℝ → ℝ := fun t => φ (c - t) + φ (c + t) - 2 * cos (q * t) * φ c
    have hFc : Continuous F := by fun_prop
    have hlim : Tendsto F (𝓝[<] (π / q)) (𝓝 (F (π / q))) :=
      hFc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[<] (π / q), 0 ≤ F t := by
      filter_upwards [Ioo_mem_nhdsLT (div_pos pi_pos hq0)] with t ht
      have ht2 : q * t < π := by have := ht.2; rwa [lt_div_iff₀ hq0, mul_comm] at this
      have := chord_lt htc hq0 c ht.1 ht2
      show 0 ≤ φ (c - t) + φ (c + t) - 2 * cos (q * t) * φ c
      linarith
    have h := ge_of_tendsto hlim hev
    change 0 ≤ φ (c - π / q) + φ (c + π / q) - 2 * cos (q * (π / q)) * φ c at h
    linarith

end ChordGK

end GKSharp

