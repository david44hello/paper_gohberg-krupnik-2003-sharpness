/- explicit general proof-step claim, frozen sec5d_monotone.tex:67.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneSine

namespace GKSharp

/-- The paper's general fact sin(x)/x is strictly decreasing on (0,pi). -/
theorem sec5d_sinc_strictAntiOn_proved :
    StrictAntiOn (fun x : ℝ => Real.sin x / x) (Set.Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  have hm : 1 < y / x := (lt_div_iff₀ hx.1).mpr (by simpa using hxy)
  have hcancel : y / x * x = y := by field_simp [hx.1.ne']
  obtain ⟨-, hlt⟩ := sec5d_sine_comparison_proved (y / x) x hm hx.1
    (by rw [hcancel]; exact hy.2)
  rw [hcancel] at hlt
  have h := mul_lt_mul_of_pos_right hlt hx.1
  have heq : y / x * Real.sin x * x = Real.sin x * y := by field_simp [hx.1.ne']
  rw [heq] at h
  exact (div_lt_div_iff₀ hy.1 hx.1).mpr h

end GKSharp
