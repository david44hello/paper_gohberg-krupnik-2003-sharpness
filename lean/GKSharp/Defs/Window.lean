/- GKSharp/Defs/Window.lean - the function G_C, the disk D_C and the window half-angle (sec3_nonreal.tex l.8-25).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.GK

namespace GKSharp

/-- `G_C(ζ) = C^p |1 + ζ|^p - |ρ + ζ|^p` (sec3_nonreal.tex l.8; real powers). -/
noncomputable def obstacleG (p C : ℝ) (ρ ζ : ℂ) : ℝ := C ^ p * ‖1 + ζ‖ ^ p - ‖ρ + ζ‖ ^ p

/-- The centre `c = -(C² - ρ)/(C² - 1)` of the disk `D_C` (l.20). -/
noncomputable def diskCentre (C : ℝ) (ρ : ℂ) : ℂ := -(((C : ℂ) ^ 2 - ρ) / ((C : ℂ) ^ 2 - 1))

/-- The squared radius `R² = |c|² - (C² - |ρ|²)/(C² - 1)` of `D_C` (l.20). -/
noncomputable def diskRadiusSq (C : ℝ) (ρ : ℂ) : ℝ :=
  ‖diskCentre C ρ‖ ^ 2 - (C ^ 2 - ‖ρ‖ ^ 2) / (C ^ 2 - 1)

/-- The window half-angle `ψ(C)`: half the angle that `D_C` subtends at `0`, `sin ψ = R/|c|` (l.23-24). -/
noncomputable def windowHalfAngle (C : ℝ) (ρ : ℂ) : ℝ :=
  Real.arcsin (Real.sqrt (diskRadiusSq C ρ) / ‖diskCentre C ρ‖)

end GKSharp
