/- GKSharp/Cited/HV2000.lean - cited input from another paper (Hollenbeck-Verbitsky 2000).
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Defs.Pencil

namespace GKSharp.Cited

/-- B. Hollenbeck, I. E. Verbitsky, Best constants for the Riesz projection, J. Funct. Anal. 175 (2000), 370-392
(refereed), p. 370-371: the Riesz projection `P₊ f(ζ) = Σ_{k ≥ 0} f̂(k) ζ^k` is a continuous operator on `L^p(T)`,
`1 < p < ∞` ("It follows from the classical M. Riesz theorem"), and `‖P₊ f‖_{L^p} ≤ (1/sin(π/p)) ‖f‖_{L^p}` (1.1) "with a
sharp constant"; the lower estimate `‖P₊‖_p ≥ 1/sin(π/p)` is Gohberg-Krupnik's, quoted on p. 371. Together: a bounded
`P₊` with the exact nonnegative-frequency mask exists and `‖P₊‖_p = 1/sin(π/p)`. The paper cites this as [HV]
(sec2_obstacle.tex l.29). -/
axiom hv2000_riesz_norm (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) :
    ∃ P : RieszProjection p, ‖P.plus‖ = 1 / Real.sin (Real.pi / p)

end GKSharp.Cited
