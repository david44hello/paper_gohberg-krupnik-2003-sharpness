/- GKSharp/Paper/Statements.lean - the claims of the paper, one theorem per claim, with file:line of the frozen
paper short v3.70 (printed numbers such as Lemma 3.1, with the TeX label in parentheses). GKSharp. 20261030.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.GKRoot
import GKSharp.Proofs.GKProps
import GKSharp.Proofs.Window
import GKSharp.Proofs.LemmaI
import GKSharp.Proofs.KConst
import GKSharp.Proofs.GKMinusOne
import GKSharp.Proofs.PencilSymm
import GKSharp.Proofs.PencilL2
import GKSharp.Proofs.PencilDual
import GKSharp.Proofs.CriticalCurve
import GKSharp.Proofs.PolynomialPairs
import GKSharp.Proofs.PencilPairs
import GKSharp.Proofs.MobiusDict
import GKSharp.Proofs.CurveDict
import GKSharp.Proofs.CurveK
import GKSharp.Proofs.GKSymm
import GKSharp.Proofs.LemmaA
import GKSharp.Proofs.LemmaASteps
import GKSharp.Proofs.NormReduce
import GKSharp.Proofs.GKInvariance
import GKSharp.Proofs.ThresholdAlgebra
import GKSharp.Proofs.EndpointBridge
import GKSharp.Proofs.LocalFCertificate
import GKSharp.ComputerChecked
import GKSharp.Proofs.Gamma
import GKSharp.Proofs.GammaDerivative
import GKSharp.Proofs.ContactK
import GKSharp.Proofs.EndpointElementary
import GKSharp.Proofs.PotentialLeaves
import GKSharp.Proofs.StripLeaves
import GKSharp.Proofs.StripInvolution
import GKSharp.Proofs.Sec5Lambda
import GKSharp.Proofs.RealSegment
import GKSharp.Proofs.CircleExtrema
import GKSharp.Proofs.MonotoneElementary
import GKSharp.Proofs.MonotoneSine
import GKSharp.Proofs.MonotoneIdentities
import GKSharp.Proofs.MonotoneSinc
import GKSharp.Proofs.Sec4aBasic
import GKSharp.Proofs.Sec4bAxis
import GKSharp.Proofs.Sec4aOmega
import GKSharp.Proofs.ContactScalar
import GKSharp.Proofs.Sec4bLocal
import GKSharp.Proofs.Sec4Limits
import GKSharp.Proofs.Sec4bChecks
import GKSharp.Proofs.StripCorner
import GKSharp.Proofs.SubharmonicBasic
import GKSharp.Proofs.Envelope
import GKSharp.Proofs.ColeHom
import GKSharp.Cited.HKV21
import GKSharp.Proofs.ColeEnvelope
import GKSharp.Proofs.ContactLog
import GKSharp.Proofs.ThresholdGammaLinks
import GKSharp.Proofs.LocalGapCertificate
import GKSharp.Proofs.StripAnalytic
import GKSharp.Proofs.StripCornerPos
import GKSharp.Proofs.SymmetricTaylor
import GKSharp.Proofs.PotentialCoordinates
import GKSharp.Proofs.GammaCoercive
import GKSharp.Proofs.ObstacleMinimum
import GKSharp.Proofs.Sec4aEndpoint
import GKSharp.Proofs.Sec4Near
import GKSharp.Proofs.Sec4Quad
import GKSharp.Proofs.StripMinimum
import GKSharp.Proofs.StripAssembly
import GKSharp.Proofs.ContactRayMaximum
import GKSharp.Proofs.Sec4aAngular
import GKSharp.Proofs.Sec4aArch
import GKSharp.Proofs.NegativeContact
import GKSharp.Proofs.DiscRescale
import GKSharp.Proofs.ContactExpanded
import GKSharp.Proofs.Select
import GKSharp.Proofs.GammaAsymptotics
import GKSharp.Proofs.ContactHarmonic
import GKSharp.Proofs.Sec4bContactDeriv
import GKSharp.Proofs.StripExtras
import GKSharp.Proofs.NormDisc
import GKSharp.Proofs.TheoremR
import GKSharp.Proofs.Contact
import GKSharp.Proofs.RealSegmentSign
import GKSharp.Proofs.CriticalMaximum
import GKSharp.Proofs.MonotoneBplusA
import GKSharp.Proofs.Sec4Coverage
import GKSharp.Proofs.Sec4Limsup
import GKSharp.Proofs.QEnds
import GKSharp.Defs.PolarProfile
import GKSharp.Proofs.ContactSpecification
import GKSharp.Proofs.ContactScaling
import GKSharp.Proofs.ContactSchur
import GKSharp.Proofs.ContactSign
import GKSharp.Proofs.ContactSmooth
import GKSharp.Proofs.ContactEnvelope
import GKSharp.Proofs.ContactNegativePair
import GKSharp.Proofs.Sec4Continuity
import GKSharp.Proofs.ContactValues
import GKSharp.Proofs.A1
import GKSharp.Proofs.ChordGK
import GKSharp.Proofs.Sec3Geom
import GKSharp.Proofs.MonotoneCurveAlgebra
import GKSharp.Proofs.MonotoneGamma
import GKSharp.Proofs.MonotoneFactorization
import GKSharp.Proofs.MonotonePi
import GKSharp.Proofs.MonotoneLogM
import GKSharp.Proofs.MonotonePiPsi
import GKSharp.Proofs.MonotoneKfLog
import GKSharp.Proofs.InverseCritical
import GKSharp.Proofs.RealGradients
import GKSharp.Proofs.CriticalClassification
import GKSharp.Proofs.Sec4Dual
import GKSharp.Proofs.ReductionStep4
import GKSharp.Proofs.MonotoneBplusB
import GKSharp.Proofs.MonotoneUA
import GKSharp.Proofs.MonotoneLemmaB
import GKSharp.Proofs.MonotoneUB
import GKSharp.Proofs.MonotoneUC
import GKSharp.Proofs.MonotoneUD
import GKSharp.Proofs.MonotoneUE
import GKSharp.Proofs.ReductionStep2
import GKSharp.Proofs.PropositionQFull
import GKSharp.Proofs.GKLowerAll
import GKSharp.Proofs.LemmaEContact
import GKSharp.Proofs.ContactDerivativeFull
import GKSharp.Proofs.MonotoneSign
import GKSharp.Proofs.TheoremC1
import GKSharp.Proofs.SharpA3Final
import GKSharp.Proofs.A2Injective
import GKSharp.Proofs.LocalConsequences
import GKSharp.Proofs.CstarBranch
import GKSharp.Proofs.AxisOrigin
import GKSharp.Proofs.CstarCurve
import GKSharp.Proofs.CstarLambdaSecond
import GKSharp.Proofs.CosineExteriorSupport
import GKSharp.Proofs.ThmBb
import GKSharp.Proofs.TheoremCstar
import GKSharp.Proofs.CstarLambdaPos
import GKSharp.Proofs.EndpointEstimate
import GKSharp.Proofs.EndpointThreshold
import GKSharp.Proofs.PropositionEdge
import GKSharp.Proofs.PropSFinal
import GKSharp.Proofs.TheoremCstarFinal
import GKSharp.Proofs.ThmBa
import GKSharp.Proofs.ThmClass
import GKSharp.Proofs.A2Ift
import GKSharp.Proofs.GKSingular
import GKSharp.Proofs.AngularContact
import GKSharp.Proofs.Sec4JointCont
import GKSharp.Proofs.StripCriterion
import GKSharp.Proofs.RadialMinusOne
import GKSharp.Proofs.Q15Contact
import GKSharp.Proofs.Q15Monotone
import GKSharp.Proofs.Q15Misc
import GKSharp.Proofs.Q19Rows
import GKSharp.Proofs.FinalRows

namespace GKSharp.Paper

open GKSharp ComplexConjugate

/-- sec2_obstacle.tex l.20: "GK_p(α,β) = |α| GK_p(β/α) when α ≠ 0". -/
theorem sec2_gk_homogeneous (p : ℝ) {α : ℂ} (hα : α ≠ 0) (β : ℂ) :
    gkPair p α β = ‖α‖ * gk p (β / α) :=
  gkPair_homog p hα β

/-- sec2_obstacle.tex l.21: "GK_p(0,β) = |β|/sin(π/p)". -/
theorem sec2_gk_pure_minus (p : ℝ) (hp : 1 < p) (β : ℂ) :
    gkPair p 0 β = ‖β‖ / Real.sin (Real.pi / p) :=
  gkPair_zero_left p hp β

/-- sec2_obstacle.tex l.21: "GK_2(α,β) = max(|α|,|β|)". -/
theorem sec2_gk_two (α β : ℂ) : gkPair 2 α β = max ‖α‖ ‖β‖ :=
  gkPair_two α β

/-- eq:GK, sec2_obstacle.tex l.31-33: "GK_p(ρ)² is the larger root of
X² − (1 + |ρ|² + |1−ρ|² cot²θ₀) X + |ρ|² = 0", θ₀ = π/p. -/
theorem eq_GK (p : ℝ) (ρ : ℂ) :
    gkQuad p ρ (gk p ρ ^ 2) = 0 ∧ ∀ X : ℝ, gkQuad p ρ X = 0 → X ≤ gk p ρ ^ 2 :=
  gk_sq_larger_root p ρ

/-- sec2_obstacle.tex l.29: "GK_p(ρ) = GK_{p′}(ρ)" (with l.24: "unchanged by ... replacing p by p′"). -/
theorem sec2_gk_dual (p : ℝ) (hp : 1 < p) (ρ : ℂ) : gk (p / (p - 1)) ρ = gk p ρ :=
  gk_dual p hp ρ

/-- sec2_obstacle.tex l.36: "GK_p(0) = 1/sin(π/p)". -/
theorem sec2_gk_at_zero (p : ℝ) (hp : 1 < p) : gk p 0 = 1 / Real.sin (Real.pi / p) :=
  gk_zero p hp

/-- sec2_obstacle.tex l.37: "for 1 < p < 2, GK_p(−1) = tan(π/(2p))". -/
theorem sec2_gk_at_minus_one {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    gk p (-1) = Real.tan (Real.pi / (2 * p)) :=
  gk_minus_one hp1 hp2

/-- eq:GKreal, sec2_obstacle.tex l.37-42: for real λ (stated for λ ∈ [-1,1), 1 < p < 2; proved for every λ < 1,
1 < p), C = GK_p(λ) satisfies (1 − λ) C = s₀ (C² − λ), s₀ = sin θ₀, and C is the larger root. -/
theorem eq_GKreal {p : ℝ} (hp : 1 < p) {lam : ℝ} (hlam : lam < 1) :
    (1 - lam) * gk p lam = Real.sin (Real.pi / p) * (gk p lam ^ 2 - lam) ∧
      ∀ y : ℝ, (1 - lam) * y = Real.sin (Real.pi / p) * (y ^ 2 - lam) → y ≤ gk p lam :=
  gk_real_eq hp hlam

/-- sec3_nonreal.tex l.12-13 (Section 3: 1 < p, p ≠ 2): "If ρ ≠ 1, then GK > max(1, |ρ|)". -/
theorem sec3_gk_gt_max {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {ρ : ℂ} (hρ : ρ ≠ 1) : max 1 ‖ρ‖ < gk p ρ :=
  gk_gt_max hp hp2 hρ

/-- sec3_nonreal.tex l.20-23: for C > max(1,|ρ|), U_C = {G_C < 0} = {|ζ + ρ| > C|ζ + 1|} is the open disk with
centre c = −(C² − ρ)/(C² − 1) and radius R, R² = |c|² − (C² − |ρ|²)/(C² − 1); it contains −1 (ρ ≠ 1) and does not
contain 0 (here: 0 is not even in its closure). -/
theorem sec3_disk {p C : ℝ} (hp : 0 < p) (ρ : ℂ) (hC : max 1 ‖ρ‖ < C) :
    (∀ ζ : ℂ, obstacleG p C ρ ζ < 0 ↔ C * ‖ζ + 1‖ < ‖ζ + ρ‖) ∧
      (∀ ζ : ℂ, C * ‖ζ + 1‖ < ‖ζ + ρ‖ ↔ ‖ζ - diskCentre C ρ‖ ^ 2 < diskRadiusSq C ρ) ∧
      (ρ ≠ 1 → ‖(-1 : ℂ) - diskCentre C ρ‖ ^ 2 < diskRadiusSq C ρ) ∧
      diskRadiusSq C ρ < ‖diskCentre C ρ‖ ^ 2 :=
  disk_of_obstacle hp ρ hC

/-- (3.2), sec3_nonreal.tex l.25-27: ψ = ψ(C) ∈ (0, π/2) is half the angle that U_C subtends at 0, sin ψ = R/|c|,
and cos² ψ(C) = (C² − |ρ|²)(C² − 1)/|C² − ρ|². -/
theorem eq_3_3 {C : ℝ} {ρ : ℂ} (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    0 < windowHalfAngle C ρ ∧ windowHalfAngle C ρ < Real.pi / 2 ∧
      Real.cos (windowHalfAngle C ρ) ^ 2 = (C ^ 2 - ‖ρ‖ ^ 2) * (C ^ 2 - 1) / ‖(C : ℂ) ^ 2 - ρ‖ ^ 2 :=
  window_cos_sq hρ hC

/-- Lemma 3.1 (label W), sec3_nonreal.tex l.29-31 (Section 3: 1 < p, p ≠ 2): "Let ρ ≠ 1. Then C = GK_p(ρ) is the unique
C > max(1, |ρ|) at which the window has width 2ψ(C) = 2π/max(p, p′)" (existence: `sec3_gk_gt_max`). -/
theorem lemma_W {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {ρ : ℂ} (hρ : ρ ≠ 1) {C : ℝ} (hC : max 1 ‖ρ‖ < C) :
    2 * windowHalfAngle C ρ = 2 * Real.pi / max p (p / (p - 1)) ↔ C = gk p ρ :=
  GKSharp.lemma_W hp hp2 hρ hC

/-- Lemma 5.6 (label I), sec5_sharp_inequality.tex l.129-140 (0 < λ < 1, q = p/2, z' = 1/(λ z̄); any C ≥ 0 and any K):
"D_C(z) − λ^q|z|^p D_C(z') = (C^p + λ^q)(|1+z|^p − λ^{-q}|1+λz|^p), which is positive exactly when |z| > 1/√λ,
i.e. when |w| < √λ. So D_C ≥ 0 on {|z| ≤ 1/√λ} implies D_C > 0 on {|z| > 1/√λ}. In the w-plane, z ↦ z' is
w ↦ λ/w̄." -/
theorem lemma_I {p C K lam : ℝ} (hp : 1 < p) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hC : 0 ≤ C) :
    (∀ z : ℂ, z ≠ 0 →
      critD p C K lam z - lam ^ (p / 2) * ‖z‖ ^ p * critD p C K lam (1 / ((lam : ℂ) * conj z)) =
        (C ^ p + lam ^ (p / 2)) * (‖1 + z‖ ^ p - lam ^ (-(p / 2)) * ‖1 + (lam : ℂ) * z‖ ^ p)) ∧
    (∀ z : ℂ, 0 < (C ^ p + lam ^ (p / 2)) * (‖1 + z‖ ^ p - lam ^ (-(p / 2)) * ‖1 + (lam : ℂ) * z‖ ^ p) ↔
      1 / Real.sqrt lam < ‖z‖) ∧
    (∀ z : ℂ, z ≠ -1 → (1 / Real.sqrt lam < ‖z‖ ↔ ‖mobW lam z‖ < Real.sqrt lam)) ∧
    ((∀ u : ℂ, ‖u‖ ≤ 1 / Real.sqrt lam → 0 ≤ critD p C K lam u) →
      ∀ u : ℂ, 1 / Real.sqrt lam < ‖u‖ → 0 < critD p C K lam u) ∧
    (∀ z : ℂ, z ≠ 0 → z ≠ -1 → 1 + (lam : ℂ) * z ≠ 0 →
      mobW lam (1 / ((lam : ℂ) * conj z)) = (lam : ℂ) / conj (mobW lam z)) :=
  GKSharp.lemma_I hp hlam0 hlam1 hC

/-- eq:K (4.1), sec4a_criterion.tex l.39-42 (1 < p < 2, real λ < 1, C = GK_p(λ), q = p/2, s₀ = sin θ₀, c₀ = −cos θ₀): the two
closed forms of K agree, "K = 2(1 − λ) C s₀^{p−2} c₀^{1−q} (C² + λ)^{q−1} =
2(1 − λ)^p C^p (C² + λ)^{q−1} / (s₀ c₀^{q−1} (C² − λ)^{p−1})" (`kConst` is the first form). -/
theorem eq_K {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hlam1 : lam < 1) :
    kConst p lam =
      2 * (1 - lam) ^ p * gk p lam ^ p * (gk p lam ^ 2 + lam) ^ (p / 2 - 1) /
        (Real.sin (Real.pi / p) * (-Real.cos (Real.pi / p)) ^ (p / 2 - 1) * (gk p lam ^ 2 - lam) ^ (p - 1)) :=
  eq_K_forms hp1 hp2 hlam1

section Pencil

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- P019_paper.tex l.51: "P₋ = I − P₊ retains the frequencies n < 0" (`P.plus` keeps n ≥ 0, including constants). -/
theorem intro_minus_mask (P : RieszProjection p) (f : LpT p) (n : ℤ) :
    fourierCoeff (⇑(rieszMinus P f)) n = if n < 0 then fourierCoeff (⇑f) n else 0 :=
  coeff_minus P f n

/-- P019_paper.tex l.51-52 and l.53: "H = −i(P₊ − P₋)"; "aI + bH = αP₊ + βP₋, α = a − ib, β = a + ib"; "Our H maps the
constant 1 to −i". -/
theorem intro_hilbert_convention (P : RieszProjection p) (a b : ℂ) :
    a • ContinuousLinearMap.id ℂ (LpT p) + b • shiftedHilbert P =
      pencil P (a - Complex.I * b) (a + Complex.I * b) ∧
    shiftedHilbert P (DensityLp.toLpT p 1) = (-Complex.I) • DensityLp.toLpT p 1 :=
  ⟨pencil_hilbert_identity P a b, shiftedHilbert_one P⟩

/-- P019_paper.tex l.58: "For α ≠ 0, homogeneity gives ‖αP₊ + βP₋‖_p = |α| N_p(β/α)". -/
theorem intro_pencil_homogeneous (P : RieszProjection p) {α : ℂ} (hα : α ≠ 0) (β : ℂ) :
    ‖pencil P α β‖ = ‖α‖ * pencilNorm P (β / α) :=
  pencil_norm_homogeneous P α β hα

/-- P019_paper.tex l.58: "The isometry Uf(e^{it}) = e^{−it} f(e^{−it}) interchanges P₊ and P₋". -/
theorem intro_isometry_U (P : RieszProjection p) :
    ∃ U : LpT p → LpT p, Isometry U ∧ Function.Involutive U ∧
      (∀ f g, U (f + g) = U f + U g) ∧ (∀ (a : ℂ) f, U (a • f) = a • U f) ∧
      (∀ f, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure Circ), U f x = fourier (-1) x * f (-x)) ∧
      (∀ f, U (P.plus f) = rieszMinus P (U f)) ∧
      (∀ f, U (rieszMinus P f) = P.plus (U f)) :=
  exists_U P

/-- P019_paper.tex l.58: "the conjugate-linear isometry Jf(e^{it}) = conj f(e^{−it}) preserves both frequency spaces
and conjugates scalar coefficients". -/
theorem intro_isometry_J (P : RieszProjection p) :
    ∃ J : LpT p → LpT p, Isometry J ∧ Function.Involutive J ∧
      (∀ f g, J (f + g) = J f + J g) ∧ (∀ (a : ℂ) f, J (a • f) = star a • J f) ∧
      (∀ f, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure Circ), J f x = star (f (-x))) ∧
      (∀ f, J (P.plus f) = P.plus (J f)) ∧
      (∀ f, J (rieszMinus P f) = rieszMinus P (J f)) :=
  exists_J P

/-- P019_paper.tex l.60 (first identity): "N_p(ρ) = N_p(ρ̄)". -/
theorem intro_norm_conj (P : RieszProjection p) (ρ : ℂ) : pencilNorm P ρ = pencilNorm P (star ρ) :=
  pencilNorm_conj P ρ

/-- P019_paper.tex l.60 (second identity): "N_p(ρ) = |ρ| N_p(1/ρ) (ρ ≠ 0)". -/
theorem intro_norm_inv (P : RieszProjection p) {ρ : ℂ} (hρ : ρ ≠ 0) :
    pencilNorm P ρ = ‖ρ‖ * pencilNorm P (1 / ρ) :=
  pencilNorm_inv P ρ hρ

/-- P019_paper.tex l.62: "If α = 0, the norm is |β|/sin(π/p), since U conjugates P₋ isometrically to P₊ and
‖P₊‖_p = 1/sin(π/p) [HV]" (every β, including β = 0; uses the cited norm of P₊, Hollenbeck-Verbitsky 2000). -/
theorem intro_pencil_zero_left (hp : 1 < p) (P : RieszProjection p) (β : ℂ) :
    ‖pencil P 0 β‖ = ‖β‖ / Real.sin (Real.pi / p) :=
  norm_pencil_zero_left_eq hp P β

/-- P019_paper.tex l.56: "for p = 2, where orthogonality gives ‖αP₊ + βP₋‖₂ = max(|α|, |β|)". -/
theorem intro_pencil_two (hp : p = 2) (P : RieszProjection p) (α β : ℂ) :
    ‖pencil P α β‖ = max ‖α‖ ‖β‖ :=
  norm_pencil_two hp P α β

/-- sec2_obstacle.tex l.57-58: "Testing (eq:pairs) with z ≡ 1, w ≡ 0, and with z ≡ 0, w(ζ) = ζ, respectively, shows that N_p(ρ) ≥ max(1, |ρ|)". -/
theorem sec2_norm_ge_max (P : RieszProjection p) (ρ : ℂ) : max 1 ‖ρ‖ ≤ pencilNorm P ρ :=
  max_one_le_pencilNorm P ρ

/-- P019_paper.tex l.58: "both projections are self-adjoint for the sesquilinear L^p–L^{p′} pairing
⟨f,g⟩ = ∫_𝕋 f ḡ dt/(2π)" (here `∫ f ḡ`; the normalized form is the link `cover_q15_intro_pairing`). -/
theorem intro_selfadjoint {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hp : 1 < p) (hq : q = p / (p - 1))
    (P : RieszProjection p) (Q : RieszProjection q) (f : LpT p) (g : LpT q) :
    (∫ x : Circ, P.plus f x * star (g x)) = (∫ x : Circ, f x * star (Q.plus g x)) ∧
    (∫ x : Circ, rieszMinus P f x * star (g x)) = (∫ x : Circ, f x * star (rieszMinus Q g x)) := by
  subst hq
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  exact ⟨pair_plus hpq P Q f g, pair_minus hpq P Q f g⟩

/-- P019_paper.tex l.60 (third identity): "N_p(ρ) = N_{p′}(ρ̄)", `p′ = p/(p − 1)`. -/
theorem intro_norm_dual [Fact (1 ≤ ENNReal.ofReal (p / (p - 1)))] (hp : 1 < p) (P : RieszProjection p)
    (Q : RieszProjection (p / (p - 1))) (ρ : ℂ) : pencilNorm P ρ = pencilNorm Q (star ρ) :=
  pencilNorm_dual hp P Q ρ

end Pencil

/-- P019_paper.tex l.70: "the exact norms for real a, b (|ρ| = 1)" (and l.80: "the ratios of all real pairs a, b with
ab ≠ 0 (|ρ| = 1, ρ ≠ ±1)"); here for every a − ib ≠ 0. -/
theorem normcorr_ratio_unimodular (a b : ℝ) (ha : (a : ℂ) - Complex.I * b ≠ 0) :
    ‖((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b)‖ = 1 :=
  norm_ratio_of_real a b ha

/-- sec2_obstacle.tex l.47-51: "by density, N_p(ρ) ≤ C if and only if ∫_T G_C(z, w) dθ/2π ≥ 0, G_C(z, w) :=
C^p |z + w̄|^p − |z + ρw̄|^p, for all polynomials z, w with w(0) = 0" (eq:pairs; the positive factor 1/2π omitted). -/
theorem eq_pairs {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) (ρ : ℂ) {C : ℝ}
    (hC : 0 ≤ C) : pencilNorm P ρ ≤ C ↔ PolynomialPairBound p C ρ :=
  norm_iff_polynomial_pairs hp P ρ C hC

/-- sec4b_failure.tex l.105: "4λ/(1+λ)² = 1 − x², and x decreases from 1 to 0 as λ increases from 0 to 1"
(x = (1 − λ)/(1 + λ); so 4λ/(1+λ)² increases on (0,1)). -/
theorem sec4_local_factor_strictMono :
    StrictMonoOn (fun lam : ℝ => 4 * lam / (1 + lam) ^ 2) (Set.Ioo 0 1) :=
  local_factor_strictMono

/-- sec4b_failure.tex l.105, 20 (proof of Lemma 4.6(b); Theorem 4.4): "4λ/(1+λ)² = 1 − x²" (x = (1 − λ)/(1 + λ)),
and "If T(p) > 0, its sign is that of √T(p) − x, which is negative, zero or positive according as λ < λ_loc(p),
λ = λ_loc(p) or λ > λ_loc(p)": for `0 < λ < 1`, `d > 0`, `1 − d² < 4λ/(1+λ)²` holds exactly when `λ > (1 − d)/(1 + d)`
(for every `d > 0`, in particular the paper's `d = √T(p)`). -/
theorem sec4_local_threshold_algebra (lam dd : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hdd : 0 < dd) :
    (1 - dd ^ 2 < 4 * lam / (1 + lam) ^ 2 ↔ (1 - dd) / (1 + dd) < lam) :=
  local_factor_threshold_iff lam dd hlam hdd

/-- sec4b_failure.tex l.141 ("1 − λ_loc(p) = 2d/(1+d) ≤ 2d ≤ 0.03"), route step: with
`λ_loc = (1 − d)/(1 + d)`, `d ≥ 0`, `1 − (1 − d)/(1 + d) = 2d/(1 + d) ≤ 2d` (Lean's kernel check
`sec4_local_gap_kernel` bounds `2d ≤ 0.03`, which gives the printed bound of calculation_certificates.tex l.38). -/
theorem sec4_local_threshold_gap (dd : ℝ) (hdd : 0 ≤ dd) :
    1 - (1 - dd) / (1 + dd) = 2 * dd / (1 + dd) ∧ 2 * dd / (1 + dd) ≤ 2 * dd :=
  local_threshold_gap dd hdd

/-- sec5f_strip.tex l.56-57: with `Ξ(η) = Ξ(0) + e₂η² + c₄η⁴`, `Ξ(0) ≥ 0`, `0 < η ≤ η₁` and `τ₄ ≥ η₁² sup|c₄|`:
"either e₂ > τ₄ ... or Ξ(0,σ) > η₁²(max(0, −e₂) + τ₄) (then Ξ > 0)" (the polynomial inference, for any such reals). -/
theorem sec5_corner_taylor_inference (eta bound value initial e2 c4 tau : ℝ)
    (heta : 0 < eta) (hb : eta ≤ bound) (hi : 0 ≤ initial) (ht : 0 ≤ tau)
    (hc : bound ^ 2 * |c4| ≤ tau)
    (hv : value = initial + e2 * eta ^ 2 + c4 * eta ^ 4)
    (hm : tau < e2 ∨ bound ^ 2 * (max 0 (-e2) + tau) < initial) : 0 < value :=
  corner_taylor_positive eta bound value initial e2 c4 tau heta hb hi ht hc hv hm

/-- sec5f_strip.tex l.44, 67: the strip `p ∈ [p₀, 1.268]` reaches past `3 − √3`, where Theorem 5.2 (label B) (a) takes over:
`3 − √3 < 1.268`. -/
theorem sec5_strip_endpoint : 3 - Real.sqrt 3 < (317 / 250 : ℝ) :=
  strip_upper_endpoint

/-- sec5_sharp_inequality.tex l.22-24: "w = (1 + λz)/(1 + z), a bijection of ℂ \ {−1} onto ℂ \ {λ} with
Im w = −(1−λ) Im z/|1+z|². From w − λ = (1−λ)/(1+z) and 1 − w = (1−λ)z/(1+z)". -/
theorem sec5_mobius {lam : ℝ} (hl : lam < 1) :
    Set.BijOn (mobW lam) {z | z ≠ -1} {w | w ≠ (lam : ℂ)} ∧
    (∀ z : ℂ, (mobW lam z).im = -(1 - lam) * z.im / ‖1 + z‖ ^ 2) ∧
    ∀ z : ℂ, z ≠ -1 → mobW lam z - lam = (1 - lam) / (1 + z) ∧ 1 - mobW lam z = (1 - lam) * z / (1 + z) :=
  ⟨mobW_bijOn hl.ne, mobW_im_norm lam, fun _ hz => mobW_sub lam hz⟩

/-- (5.1), sec5_sharp_inequality.tex l.25-27 (`λ < 1`, `z ≠ −1`, `q = p/2`): "Q := (w − λ)(1 − w̄) = (1−λ)² z̄/|1+z|²,
Re Q^q = (1−λ)^p Re z^q/|1+z|^p, 𝒟_C(z) = |1+z|^p/(1−λ)^p Φ(w)", `Φ(w) = (1−λ)^p(C^p − |w|^p) − K Re Q(w)^q`. -/
theorem eq_5_1 (p C K : ℝ) (hp : 0 < p) {lam : ℝ} (hl : lam < 1) {z : ℂ} (hz : z ≠ -1) :
    mobQ lam (mobW lam z) = (((1 - lam) ^ 2 / ‖1 + z‖ ^ 2 : ℝ) : ℂ) * conj z ∧
    reQPow (mobQ lam (mobW lam z)) (p / 2) = (1 - lam) ^ p * reQPow z (p / 2) / ‖1 + z‖ ^ p ∧
    critD p C K lam z = ‖1 + z‖ ^ p / (1 - lam) ^ p * mobPhi p C K lam (mobW lam z) :=
  ⟨mobQ_mobW lam hz, reQPow_mobQ p hl hz, critD_eq_mobPhi p C K hl hz⟩

/-- sec5_sharp_inequality.tex l.28-31: "For w = ρe^{iφ} ... Q = −(ρ² + λ) + (1+λ)ρ cos φ + i(1−λ)ρ sin φ runs over an
ellipse E_ρ"; "Q(w̄) = conj Q(w)". -/
theorem sec5_ellipse (lam ρ φ : ℝ) (w : ℂ) :
    mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) =
      ((-(ρ ^ 2 + lam) + (1 + lam) * ρ * Real.cos φ : ℝ) : ℂ) + (((1 - lam) * ρ * Real.sin φ : ℝ) : ℂ) * Complex.I ∧
    mobQ lam (conj w) = conj (mobQ lam w) :=
  ⟨mobQ_polar lam ρ φ, mobQ_conj lam w⟩

/-- (5.3), sec5_sharp_inequality.tex l.35-40, algebraic part: for `z = r e^{−iθ}` and
`v = e^{iω} + λe^{−iω}`, `ω = (1−q)θ`: "Im(v̄ w) = (1−λ) D(θ, r)/|1+z|²", `D(θ, r) = (1+λ) r s₂ − (1 + λr²) s₁`. -/
theorem eq_5_3_cross (p lam θ r : ℝ) :
    (conj (curveV p lam θ) * mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I))).im =
      (1 - lam) * curveD p lam θ r / ‖1 + (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)‖ ^ 2 :=
  cross_curveD p lam θ r

/-- sec5_sharp_inequality.tex l.41-42 (`0 < θ < π`, `r > 0`, `λ < 1`): "w = τv with τ = ρ/|v| > 0, if and only if
D(θ, r) = 0". -/
theorem sec5_critical_iff {p lam θ r : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl1 : lam < 1) (hθ0 : 0 < θ)
    (hθ : θ < Real.pi) (hr : 0 < r) :
    (∃ τ : ℝ, 0 < τ ∧ mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)) = (τ : ℂ) * curveV p lam θ) ↔
      curveD p lam θ r = 0 :=
  critical_iff hp1 hp2 hl1 hθ0 hθ hr

/-- (5.4), sec5_sharp_inequality.tex l.42-44: at `w = τv` (`τ ≥ 0`): `v = (1+λ) cos ω + i(1−λ) sin ω`,
`|v|² = 1 + λ² + 2λ cos 2ω`, "|Q| sin θ = (1−λ) Im w = (1−λ)²τ sin ω, ρ = τ|v|, w − λw̄ = (1−λ²)τe^{iω},
Re[e^{−iω}(w + λw̄)] = τ|v|²" (θ = arg Q). -/
theorem eq_5_4 (p lam θ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    curveV p lam θ = (((1 + lam) * Real.cos ((1 - p / 2) * θ) : ℝ) : ℂ) +
      (((1 - lam) * Real.sin ((1 - p / 2) * θ) : ℝ) : ℂ) * Complex.I ∧
    ‖curveV p lam θ‖ ^ 2 = 1 + lam ^ 2 + 2 * lam * Real.cos (2 * ((1 - p / 2) * θ)) ∧
    (mobQ lam ((τ : ℂ) * curveV p lam θ)).im = (1 - lam) * ((τ : ℂ) * curveV p lam θ).im ∧
    (1 - lam) * ((τ : ℂ) * curveV p lam θ).im = (1 - lam) ^ 2 * τ * Real.sin ((1 - p / 2) * θ) ∧
    ‖(τ : ℂ) * curveV p lam θ‖ = τ * ‖curveV p lam θ‖ ∧
    (τ : ℂ) * curveV p lam θ - lam * conj ((τ : ℂ) * curveV p lam θ) =
      (((1 - lam ^ 2) * τ : ℝ) : ℂ) * Complex.exp ((((1 - p / 2) * θ : ℝ) : ℂ) * Complex.I) ∧
    (Complex.exp (-((((1 - p / 2) * θ : ℝ) : ℂ)) * Complex.I) *
      ((τ : ℂ) * curveV p lam θ + lam * conj ((τ : ℂ) * curveV p lam θ))).re = τ * ‖curveV p lam θ‖ ^ 2 ∧
    ∀ Q : ℂ, ‖Q‖ * Real.sin (Complex.arg Q) = Q.im :=
  curve_identities p lam θ hτ

/-- sec5_sharp_inequality.tex l.47 (`1 < p < 2`, `0 < θ < π`): "0 < s₁ < s₂, as s₂ − s₁ = 2 cos(θ/2) sin(εθ/2)",
`s₁ = sin((1−q)θ)`, `s₂ = sin(qθ)`, `ε = p − 1`. -/
theorem sec5_sines {p θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    0 < Real.sin ((1 - p / 2) * θ) ∧ Real.sin ((1 - p / 2) * θ) < Real.sin (p / 2 * θ) ∧
      Real.sin (p / 2 * θ) - Real.sin ((1 - p / 2) * θ) = 2 * Real.cos (θ / 2) * Real.sin ((p - 1) * θ / 2) :=
  curve_sines hp1 hp2 hθ0 hθ

/-- sec5_sharp_inequality.tex l.47-49 (`−1 < λ < 1`): "D(θ, 0) = −s₁ < 0 < (1+λ)(s₂ − s₁) = D(θ, 1) and
∂_r D = (1+λ)s₂ − 2λrs₁ > 0 on [0, 1], so D(θ, ·) has exactly one zero R(θ) ∈ (0, 1)". -/
theorem sec5_critical_root {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hl : -1 < lam) (hl1 : lam < 1) :
    curveD p lam θ 0 = -Real.sin ((1 - p / 2) * θ) ∧ -Real.sin ((1 - p / 2) * θ) < 0 ∧
    0 < (1 + lam) * (Real.sin (p / 2 * θ) - Real.sin ((1 - p / 2) * θ)) ∧
    curveD p lam θ 1 = (1 + lam) * (Real.sin (p / 2 * θ) - Real.sin ((1 - p / 2) * θ)) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (curveD p lam θ)
      ((1 + lam) * Real.sin (p / 2 * θ) - 2 * lam * r * Real.sin ((1 - p / 2) * θ)) r ∧
      0 < (1 + lam) * Real.sin (p / 2 * θ) - 2 * lam * r * Real.sin ((1 - p / 2) * θ)) ∧
    0 < curveR p lam θ ∧ curveR p lam θ < 1 ∧ curveD p lam θ (curveR p lam θ) = 0 ∧
    ∀ r ∈ Set.Icc (0 : ℝ) 1, curveD p lam θ r = 0 → r = curveR p lam θ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := curve_root_unique hp1 hp2 hθ0 hθ hl hl1
  exact ⟨h1, h2, h3, h4, fun r hr => ⟨curveD_hasDerivAt p lam θ r, h5 r hr⟩, h6, h7, h8, h9⟩

/-- sec5_sharp_inequality.tex l.49 (`λ = −1`): "D = −(1 − r²)s₁" (and the root formula gives `R = 1`). -/
theorem sec5_critical_root_minus_one {p θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (∀ r, curveD p (-1) θ r = -(1 - r ^ 2) * Real.sin ((1 - p / 2) * θ)) ∧ curveR p (-1) θ = 1 :=
  curve_root_minus_one hp1 hp2 hθ0 hθ

/-- sec5_sharp_inequality.tex l.49-52 (`−1 ≤ λ < 1`): "In both cases R = 2s₁/((1+λ)s₂ + √((1+λ)²s₂² − 4λs₁²)), with
discriminant ≥ (1−λ)²s₁² > 0" (the formula is a zero of `D(θ, ·)` in `(0, 1]`). -/
theorem sec5_critical_root_formula {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hl : -1 ≤ lam) (hl1 : lam < 1) :
    (1 - lam) ^ 2 * Real.sin ((1 - p / 2) * θ) ^ 2 ≤
      (1 + lam) ^ 2 * Real.sin (p / 2 * θ) ^ 2 - 4 * lam * Real.sin ((1 - p / 2) * θ) ^ 2 ∧
    0 < (1 - lam) ^ 2 * Real.sin ((1 - p / 2) * θ) ^ 2 ∧
    0 < curveR p lam θ ∧ curveR p lam θ ≤ 1 ∧ curveD p lam θ (curveR p lam θ) = 0 :=
  curve_root_formula hp1 hp2 hθ0 hθ hl hl1

/-- sec5_sharp_inequality.tex l.52-53 (`−1 ≤ λ < 1`): "so R is real-analytic, R(π⁻) = 1, and r₀ := R(0⁺) ∈ (0, 1]"
(`r₀` is the root formula at `s₁ = 1 − q`, `s₂ = q`). -/
theorem sec5_critical_root_regular {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    (∀ θ, 0 < θ → θ < Real.pi → AnalyticAt ℝ (curveR p lam) θ) ∧
    Filter.Tendsto (curveR p lam) (nhdsWithin Real.pi (Set.Iio Real.pi)) (nhds 1) ∧
    Filter.Tendsto (curveR p lam) (nhdsWithin 0 (Set.Ioi 0)) (nhds (curveRoot lam (1 - p / 2) (p / 2))) ∧
    0 < curveRoot lam (1 - p / 2) (p / 2) ∧ curveRoot lam (1 - p / 2) (p / 2) ≤ 1 :=
  ⟨fun _ h0 h1 => curve_root_analytic hp1 hp2 hl hl1 h0 h1, curve_root_limits hp1 hp2 hl hl1⟩

/-- sec5_sharp_inequality.tex l.53-55 (`−1 ≤ λ < 1`, `λ ≠ 0`; "its" = of D(θ, ·)): "For λ ≠ 0 its zeros have product
1/λ: for λ < 0 the other zero is negative; for λ > 0 the other one, 1/(λR), gives the image of Re^{−iθ} under the
inversion z ↦ 1/(λz̄)". -/
theorem sec5_critical_zero_product {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hl0 : lam ≠ 0) :
    (∀ r, curveD p lam θ r = -lam * Real.sin ((1 - p / 2) * θ) * (r - curveR p lam θ) *
      (r - 1 / (lam * curveR p lam θ))) ∧
    (lam < 0 → ∀ r, 0 < r → curveD p lam θ r = 0 → r = curveR p lam θ) ∧
    (0 < lam → curveD p lam θ (1 / (lam * curveR p lam θ)) = 0 ∧
      1 / ((lam : ℂ) * conj (curveZ p lam θ)) =
        ((1 / (lam * curveR p lam θ) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)) :=
  curve_root_product hp1 hp2 hθ0 hθ hl hl1 hl0

/-- (5.5), sec5_sharp_inequality.tex l.57-60 (`−1 ≤ λ < 1`, `0 < θ < π`): "On the critical curve, with r = R(θ),
A_θ := |1 + z_θ|² = 1 + 2r cos θ + r² and B := |1 + λz_θ|², |Q| = (1−λ)²r/A_θ, ρ² = B/A_θ, τ = r sin θ/(A_θ s₁),
2τ cos ω − 1 = Y/(A_θ s₁), Y := 2rs₂ − (1 + r²)s₁ = (1−λ) r (s₂ − rs₁) > 0" (with `w = τv`). -/
theorem eq_5_5 {p lam θ r : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) (hr : r = curveR p lam θ) :
    ‖1 + (r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)‖ ^ 2 = 1 + 2 * r * Real.cos θ + r ^ 2 ∧
    ‖mobQ lam (mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)))‖ =
      (1 - lam) ^ 2 * r / (1 + 2 * r * Real.cos θ + r ^ 2) ∧
    ‖mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I))‖ ^ 2 =
      ‖1 + (lam : ℂ) * ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I))‖ ^ 2 / (1 + 2 * r * Real.cos θ + r ^ 2) ∧
    mobW lam ((r : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)) =
      ((r * Real.sin θ / ((1 + 2 * r * Real.cos θ + r ^ 2) * Real.sin ((1 - p / 2) * θ)) : ℝ) : ℂ) *
        curveV p lam θ ∧
    2 * (r * Real.sin θ / ((1 + 2 * r * Real.cos θ + r ^ 2) * Real.sin ((1 - p / 2) * θ))) *
        Real.cos ((1 - p / 2) * θ) - 1 =
      (2 * r * Real.sin (p / 2 * θ) - (1 + r ^ 2) * Real.sin ((1 - p / 2) * θ)) /
        ((1 + 2 * r * Real.cos θ + r ^ 2) * Real.sin ((1 - p / 2) * θ)) ∧
    2 * r * Real.sin (p / 2 * θ) - (1 + r ^ 2) * Real.sin ((1 - p / 2) * θ) =
      (1 - lam) * r * (Real.sin (p / 2 * θ) - r * Real.sin ((1 - p / 2) * θ)) ∧
    0 < 2 * r * Real.sin (p / 2 * θ) - (1 + r ^ 2) * Real.sin ((1 - p / 2) * θ) :=
  dict_identities hp1 hp2 hl hl1 hθ0 hθ hr

/-- sec2_obstacle.tex l.27: "GK_p(ρ̄) = GK_p(ρ)" (used at P019_paper.tex l.62, "the corresponding symmetries of
GK_p"). -/
theorem sec2_gk_conj (p : ℝ) (ρ : ℂ) : gk p (star ρ) = gk p ρ :=
  gk_conj p ρ

/-- sec5d_monotone.tex l.159-160: "GK_p(λ) = |λ| GK_p(1/λ) (in (2.1), λ ↦ 1/λ amounts to X ↦ X/λ²)"
(stated for every complex `ρ ≠ 0`). -/
theorem sec5_gk_inv (p : ℝ) {ρ : ℂ} (hρ : ρ ≠ 0) : gk p ρ = ‖ρ‖ * gk p (1 / ρ) :=
  gk_inv p hρ

/-- sec5d_monotone.tex l.158-159: "λ = 1 is trivial (P₊ + P₋ = I, GK_p(1) = 1)"; P019_paper.tex l.62: "for $\rho=1$
both sides equal $1$": `N_p(1) = 1 = GK_p(1)`. -/
theorem sec5_lambda_one {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) :
    pencilNorm P 1 = 1 ∧ gk p 1 = 1 :=
  ⟨pencilNorm_one P, gk_one p⟩

/-- (5.7), sec5_sharp_inequality.tex l.104-106 (`−1 ≤ λ < 1`, `0 < θ < π`):
"K_f(θ) := 2(1−λ)^p ρ^{p−2} τ |Q|^{1−q}/(2τ cos ω − 1) = 2(1−λ)² sin θ r^{2−q} B^{q−1}/Y (r = R(θ))";
`curveKf` is the first form. -/
theorem eq_5_7 {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    curveKf p lam θ =
      2 * (1 - lam) ^ 2 * Real.sin θ * curveR p lam θ ^ (2 - p / 2) *
        (‖1 + (lam : ℂ) * curveZ p lam θ‖ ^ 2) ^ (p / 2 - 1) /
        (2 * curveR p lam θ * Real.sin (p / 2 * θ) - (1 + curveR p lam θ ^ 2) * Real.sin ((1 - p / 2) * θ)) :=
  curveKf_eq hp1 hp2 hl hl1 hθ0 hθ

/-- Proof of Theorem 5.1 (label C1), sec5d_monotone.tex l.151-153 (`λ = −1`, `ε = p − 1`): "R ≡ 1, B = 4 sin²(θ/2),
Y = 4 cos(θ/2) sin(εθ/2), and (5.7) gives K_f = 2^p sin^ε(θ/2)/sin(εθ/2)". -/
theorem thmC1_Kf_minus_one {p θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    curveR p (-1) θ = 1 ∧
    ‖1 + ((-1 : ℝ) : ℂ) * curveZ p (-1) θ‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 ∧
    2 * curveR p (-1) θ * Real.sin (p / 2 * θ) - (1 + curveR p (-1) θ ^ 2) * Real.sin ((1 - p / 2) * θ) =
      4 * Real.cos (θ / 2) * Real.sin ((p - 1) * θ / 2) ∧
    curveKf p (-1) θ = 2 ^ p * Real.sin (θ / 2) ^ (p - 1) / Real.sin ((p - 1) * θ / 2) :=
  curveKf_minus_one hp1 hp2 hθ0 hθ

/-- Proof of Theorem 5.1 (label C1), sec5d_monotone.tex l.153 (`λ = −1`): "(log K_f)′ =(ε/2)[cot(θ/2) − cot(εθ/2)] < 0";
hence `K_f` is strictly decreasing on `(0, π)`. -/
theorem thmC1_Kf_minus_one_decreasing {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∀ θ, 0 < θ → θ < Real.pi →
      HasDerivAt (fun x => Real.log (curveKf p (-1) x))
        ((p - 1) / 2 * (Real.cot (θ / 2) - Real.cot ((p - 1) * θ / 2))) θ ∧
      (p - 1) / 2 * (Real.cot (θ / 2) - Real.cot ((p - 1) * θ / 2)) < 0) ∧
    StrictAntiOn (curveKf p (-1)) (Set.Ioo 0 Real.pi) :=
  curveKf_minus_one_deriv hp1 hp2

/-- Lemma 5.4 (label A; cases λ ≤ 0 and λ > 0), sec5_sharp_inequality.tex l.64-67, the bracket of (5.6) (`1 < p < 2`, `−1 ≤ λ < 1`, `0 < θ < π`):
"(1−q)(1+λ)² cos(qθ) − |v|² sin ω/sin θ < 0", `q = p/2`, `ω = (1−q)θ`, `v = e^{iω} + λe^{−iω}`. -/
theorem lemmaA_bracket {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (1 - p / 2) * (1 + lam) ^ 2 * Real.cos (p / 2 * θ) -
      ‖curveV p lam θ‖ ^ 2 * (Real.sin ((1 - p / 2) * θ) / Real.sin θ) < 0 :=
  GKSharp.lemmaA_bracket hp1 hp2 hl hl1 hθ0 hθ

/-- P019_paper.tex l.62: "these identities reduce the question to |ρ| ≤ 1 and 1 < p < 2": with `q ∈ {p, p′}`,
`1 < q ≤ 2`, `r ∈ {ρ, ρ̄, 1/ρ, 1/ρ̄}`, `|r| ≤ 1` and `s = max(1, |ρ|)`, both `N_p(ρ) = s N_q(r)` and `GK_p(ρ) = s GK_q(r)`
(uses the cited `P₊` on `L^{p′}` when `p > 2`). -/
theorem intro_norm_reduce {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) (ρ : ℂ) :
    ∃ (q : ℝ) (hq : Fact (1 ≤ ENNReal.ofReal q)) (Q : @RieszProjection q hq) (r : ℂ) (s : ℝ),
      (q = p ∨ q = p / (p - 1)) ∧ 1 < q ∧ q ≤ 2 ∧
      (r = ρ ∨ r = star ρ ∨ r = 1 / ρ ∨ r = 1 / star ρ) ∧ ‖r‖ ≤ 1 ∧
      s = max 1 ‖ρ‖ ∧
      pencilNorm P ρ = s * @pencilNorm q hq Q r ∧ gk p ρ = s * gk q r :=
  pencil_and_gk_reduce hp P ρ

/-- Lemma 5.4 (label A), sec5_sharp_inequality.tex l.76: "tan y/y increases" (on `(0, π/2)`). -/
theorem lemmaA_tan_div_increasing : StrictMonoOn (fun y => Real.tan y / y) (Set.Ioo 0 (Real.pi / 2)) :=
  tan_div_self_strictMonoOn

/-- Lemma 5.4 (label A), sec5_sharp_inequality.tex l.75-76 (`0 < q < 1`, `0 < θ < π/2`): "tan(qθ)/(qθ) < tan θ/θ". -/
theorem lemmaA_tan_step {q θ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi / 2) :
    Real.tan (q * θ) / (q * θ) < Real.tan θ / θ :=
  tan_div_lt_of_lt hq0 hq1 hθ0 hθ

/-- sec2_obstacle.tex l.22-23: "The squared Frobenius norm and the squared modulus of the determinant of
this matrix are |α|² + |β|² + |β − α|² cot²(π/p) and |αβ|²". -/
theorem sec2_gk_matrix_invariants (p : ℝ) (α β : ℂ) :
    ∑ i, ∑ j, ‖gkMatrix p α β i j‖ ^ 2 = ‖α‖ ^ 2 + ‖β‖ ^ 2 + ‖β - α‖ ^ 2 * Real.cot (Real.pi / p) ^ 2 ∧
    ‖(gkMatrix p α β).det‖ ^ 2 = ‖α * β‖ ^ 2 :=
  gkMatrix_frobenius_det p α β

/-- sec2_obstacle.tex l.24: the invariants "are unchanged by interchanging α, β, conjugating both
coefficients", so `GK_p(α, β) = GK_p(β, α) = GK_p(ᾱ, β̄)` (`1 < p`). -/
theorem sec2_gk_swap_conj {p : ℝ} (hp : 1 < p) (α β : ℂ) :
    gkPair p α β = gkPair p β α ∧ gkPair p (conj α) (conj β) = gkPair p α β :=
  ⟨gkPair_swap hp α β, gkPair_conj hp α β⟩

section ThresholdBridge
open GKSharp.Threshold

/-- endpoint_estimate.tex:12–17 and P019_paper.tex:87–88: the endpoint D
equals the square root of the global local-threshold radicand. -/
theorem endpoint_threshold_radicand {p : ℝ} (hp : 1 < p) :
    endpointD p = Real.sqrt (localD2 p) :=
  endpointD_eq_sqrt_localD2 hp

/-- sec4b_failure.tex:100: F>0 on the explicit interval (1, 1 + 10^{−6}]. -/
theorem sec4_localF_endpoint {p : ℝ} (hp : 1 < p) (hhi : p ≤ 1000001 / 1000000) :
    0 < localF p := localF_positive_endpoint hp hhi

/-- endpoint_estimate.tex:12–17 and P019_paper.tex:87–88: the endpoint
formula denotes the global lambda_loc on the entire endpoint interval. -/
theorem endpoint_threshold_identification {p : ℝ} (hp : 1 < p) (hhi : p ≤ 1000001 / 1000000) :
    endpointLambda p = lambdaLoc p := endpointLambda_eq_lambdaLoc hp hhi

/-- sec4a_criterion.tex:40 and endpoint_estimate.tex:42–51: the absolute-cosine
contact constant is the shared K constant for 1 < p < 2. -/
theorem endpoint_K_identification {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (lam : ℝ) :
    contactK p lam = kConst p lam := contactK_eq_kConst hp hp2 lam

/-- sec4b_failure.tex:141,calculation_certificates.tex:38: the clipped
square-root upper bound is exactly the rational radicand bound. This proves
the reduction, not the remaining bound on localD2 over the compact interval. -/
theorem sec4_local_gap_squared (p : ℝ) :
    (2 * Real.sqrt (max (localD2 p) 0) ≤ 3 / 100 ↔ localD2 p ≤ 9 / 40000) :=
  clipped_sqrt_gap_iff (localD2 p)

/-- sec4b_failure.tex:94,102–103;calculation_certificates.tex:27: the lower
pc bracket endpoint has positive F. -/
theorem sec4_localF_bracket_lower : 0 < localF (1213490304 / 1000000000) :=
  localF_bracket_lower

/-- sec4b_failure.tex:94,102–103;calculation_certificates.tex:27: the upper
pc bracket endpoint has negative F. -/
theorem sec4_localF_bracket_upper : localF (1213490305 / 1000000000) < 0 :=
  localF_bracket_upper

end ThresholdBridge

section PotentialLeaves
open Real
/-- sec2_obstacle.tex:51–55; both squared bases and exact pair factorization. -/
theorem slice_O09 {p : ℝ} (hp : 1 < p) (C : ℝ) (ρ z w : ℂ) (hzw : z * w ≠ 0) :
    let y := log (‖z‖ / ‖w‖)
    let t := Complex.arg (z * w)
    ‖z + star w‖ ^ 2 = ‖z * w‖ * (2 * cosh y + 2 * cos t) ∧
    ‖z + ρ * star w‖ ^ 2 = ‖z * w‖ *
      (exp y + ‖ρ‖ ^ 2 * exp (-y) + 2 * (star ρ * unitPoint t).re) ∧
    pairObstacle p C ρ z w = ‖z * w‖ ^ (p / 2) * gamma p C ρ y t :=
  GKSharp.slice_O09_proved hp C ρ z w hzw

/-- sec2_obstacle.tex:60; real ratio gives an even obstacle. -/
theorem slice_O13 (p C lam t : ℝ) : obstacle p C (lam : ℂ) (-t) = obstacle p C (lam : ℂ) t :=
  GKSharp.slice_O13_proved p C lam t

/-- sec2_obstacle.tex:60–61; radial expression and actual infimum. -/
theorem slice_O14 (p C : ℝ) (ρ : ℂ) (y t : ℝ) :
    gamma p C ρ y t = (exp y) ^ (-(p / 2)) * obstacleG p C ρ ((exp y : ℂ) * unitPoint t) ∧
    obstacle p C ρ t = sInf {v : ℝ | ∃ r : ℝ, 0 < r ∧
      v = r ^ (-(p / 2)) * obstacleG p C ρ ((r : ℂ) * unitPoint t)} :=
  GKSharp.slice_O14_proved p C ρ y t

/-- sec4a_criterion.tex:39–50; K closed form and positive-base derivative. -/
theorem slice_O36 {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (lam : ℝ) (hlam : -1 ≤ lam ∧ lam < 1) :
    let C := gk p (lam : ℂ)
    kConst p lam = 2 * (1 - lam) ^ p * C ^ p * (C ^ 2 + lam) ^ (p / 2 - 1) /
      (sin (Real.pi / p) * |cos (Real.pi / p)| ^ (p / 2 - 1) * (C ^ 2 - lam) ^ (p - 1)) ∧
    (∀ y t : ℝ, 0 < 2 * cosh y + 2 * cos t →
      0 < exp y + lam ^ 2 * exp (-y) + 2 * lam * cos t →
      deriv (gamma p C (lam : ℂ) y) t =
        -2 * (p / 2) * sin t *
          (C ^ p * (2 * cosh y + 2 * cos t) ^ (p / 2 - 1) -
            lam * (exp y + lam ^ 2 * exp (-y) + 2 * lam * cos t) ^ (p / 2 - 1))) :=
  GKSharp.slice_O36_proved hp hp2 lam hlam

/-- sec4a_criterion.tex:51; projection endpoint K simplification. -/
theorem slice_O37 {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    kConst p 0 = 2 * |cos (Real.pi / p)| ^ (1 - p / 2) / sin (Real.pi / p) :=
  GKSharp.slice_O37_proved hp hp2

/-- endpoint_estimate.tex:11,17; full angular range and inversion. -/
theorem slice_E02 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    0 < endpointA p ∧ endpointA p < 3.2 * 10 ^ (-6 : ℤ) ∧
      p = Real.pi / (Real.pi - endpointA p) :=
  GKSharp.slice_E02_proved hp hp1

/-- endpoint_estimate.tex:22–25; four enclosure ingredients. -/
theorem slice_E05 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    a ^ 2 * (1 - a ^ 2 / 3) ≤ sin a ^ 2 ∧
    Real.pi / (4 * a) - 2 ≤ p * Real.pi / (4 * a) - 1 - cos a ^ 2 ∧
    (cos a) ^ (-4 : ℤ) ≤ 1 + 3 * a ^ 2 ∧
    (1 + a / 3) * (1 + 3 * a ^ 2) ≤ 1 + a :=
  GKSharp.slice_E05_proved hp hp1

end PotentialLeaves

section StripRows
open Set GKSharp.Threshold GKSharp.ComputerChecked
/-- sec5f_strip.tex l.65-66: "g ≥ (T₁ + 0.95)/0.05^q − k, respectively (as ψ_p ≥ 1)", where ψ_p(x) = (1 − (1−x)^p)/x (l.22);
here for 1 ≤ p and 0 ≤ x ≤ 1. -/
theorem phi_ge_one (p x : ℝ) (hp : 1 ≤ p) (hx : x ∈ Icc (0 : ℝ) 1) : 1 ≤ phi p x :=
  GKSharp.phi_ge_one_proved p x hp hx

/-- calculation_certificates.tex l.35: "The domains of Cases 1 and 2 of Proposition 5.14 share boundary segments and
together cover the required region". The two domains are table rows l.31-32: "g, Case 1" p∈[p₀⁻,p₁], 0<δ≤0.05;
"g, Case 2" [p₀⁻,1.268]×[0.05,1] ∪ [p₁,1.268]×[0,0.05] in (p,δ) (l.15: p₀⁻ = 1.2336025 = `a0`, p₁ = 1.2341027 = `b1`).
(The row covers p ∈ [p₀, 1.268], 0 < δ < 1, with Case 1 taken from p₀⁻.) -/
theorem strip_cover (p delta : ℝ) (hp : p ∈ Icc p0 (317 / 250 : ℝ))
    (hp0 : a0 < p0) (hd : delta ∈ Ioo (0 : ℝ) 1) :
    (p ∈ Icc a0 b1 ∧ delta ∈ Ioc (0 : ℝ) (1 / 20)) ∨ bulkDomain p delta :=
  GKSharp.strip_cover_proved p delta hp hp0 hd

/-- sec5f_strip.tex l.58-60: "The quotients are evaluated without division by η through the entire function
E(z) = (1 − e^{−z})/z: δ = ηE(η), s = σE(ση)/E(η), 1 − s = e^{−ση}(1−σ)E((1−σ)η)/E(η), sψ_p(sδ) = pσE(pση)/E(η)"
(`exprel` is E). -/
theorem exprel_coordinate_identities (p eta sigma : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hs : sigma ∈ Ioo (0 : ℝ) 1) :
    deltaEta eta = eta * exprel eta ∧
    1 - sEta eta sigma = Real.exp (-sigma * eta) * (1 - sigma) *
      exprel ((1 - sigma) * eta) / exprel eta ∧
    sEta eta sigma * phi p (sEta eta sigma * deltaEta eta) =
      p * sigma * exprel (p * sigma * eta) / exprel eta :=
  GKSharp.exprel_coordinate_identities_proved p eta sigma hp hp2 hs

/-- sec5f_strip.tex l.24-26: "At δ = 0, g(0, s) = p(A + s)/(s(1−s))^q − 2^q s₀^{p−2} c₀^{1−q}". -/
theorem g_zero (p s : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    g p 0 s = omegaFirst p s - kappaZero p :=
  GKSharp.g_zero_proved p s hp hp2

/-- sec5f_strip.tex l.23: "C = C(δ) is the root near 1 of s₀C² − δC − s₀(1 − δ) = 0"; for λ = 1 − δ this is
C = GK_p(λ) (sec4a_criterion.tex l.84-85: "Equation (2.2) gives the exact relations s₀(C² − 1) = δ(C − s₀)").
`cDelta` is this root, continued also to δ < 0; the row is the side 0 ≤ δ < 1. -/
theorem cDelta_eq_gk (p delta : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hd : delta ∈ Ico (0 : ℝ) 1) : cDelta p delta = gk p ((1 - delta : ℝ) : ℂ) :=
  GKSharp.cDelta_eq_gk_proved p delta hp hp2 hd

/-- sec5f_strip.tex l.65-66: "Near the ends s ≤ 0.05 and s ≥ 0.95 we have g ≥ T₁/0.05^q − k and
g ≥ (T₁ + 0.95)/0.05^q − k, respectively (as ψ_p ≥ 1)" (`lowTail` and `highTail` are the two right sides). -/
theorem g_tail_bounds (p delta s : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hd : delta ∈ Icc (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    (s ≤ 1 / 20 → lowTail p delta ≤ g p delta s) ∧
    (19 / 20 ≤ s → highTail p delta ≤ g p delta s) :=
  GKSharp.g_tail_bounds_proved p delta s hp hp2 hd hs

/-- Proposition 5.14 (label strip), proof, "Case 2", sec5f_strip.tex l.68-70: "Here we use interval arithmetic on boxes in
(p, δ, s) ... A mean-value form proves g>0 on boxes with 0.05≤s≤0.95, and the bounds at the ends in s prove it on
rectangles in (p,δ) for s≤0.05 and s≥0.95"; calculation_certificates.tex l.32 (row "g, Case 2": "g>0 for every 0<s<1";
"13168 mean-value boxes and 714 tail rectangles"). -/
theorem bulk_positive (hc : CheckStripBulkMiddle) (ht : CheckStripBulkTails)
    (p delta s : ℝ) (hp : bulkDomain p delta) (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < g p delta s :=
  GKSharp.bulk_positive_proved hc ht p delta s hp hs

/-- sec5f_strip.tex l.63-64: "σ ∈ [0.045, 0.95], which covers s ∈ [0.05, 0.95] since sE(η) ≤ σ ≤ s". -/
theorem sigma_core_cover (eta sigma : ℝ) (he : eta ∈ Icc (0 : ℝ) eta1)
    (hs : sEta eta sigma ∈ Icc (1 / 20 : ℝ) (19 / 20)) (hsi : sigma ∈ Ioo (0 : ℝ) 1) :
    sEta eta sigma * exprel eta ≤ sigma ∧ sigma ≤ sEta eta sigma ∧
    sigma ∈ Icc (9 / 200 : ℝ) (19 / 20) :=
  GKSharp.sigma_core_cover_proved eta sigma he hs hsi

/-- Lemma 5.13 (label J), sec5f_strip.tex l.29-30: "Let δ^♯ = −δ/(1−δ) (so 1 − δ^♯ = 1/λ), s^♯ = s(1−δ)/(1 − sδ) and
Θ(δ) = (1−δ)^{q−1}C(δ)^p. Then C(δ)C(δ^♯) = 1 and g(δ, s) = Θ(δ) g(δ^♯, s^♯)" (proof l.34-38). (For δ^♯ < 0,
C(δ^♯) is the continued root `cDelta`.) -/
theorem involution (p delta s : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hd : delta < 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    cDelta p delta * cDelta p (-delta / (1 - delta)) = 1 ∧
    g p delta s =
      (1 - delta) ^ (q p - 1) * cDelta p delta ^ p *
        g p (-delta / (1 - delta)) (s * (1 - delta) / (1 - s * delta)) :=
  GKSharp.involution_proved p delta s hp hp2 hd hs

/-- Lemma 5.13 (label J), sec5f_strip.tex l.30-31: "the function Ξ(η, σ) := g/V, V := e^{(1−q)η/2}C^{p/2}, is even in η
for each σ ∈ (0,1)" (proof l.39-40). -/
theorem etilde_even (p sigma : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hs : sigma ∈ Ioo (0 : ℝ) 1) : Function.Even (fun eta => etilde p eta sigma) :=
  GKSharp.etilde_even_proved p sigma hp hp2 hs

/-- sec5f_strip.tex l.51: "By Lemma 5.13, ∂_ηΞ(0, σ) = ∂_η³Ξ(0, σ) = 0". -/
theorem etilde_odd_derivatives (p sigma : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hs : sigma ∈ Ioo (0 : ℝ) 1) :
    deriv (fun eta => etilde p eta sigma) 0 = 0 ∧
    deriv (deriv (deriv (fun eta => etilde p eta sigma))) 0 = 0 :=
  GKSharp.etilde_odd_derivatives_proved p sigma hp hp2 hs

end StripRows

section SectionFiveC
/-- sec5_sharp_inequality.tex:100–101; normalized critical-curve Lambda dictionary. -/
theorem sec5_Lambda {p C K lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    mobPhi p C K lam (mobW lam (curveZ p lam θ)) / (1 - lam) ^ p =
        C ^ p - ‖mobW lam (curveZ p lam θ)‖ ^ p -
          K * reQPow (curveZ p lam θ) (p / 2) / ‖1 + curveZ p lam θ‖ ^ p ∧
    mobPhi p C K lam (mobW lam (curveZ p lam θ)) / (1 - lam) ^ p =
        critD p C K lam (curveZ p lam θ) / ‖1 + curveZ p lam θ‖ ^ p :=
  GKSharp.Proofs.Sec5Lambda.sec5_Lambda_proved hp1 hp2 hl hl1 hθ0 hθ

/-- sec5d_monotone.tex:131–135; actual real-segment derivative, factorization and logarithmic derivative. -/
theorem reduction_real_segment {p C K lam ρ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 ≤ lam) (hl1 : lam < 1) (hρ0 : 0 < ρ) (hQ : 0 < (ρ - lam) * (1 - ρ)) :
    HasDerivAt (fun x : ℝ => mobPhi p C K lam (x : ℂ))
      (-(1 - lam) ^ p * p * ρ ^ (p - 1) - K * (p / 2) * ((ρ - lam) * (1 - ρ)) ^ (p / 2 - 1) * (1 + lam - 2 * ρ)) ρ ∧
    (2 * ρ - 1 - lam ≠ 0 →
      -(1 - lam) ^ p * p * ρ ^ (p - 1) - K * (p / 2) * ((ρ - lam) * (1 - ρ)) ^ (p / 2 - 1) * (1 + lam - 2 * ρ) =
        p / 2 * ((ρ - lam) * (1 - ρ)) ^ (p / 2 - 1) * (2 * ρ - 1 - lam) *
          (K - 2 * (1 - lam) ^ p * ρ ^ (p - 1) * ((ρ - lam) * (1 - ρ)) ^ (1 - p / 2) / (2 * ρ - 1 - lam))) ∧
    ((1 + lam) / 2 < ρ → ρ < 1 →
      HasDerivAt (fun x => Real.log (2 * (1 - lam) ^ p * x ^ (p - 1) * ((x - lam) * (1 - x)) ^ (1 - p / 2) /
          (2 * x - 1 - lam)))
        ((p - 1) / ρ - 2 / (2 * ρ - 1 - lam) - (1 - p / 2) * (2 * ρ - 1 - lam) / ((ρ - lam) * (1 - ρ))) ρ ∧
      (p - 1) / ρ - 2 / (2 * ρ - 1 - lam) - (1 - p / 2) * (2 * ρ - 1 - lam) / ((ρ - lam) * (1 - ρ)) < 0) :=
  GKSharp.Proofs.RealSegment.reduction_real_segment_proved hp1 hp2 hl hl1 hρ0 hQ

/-- sec5_sharp_inequality.tex:28–32, equation (5.2); attained full-circle extrema for positive radius. -/
theorem eq_5_2 {p C K lam ρ : ℝ} (hp : 0 < p) (hK : 0 ≤ K) (hl1 : lam < 1) (hρ : 0 < ρ) :
    ∃ M : ℝ,
      IsGreatest ((fun φ : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))) (p / 2)) ''
        Set.Icc 0 Real.pi) M ∧
      IsLeast ((mobPhi p C K lam) '' Metric.sphere (0 : ℂ) ρ)
        ((1 - lam) ^ p * (C ^ p - ρ ^ p) - K * M) :=
  GKSharp.Proofs.CircleExtrema.eq_5_2_proved hp hK hl1 hρ

end SectionFiveC

/-- sec5d_monotone.tex l.44, 62: "ω = (1−q)θ. Then ω ∈ (0, π/(m+1)), where m := q/(1−q) = p/(2−p) > 1"; "With θ = (m+1)ω,
εθ = (m−1)ω, (1−ε)θ = 2ω" (ε = p − 1). -/
theorem sec5d_coordinate_dictionary (p θ : ℝ) (hp : 1 < p ∧ p < 2)
    (hθ : 0 < θ ∧ θ < Real.pi) :
    1 < p / (2 - p) ∧
    0 < (1 - p / 2) * θ ∧
    (1 - p / 2) * θ < Real.pi / (p / (2 - p) + 1) ∧
    (p / (2 - p) + 1) * ((1 - p / 2) * θ) = θ ∧
    (p / (2 - p) - 1) * ((1 - p / 2) * θ) = (p - 1) * θ ∧
      (p - 1) = (p / (2 - p) - 1) / (p / (2 - p) + 1) := sec5d_coordinate_dictionary_proved p θ hp hθ

/-- sec5d_monotone.tex l.16-17: "the radius r = R(θ) ∈ (0,1) is written as r = sin(γ − b)/sin(γ + b) with
γ ∈ (b, π/2)"; the denominators of (5.9), l.19, are positive (0 < b < a < π/2). -/
theorem sec5d_gamma_denominators (a b γ : ℝ)
    (hab : 0 < b ∧ b < a ∧ a < Real.pi / 2)
    (hγ : b < γ ∧ γ < Real.pi / 2) :
    0 < Real.sin (γ + b) ∧ 0 < Real.sin (γ + a) ∧ 0 < Real.sin (γ - b) ∧
    0 < Real.sin (γ - b) / Real.sin (γ + b) ∧
    Real.sin (γ - b) / Real.sin (γ + b) < 1 := sec5d_gamma_denominators_proved a b γ hab hγ

/-- (5.9), sec5d_monotone.tex l.16-19: "the radius r = R(θ) ∈ (0,1) is written as r = sin(γ − b)/sin(γ + b)";
"so D = 0 becomes μ = −λ = sin(γ − a) sin(γ + b)/(sin(γ + a) sin(γ − b))" (the identities of l.18 are their own rows). -/
theorem sec5d_eq_5_10 (p lam θ γ : ℝ) (hp : 1 < p ∧ p < 2)
    (hlam : -1 < lam ∧ lam < 1) (hθ : 0 < θ ∧ θ < Real.pi)
    (hγ : (p - 1) * (θ / 2) < γ ∧ γ < Real.pi / 2) :
    curveD p lam θ
      (Real.sin (γ - (p - 1) * (θ / 2)) / Real.sin (γ + (p - 1) * (θ / 2))) = 0 ↔
    -lam = (Real.sin (γ - θ / 2) * Real.sin (γ + (p - 1) * (θ / 2))) /
      (Real.sin (γ + θ / 2) * Real.sin (γ - (p - 1) * (θ / 2))) := sec5d_eq_5_10_proved p lam θ γ hp hlam hθ hγ

/-- sec5d_monotone.tex l.54-55: "d_ω = cos ω > 0"; "Using d_ω² − c_q² = sin θ sin(εθ), sin u₃ c_q/d_ω = sin u₁ − sin u₂"
(c_q = cos(qθ); the two identities used by (5.10)). -/
theorem sec5d_trig_dictionary (p θ : ℝ) (hp : 1 < p ∧ p < 2)
    (hθ : 0 < θ ∧ θ < Real.pi) :
    0 < Real.cos ((1 - p / 2) * θ) ∧
    Real.cos ((1 - p / 2) * θ) ^ 2 - Real.cos (p / 2 * θ) ^ 2 =
      Real.sin θ * Real.sin ((p - 1) * θ) ∧
    Real.sin ((1 - (p - 1)) * θ) * Real.cos (p / 2 * θ) /
      Real.cos ((1 - p / 2) * θ) = Real.sin θ - Real.sin ((p - 1) * θ) := sec5d_trig_dictionary_proved p θ hp hθ

/-- sec5d_monotone.tex:54-56, (5.10).
The identity is valid for every real X, hence also X=cos(2 gamma). -/
theorem sec5d_eq_5_11 (p θ X : ℝ) (hp : 1 < p ∧ p < 2)
    (hθ : 0 < θ ∧ θ < Real.pi) :
    monoPi (p - 1) θ X =
      monoW (p - 1) θ / Real.cos ((1 - p / 2) * θ) ^ 2 *
        (Real.cos (p / 2 * θ) ^ 2 + Real.cos ((1 - p / 2) * θ) ^ 2 -
          2 * Real.cos (p / 2 * θ) * Real.cos ((1 - p / 2) * θ) * X) -
      (1 - (p - 1)) ^ 2 * Real.sin θ * Real.sin ((p - 1) * θ) *
        (X - Real.cos (p / 2 * θ) / Real.cos ((1 - p / 2) * θ)) ^ 2 := sec5d_eq_5_11_proved p θ X hp hθ

/-- sec5d_monotone.tex l.62-63: "sin((m+1)ω) sin((m−1)ω) = sin²(mω) − sin²ω" (the row's variable `α` is ω). -/
theorem sec5d_sine_product (m α : ℝ) :
    Real.sin ((m + 1) * α) * Real.sin ((m - 1) * α) =
      Real.sin (m * α) ^ 2 - Real.sin α ^ 2 := sec5d_sine_product_proved m α

/-- sec5d_monotone.tex l.62-63: "one finds W/(4ε sin⁴ω) = 1 − Ψ_m(ω)/(m² − 1)" (the row's variable `α` is ω). -/
theorem sec5d_W_Psi_identity (m α : ℝ) (hm : 1 < m)
    (hα : 0 < α ∧ α < Real.pi / (m + 1)) :
    monoW ((m - 1) / (m + 1)) ((m + 1) * α) /
      (4 * ((m - 1) / (m + 1)) * Real.sin α ^ 4) =
        1 - monoPsi m α / (m ^ 2 - 1) := sec5d_W_Psi_identity_proved m α hm hα

/-- sec5d_monotone.tex l.71-72 (proof of Lemma 5.9 (label Bneg)): "we have 0 < sin(mω) < m sin ω". The hypotheses are slightly
more general than the paper's ω interval (the row's variable `α` is ω). -/
theorem sec5d_sine_comparison (m α : ℝ) (hm : 1 < m) (hα : 0 < α)
    (hmα : m * α < Real.pi) :
    0 < Real.sin (m * α) ∧ Real.sin (m * α) < m * Real.sin α := sec5d_sine_comparison_proved m α hm hα hmα

/-- sec5d_monotone.tex l.71-72 (proof of Lemma 5.9 (label Bneg)): "while Ψ_m(ω) > 0", on the printed domain ω ∈ (0, π/(m+1)) (l.44; the row's variable `α` is ω).
This does not assert strict monotonicity of K_f. -/
theorem sec5d_Psi_pos (m α : ℝ) (hm : 1 < m)
    (hα : 0 < α ∧ α < Real.pi / (m + 1)) : 0 < monoPsi m α := sec5d_Psi_pos_expr_proved m α hm hα

/-- sec5d_monotone.tex l.71: "since sin x / x decreases on (0, π)". -/
theorem sec5d_sinc_strictAntiOn :
    StrictAntiOn (fun x : ℝ => Real.sin x / x) (Set.Ioo 0 Real.pi) :=
  sec5d_sinc_strictAntiOn_proved


section SectionFour
open Set GKSharp.Threshold
/-- P019_paper.tex:139; continuity of the real part of the fractional power, including zero. -/
theorem reQPow_continuous (qq : ℝ) (hqq : 0 < qq) : Continuous (fun z : ℂ => reQPow z qq) :=
  GKSharp.reQPow_continuous_proved qq hqq

/-- sec4a_criterion.tex:61–62; inversion identity. -/
theorem reQPow_inv (p : ℝ) (z : ℂ) (hz : z ≠ 0) :
    reQPow z⁻¹ (q p) = ‖z‖ ^ (-p) * reQPow z (q p) :=
  GKSharp.reQPow_inv_proved p z hz

/-- sec4a_criterion.tex:85; exact GK quadratic identities. -/
theorem quadratic_identities (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) :
    sn p * (gk p lam ^ 2 - 1) = (1 - lam) * (gk p lam - sn p) ∧
    gk p lam ^ 2 - lam = (1 - lam) * gk p lam / sn p :=
  GKSharp.quadratic_identities_proved p lam hp hp2 hlam

/-- sec4b_failure.tex:87–88 (proof of Corollary 4.5 (label L0), "which is Jordan's inequality"); strict Jordan consequence. -/
theorem strict_jordan_pp (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    p * dual p / 4 * sn p ^ 2 < 1 :=
  GKSharp.strict_jordan_pp_proved p hp hp2

/-- sec4a_criterion.tex:83–84; sec4b_failure.tex:122–124 (4.6); actual infimum bounded by axis witness. -/
theorem h_le_axisUpper (p lam theta : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (0 : ℝ) 1) (htheta : theta ∈ Ioo (0 : ℝ) 1) :
    Threshold.h p lam ≤ axisUpper p lam theta :=
  GKSharp.h_le_axisUpper_proved p lam theta hp hp2 hlam htheta

/-- sec4b_failure.tex:134–135; axis rescaling: "With ρ = 1 − sδ (s ∈ (0,1) fixed), (4.6) gives h ≤ δ g(δ, p, s)". -/
theorem h_le_delta_g (p delta s : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hd : delta ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    Threshold.h p (1 - delta) ≤ delta * g p delta s :=
  GKSharp.h_le_delta_g_proved cDelta_eq_gk p delta s hp hp2 hd hs

/-- P019_paper.tex:85, sec4a_criterion.tex:90–91: "Let s_* be the unique root in (0,1) of (2q−1)s² + (1 − q + 2qA)s − qA = 0"; unique interior quadratic root and unique global minimum. -/
theorem sStar_spec (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    sStar p ∈ Ioo (0 : ℝ) 1 ∧ sQuad p (sStar p) = 0 ∧
    (∀ s ∈ Ioo (0 : ℝ) 1, sQuad p s = 0 → s = sStar p) ∧
    (∀ s ∈ Ioo (0 : ℝ) 1, omegaFirst p (sStar p) ≤ omegaFirst p s) ∧
    (∀ s ∈ Ioo (0 : ℝ) 1, omegaFirst p s = omegaFirst p (sStar p) → s = sStar p) :=
  GKSharp.sStar_spec_proved p hp hp2

/-- sec4a_criterion.tex:93; compare the minimum with its midpoint value. -/
theorem omega_midpoint_bound (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    omegaFirst p (sStar p) ≤ p * 2 ^ (p - 1) / sn p :=
  GKSharp.omega_midpoint_bound_proved p hp hp2

/-- sec4b_failure.tex:51–55 (proof of Theorem 4.4, "the contact identities give"); all three rational identities at the actual chosen contact. -/
theorem contact_rational_identities (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let r := rContact p lam
    cs p = (1 + lam) * r / (r ^ 2 + lam) ∧
    sn p ^ 2 = (r ^ 2 - 1) * (r ^ 2 - lam ^ 2) / (r ^ 2 + lam) ^ 2 ∧
    dOne p lam = (r ^ 2 - lam) * (r ^ 2 - lam ^ 2) / (r ^ 2 * (r ^ 2 + lam)) :=
  GKSharp.contact_rational_identities_proved p lam hp hp2 hlam

/-- sec4b_failure.tex:30,40 ("r > 1 the larger root"; "v = r − λ/r > 0"); scalar contact root inequalities and quadratic identity only. -/
theorem contact_root_scalar_properties {p lam : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    1 < rContact p lam ∧ |lam| < rContact p lam ∧ 0 < vContact p lam ∧
      rContact p lam + lam / rContact p lam = sigmaContact p lam :=
  GKSharp.contact_root_properties hp hp2 hlam

/-- sec4b_failure.tex:68 ("Put B₀ = δ(1+λ)²/(c₀³s₀²v³) > 0", `δ = 1 − λ`); positive scalar prefactor. -/
theorem contact_bZero_positive {p lam : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) : 0 < bZero p lam :=
  GKSharp.contact_bZero_pos hp hp2 hlam

/-- sec4b_failure.tex:70–77 ("Thus μ_*″(θ₀) < 0 if and only if (pp′/4)s₀² + 4λc₀⁴/(1+λ)² > 1"); scalar sign equivalence; Schur/envelope identification is separate. -/
theorem contact_scalar_sign_test {p lam : ℝ} (hp : 1 < p)
    (hlam : -1 < lam) : signBracket p lam < 0 ↔ 1 < localTest p lam :=
  GKSharp.contact_signBracket_negative_iff hp hlam

end SectionFour

section MoreSectionFour
open Set Filter GKSharp.Threshold GKSharp.ComputerChecked
open scoped Topology

/-- sec4b_failure.tex:20,95 ("When T(p) > 0, condition (4.2) is equivalent to λ > λ_loc(p)"; Lemma 4.6(b): "For 0<λ<1 the
left side of (4.2) is less than 1, equal to 1 or greater than 1 according as λ<λ_loc(p), λ=λ_loc(p) or λ>λ_loc(p)");
the exact local threshold comparison. -/
theorem local_threshold_iff (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (0 : ℝ) 1) :
    (1 < localTest p lam ↔ lambdaLoc p < lam) :=
  GKSharp.local_threshold_iff_proved p lam hp hp2 hlam

/-- sec4b_failure.tex:93,98–99 ("Some λ ∈ (0, 1) satisfies (4.2) if and only if F(p) ... > 0"); existence of a local witness iff F is positive. -/
theorem local_witness_iff (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    (∃ lam ∈ Ioo (0 : ℝ) 1, 1 < localTest p lam) ↔ 0 < localF p :=
  GKSharp.local_witness_iff_proved p hp hp2

/-- sec4b_failure.tex:99 ("For the zero set, write F = (p − 2)²/(p−1) − 4 sin²(π(p − 2)/(2p))"); stable expression for F. -/
theorem localF_stable (p : ℝ) (hp : 1 < p) :
    localF p = (p - 2) ^ 2 / (p - 1) -
      4 * Real.sin (Real.pi * (p - 2) / (2 * p)) ^ 2 :=
  GKSharp.localF_stable_proved p hp

/-- sec4b_failure.tex:100 ("On (1, 1 + 10^{−6}], F ≥ 1/(p−1) − 8 > 0"); lower bound and positivity near1. -/
theorem localF_endpoint_one (p : ℝ) (hp : 1 < p) (hhi : p ≤ 1000001 / 1000000) :
    1 / (p - 1) - 8 ≤ localF p ∧ 0 < localF p :=
  GKSharp.localF_endpoint_one_proved p hp hhi

/-- sec4b_failure.tex:100–101 ("On [3/2, 2) ... F/η² ≤ ... < −0.24"); explicit upper bound and negativity near2. -/
theorem localF_endpoint_two (p : ℝ) (hp : 3 / 2 ≤ p) (hp2 : p < 2) :
    localF p / (2 - p) ^ 2 ≤
      2 - (Real.pi ^ 2 / 4) * (1 - Real.pi ^ 2 / 216) ^ 2 ∧ localF p < 0 :=
  GKSharp.localF_endpoint_two_proved p hp hp2

/-- sec4a_criterion.tex:90–91; divergence at both endpoints. -/
theorem omegaFirst_endpoints (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    Tendsto (omegaFirst p) (nhdsWithin 0 (Ioi 0)) atTop ∧
    Tendsto (omegaFirst p) (nhdsWithin 1 (Iio 1)) atTop :=
  GKSharp.omegaFirst_endpoints_proved p hp hp2

/-- sec4b_failure.tex:118 ("Consequently h(·,p) has a smallest zero in (0,λ_loc(p))"); first interior zero from explicit continuity and endpoint signs. -/
theorem first_axis_zero_of (p : ℝ) (hpos : 0 < Threshold.h p 0) (hloc : 0 < lambdaLoc p)
    (hcont : ContinuousOn (Threshold.h p) (Icc 0 (lambdaLoc p))) (hedge : Threshold.h p (lambdaLoc p) < 0) :
    IsLeast (axisZeros p) (lambda0 p) ∧ 0 < lambda0 p ∧ lambda0 p < lambdaLoc p :=
  GKSharp.first_axis_zero_of_proved p hpos hloc hcont hedge

/-- Lemma 4.6 (label Pc), sec4b_failure.tex l.93-94: "p_c ∈ [1.213490304, 1.213490305] is the only zero of F in (1, 2)"; proof
l.102-103: "on [1.2134, 1.2136], F′ < 0 and F changes sign within the stated bracket"; calculation_certificates.tex
l.26-27 (root enclosure). -/
theorem pc_spec (hc : CheckLocalF) :
    IsLeast localZeros pc ∧ pc ∈ Ioo (1213490304 / 1000000000 : ℝ) (1213490305 / 1000000000) ∧
    (∀ p ∈ Ioo (1 : ℝ) 2, localF p = 0 ↔ p = pc) ∧
    (∀ p ∈ Ioo (1 : ℝ) 2, 0 < localF p ↔ p < pc) ∧
    deriv localF pc < 0 :=
  GKSharp.pc_spec_proved hc

/-- P019_paper.tex l.87-88: "Put T(p) = s₀²(pp′/4 − 1 − c₀²)/c₀⁴ and λ_loc(p) = { (1 − √T(p))/(1 + √T(p)), T(p) > 0;
1, T(p) ≤ 0 }" (s₀ = sin(π/p), c₀ = −cos(π/p)); Lemma 4.6 (label Pc), sec4b_failure.tex l.93: "Some λ ∈ (0, 1)
satisfies (4.2) if and only if F(p) ... > 0, that is, if and only if p < p_c"; sec5f_strip.tex l.16: "for p ≥ p_c
(where λ_loc = 1)". (`localD2` is d² = T(p), d = √T(p) as in sec4b_failure.tex l.128.) -/
theorem lambdaLoc_spec (hc : CheckLocalF) :
    (∀ p ∈ Ioo (1 : ℝ) pc, localD2 p ∈ Ioo (0 : ℝ) 1 ∧ lambdaLoc p ∈ Ioo (0 : ℝ) 1) ∧
    (∀ p ∈ Ico pc (2 : ℝ), lambdaLoc p = 1) :=
  GKSharp.lambdaLoc_spec_proved hc

/-- sec4b_failure.tex l.141: "so for 1.2134 ≤ p < p_c we have ... 1 − λ_loc(p) = 2d/(1+d) ≤ 2d ≤ 0.03";
calculation_certificates.tex l.38: "For 1.2134≤p<p_c the rows for g_f and T combine as in case (c) of the proof of
Proposition 4.7: 0<δ_loc(p)=1−λ_loc(p)≤0.03". -/
theorem deltaLoc_gap (hc : CheckLocalF) (p : ℝ)
    (hp : p ∈ Ico (6067 / 5000 : ℝ) pc) :
    0 < 1 - lambdaLoc p ∧ 1 - lambdaLoc p ≤ 3 / 100 :=
  GKSharp.deltaLoc_gap_proved hc GKSharp.checkLocalGap_proved p hp

/-- Proposition 4.7 (label edge), "Strict inequality at the local threshold" (sec4b_failure.tex l.118: "For every
1 < p < p_c, h(λ_loc(p), p) < 0"), case (c), l.134-140: "Let p ∈ [1.2134, p_c). As p ↑ p_c, we have λ_loc(p) → 1 and
h → 0, so we rescale"; "Interval arithmetic gives g < 0 for (p, δ) ∈ [1.2134, 1.2134904] × [0, 0.03]";
calculation_certificates.tex l.38-39: "h(λ_loc(p),p) ≤ δ_loc(p) g_f(p,δ_loc(p)) < 0". -/
theorem boundary_sliver (hc : CheckLocalF) (hs : CheckBoundarySliver)
    (p : ℝ) (hp : p ∈ Ico (6067 / 5000 : ℝ) pc) :
    Threshold.h p (lambdaLoc p) < 0 :=
  GKSharp.boundary_sliver_proved cDelta_eq_gk hc hs GKSharp.checkLocalGap_proved p hp

/-- Proposition 4.7 (label edge), "Strict inequality at the local threshold", case (a), sec4b_failure.tex l.127-129:
"For p ∈ [1 + 10^{−6}, 1.2134] we use interval arithmetic on cells in p, with a value of ϑ chosen in each cell ...
Every cell gives an upper bound <0"; calculation_certificates.tex l.28 (row "h(λ_loc(p),p) (Prop. 4.7)": "hence
h(λ_loc(p),p)<0"). -/
theorem boundary_bulk (hb : CheckBoundaryBulk) (p : ℝ)
    (hp : p ∈ Icc (1000001 / 1000000 : ℝ) (6067 / 5000)) :
    Threshold.h p (lambdaLoc p) < 0 :=
  GKSharp.boundary_bulk_proved hb p hp

/-- sec5f_strip.tex l.56: "Also Ξ(0, σ) = g(0, σ) ≥ Ω(p) ≥ 0" (the row: the first two relations, for 1 < p < 2). -/
theorem etilde_zero_minimum (p sigma : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hs : sigma ∈ Ioo (0 : ℝ) 1) :
    etilde p 0 sigma = g p 0 sigma ∧ omega p ≤ etilde p 0 sigma :=
  GKSharp.etilde_zero_minimum_proved p sigma hp hp2 hs

end MoreSectionFour

section ContactAndStrip
open Set Filter GKSharp.Threshold GKSharp.ComputerChecked
open scoped Topology

/-- sec4b_failure.tex:28 ("With ℓ = log w as a holomorphic function of u = y + it"); genuine local analytic logarithm and its derivative. -/
theorem contact_local_log (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    ∃ ell : ℂ → ℂ, ∃ U ∈ 𝓝 ((yContact p lam : ℂ) + Complex.I * (theta p : ℂ)),
      AnalyticOnNhd ℂ ell U ∧
      ∀ u ∈ U, Complex.exp (ell u) = mobContact lam (Complex.exp u) ∧
        deriv ell u = (1 - (lam : ℂ)) * Complex.exp u /
          ((Complex.exp u + (lam : ℂ)) * (Complex.exp u + 1)) :=
  GKSharp.contact_local_log_proved p lam hp hp2 hlam

/-- sec4b_failure.tex:23 ("Since λ is real, Γ_C(y, −t) = Γ_C(y, t)"); real-ratio Gamma is even in the angle. -/
theorem gamma_even (p C lam y t : ℝ) :
    Threshold.gamma p C lam y (-t) = Threshold.gamma p C lam y t :=
  GKSharp.threshold_gamma_even_proved p C lam y t

/-- sec4b_failure.tex:23 ("Since λ is real, Γ_C(y, −t) = Γ_C(y, t), so m_C is even"); evenness of the actual infimum. -/
theorem obstacle_even (p lam : ℝ) :
    Function.Even (Threshold.obstacle p lam) :=
  GKSharp.threshold_obstacle_even_proved p lam

/-- sec2_obstacle.tex:60–61; exact exponential-coordinate bridge. -/
theorem gamma_coordinate_bridge (p C lam y t : ℝ) (hp : 1 < p) :
    Threshold.gamma p C lam y t = Real.exp (-Threshold.q p * y) *
      Threshold.bigG p C lam (Threshold.zeta y t) :=
  GKSharp.threshold_gamma_coordinate_bridge_proved p C lam y t hp

/-- sec4b_failure.tex:141 ("Interval arithmetic also gives T(p) ≤ 0.015² on [1.2134,1.2134904]"); calculation_certificates.tex:30,38. Here the checked bound 2d ≤ 0.03 on [1.2134, 1.2134904]. -/
theorem sec4_local_gap_kernel (p : ℝ) (hp : p ∈ Icc (6067 / 5000 : ℝ) (12134904 / 10000000)) :
    2 * Real.sqrt (max (localD2 p) 0) ≤ 3 / 100 :=
  GKSharp.checkLocalGap_proved p hp

/-- sec5f_strip.tex l.25: "All of these are real-analytic near δ = 0. Lemma 5.13 also uses these functions for δ < 0,
through their analytic continuations; there C(δ) is still the root near 1, not GK_p(1 − δ)" (here
g(·, s), 0 < s < 1; `C(δ)` is `cDelta`, the root near 1 for both signs of δ). -/
theorem g_analytic_zero (p s : ℝ) (hp : 1 < p) (hp2 : p < 2) (hs : s ∈ Ioo (0 : ℝ) 1) :
    AnalyticAt ℝ (fun delta => g p delta s) 0 :=
  GKSharp.g_analytic_zero_proved p s hp hp2 hs

/-- sec5f_strip.tex l.51-54: "for 0 < η ≤ η₁ := −log 0.95, Ξ(η, σ) = Ξ(0, σ) + e₂(σ)η² + c₄(ξ, σ)η⁴, ξ ∈ (0, η)";
"Here e₂(σ) = ½∂²_ηΞ(0,σ) and c₄ = (1/24)∂⁴_ηΞ". -/
theorem etilde_taylor (p sigma eta : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hs : sigma ∈ Ioo (0 : ℝ) 1) (heta : eta ∈ Ioc (0 : ℝ) eta1) :
    ∃ xi ∈ Ioo (0 : ℝ) eta,
      etilde p eta sigma = etilde p 0 sigma + eTwo p sigma * eta ^ 2 + cFour p xi sigma * eta ^ 4 :=
  GKSharp.etilde_taylor_proved p sigma eta hp hp2 hs heta

/-- Proposition 5.14 (label strip), proof, sec5f_strip.tex l.51-66: "Case 1: p ∈ [p₀, 1.2341027], 0 < δ ≤ 0.05";
calculation_certificates.tex l.31 (row "g, Case 1": "e₂>τ₄ or Ξ(0,σ)>η₁²(max(0,−e₂)+τ₄) on every cell; end bounds
>0.2920 and >6.320") and l.41: "The Case 1 rectangles begin at p₀⁻<p₀, but their conclusion is used only for p≥p₀,
where Ω(p)≥0 by Proposition 5.14". -/
theorem corner_positive (hc : CheckCornerDerivatives) (ht : CheckCornerTails)
    (p delta s : ℝ) (hp : p ∈ Icc a0 b1) (ho : 0 ≤ omega p)
    (hd : delta ∈ Ioc (0 : ℝ) (1 / 20)) (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < g p delta s :=
  GKSharp.corner_positive_proved hc ht p delta s hp ho hd hs

end ContactAndStrip

section ColeRows
/-- sec2_obstacle.tex:97; HKV2003 Theorem2.1,p242, existence direction, REFEREED. Bare cited restatement. -/
theorem slice_O25 (F : ℂ → EReal) (hF : UpperSemicontinuous F) (htop : ∀ z, F z ≠ ⊤)
    (E : Set ℂ) (hE : E.Nonempty)
    (hdisc : ∀ g : Polynomial ℂ, g.eval 0 ∈ E → ∀ n : ℕ,
      0 ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), potentialTrunc n (F (g.eval (unitPoint t)))) :
    ∃ G : ℂ → EReal, IsSubharmonic G ∧ (∀ z, G z ≤ F z) ∧ ∀ z ∈ E, 0 ≤ G z :=
  Cited.hkv_thm21 F hF htop E hE hdisc

/-- sec2_obstacle.tex:97–99; largest homogeneous minorant, internal envelope/dilation proof from the exact cited existence input. -/
theorem slice_O26 (q : ℝ) (M : ℂ → ℝ) (hM : Continuous M)
    (hhom : ∀ t : ℝ, 0 < t → ∀ z : ℂ, M ((t : ℂ) * z) = t ^ q * M z)
    (hdisc : PolynomialDiscBound M) :
    ∃ V : ℂ → EReal, IsSubharmonic V ∧ (∀ z, V z ≤ (M z : EReal)) ∧ 0 ≤ V 0 ∧
      (∀ (t : ℝ) (z : ℂ), 0 < t → V ((t : ℂ) * z) = ((t ^ q : ℝ) : EReal) * V z) ∧
      (∀ u : ℂ → EReal, IsSubharmonic u → (∀ z, u z ≤ (M z : EReal)) → ∀ z, u z ≤ V z) :=
  GKSharp.slice_O26_proved q M hM hhom hdisc

end ColeRows

section ExtraElementary
open Set

/-- sec4b_failure.tex:35 ("The odd terms cancel, so m_C(θ₀ − s) + m_C(θ₀ + s) ≤ μ_*″(θ₀)s² + O(s⁴)"); symmetric fourth-order remainder from genuine local C4 regularity. -/
theorem symmetric_taylor_four (mu : ℝ → ℝ) (tt : ℝ)
    (hmu : ContDiffAt ℝ 4 mu tt) (hz : mu tt = 0) :
    ∃ bound > 0, ∃ eps > 0, ∀ s ∈ Ioo (-eps) eps,
      |mu (tt - s) + mu (tt + s) - deriv (deriv mu) tt * s ^ 2| ≤ bound * s ^ 4 :=
  GKSharp.symmetric_taylor_four_proved mu tt hmu hz

/-- sec2_obstacle.tex:95–98; dilation of the actual homogeneous obstacle for positive spatial scale. -/
theorem sec2_homogeneous_obstacle_scaling (p C : ℝ) (rho : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    homogeneousObstacle p C rho ((r : ℂ) * z) = r ^ (p / 2) * homogeneousObstacle p C rho z :=
  PotentialCoordinates.homogeneousObstacle_homogeneous p C rho r hr z

/-- sec2_obstacle.tex:95; the actual positive-degree homogeneous obstacle vanishes at0. -/
theorem sec2_homogeneous_obstacle_zero {p : ℝ} (hp : 0 < p) (C : ℝ) (rho : ℂ) :
    homogeneousObstacle p C rho 0 = 0 :=
  PotentialCoordinates.homogeneousObstacle_zero hp C rho

end ExtraElementary

section ActualObstacleMinimum
open Set
/-- sec2_obstacle.tex:58–59; actual asymmetric complex-ratio Gamma is coercive uniformly in angle. The separate leading-asymptotic equalities remain separate claims. -/
theorem sec2_uniform_coercivity {p C : ℝ} (hp : 0 < p) (rho : ℂ) (hC : max 1 ‖rho‖ < C) :
    UniformCoercive p C rho :=
  Coercive.gamma_uniform_coercive hp rho hC

/-- sec2_obstacle.tex:59–60; one compact radial interval, attained actual infimum, explicit boundedness below and angular continuity. -/
theorem slice_O12 {p : ℝ} (hp : 1 < p) (C : ℝ) (rho : ℂ) (hC : max 1 ‖rho‖ < C) :
    (∃ Y : ℝ, 0 < Y ∧ ∀ t : ℝ, ∃ y ∈ Icc (-Y) Y,
      (∀ v : ℝ, gamma p C rho y t ≤ gamma p C rho v t) ∧ obstacle p C rho t = gamma p C rho y t) ∧
    (∀ t : ℝ, BddBelow (range (fun y : ℝ => gamma p C rho y t))) ∧ Continuous (obstacle p C rho) :=
  GKSharp.slice_O12_proved hp C rho hC

/-- sec2_obstacle.tex:95; the actual homogeneous obstacle is continuous on the whole complex plane. -/
theorem sec2_homogeneous_obstacle_continuous {p C : ℝ} (hp : 0 < p) (rho : ℂ) (hC : max 1 ‖rho‖ < C) :
    Continuous (homogeneousObstacle p C rho) :=
  GKSharp.homogeneousObstacle_continuous hp rho hC

end ActualObstacleMinimum

section MoreThresholdAndStrip
open Set Filter GKSharp.Threshold GKSharp.ComputerChecked
open scoped Topology

/-- sec4a_criterion.tex:94–95; both explicit endpoint factors: "By Jordan's inequality s₀ ≥ 2(p−1)/p" ... "Together with
c₀ ≥ cos(0.001π)". -/
theorem omega_endpoint_factors (p : ℝ) (hp : 1 < p) (hhi : p ≤ 1001 / 1000) :
    p * 2 ^ (q p - 1) ≤ 7081 / 10000 ∧
    993 / 1000 < sn p ^ (p - 1) * cs p ^ (1 - q p) :=
  GKSharp.omega_endpoint_factors_proved p hp hhi

/-- sec4a_criterion.tex:93–95; analytic endpoint negativity on (1, 1.001]. -/
theorem omega_endpoint (p : ℝ) (hp : 1 < p) (hhi : p ≤ 1001 / 1000) : omega p < 0 :=
  GKSharp.omega_endpoint_proved p hp hhi

/-- Proposition 4.3 (label F), sec4a_criterion.tex l.79-80: "Moreover Ω < 0 on (1, 1.2336025]. With Proposition 5.14 it
follows that the zero p₀ of Ω in (1,1.268] (Section 1) satisfies 1.2336025<p₀<1.2336027, and that Ω<0 on (1,p₀)";
sec5f_strip.tex l.49: "Hence p₀ is the only zero of Ω in
(1, 1.268], and Ω ≥ 0 on [p₀, 1.268]". -/
theorem p0_spec (hn : CheckOmegaNeg) (hr : CheckOmegaRoot) :
    IsLeast omegaZeros p0 ∧ a0 < p0 ∧ p0 < b0 ∧
    (∀ p ∈ Ioc (1 : ℝ) (317 / 250), omega p = 0 ↔ p = p0) ∧
    (∀ p ∈ Ioo (1 : ℝ) p0, omega p < 0) ∧
    (∀ p ∈ Icc p0 (317 / 250), 0 ≤ omega p) :=
  GKSharp.p0_spec_proved hn hr

/-- sec4a_criterion.tex:85–86; all three actual GK/K near-identity limits. -/
theorem near_identity_limits (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    Tendsto (fun delta : ℝ => gk p ((1 - delta : ℝ) : ℂ)) (nhdsWithin 0 (Ioi 0)) (𝓝 1) ∧
    Tendsto (fun delta : ℝ => (gk p ((1 - delta : ℝ) : ℂ) ^ p - 1) / delta)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (p * aConst p)) ∧
    Tendsto (fun delta : ℝ => kConst p (1 - delta) / delta)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (kappaZero p)) :=
  GKSharp.near_identity_limits_proved p hp hp2

/-- sec4a_criterion.tex:87–89; negative Omega supplies an explicit eventual negative axis gap. -/
theorem omega_negative_eventual_h (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (homega : omega p < 0) :
    ∃ eps > 0, ∀ lam : ℝ, 1 - eps < lam → lam < 1 → Threshold.h p lam < 0 :=
  GKSharp.omega_negative_eventual_h_proved p hp hp2 homega

/-- sec4b_failure.tex:99,97 (F of l.99; "F′ < 0" on [1.2134, 1.2136]); exact derivative of the actual F. -/
theorem localF_derivative (p : ℝ) (hp : 1 < p) :
    deriv localF p = (p - 2) * p / (p - 1) ^ 2 -
      8 * Real.sin (Real.pi * (p - 2) / (2 * p)) *
        Real.cos (Real.pi * (p - 2) / (2 * p)) * Real.pi / p ^ 2 :=
  GKSharp.localF_derivative_proved p hp

/-- sec4b_failure.tex:140–141 ("at δ = 0, g = p(A+s)/(s(1−s))^q − 2^q s₀^{p−2} c₀^{1−q}, whose minimum over s is Ω(p)"); genuine quadratic error around the actual minimizing root. -/
theorem fixed_s_quadratic_error (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ∃ bound > 0, ∃ eps > 0, ∀ s ∈ Ioo (sStar p - eps) (sStar p + eps),
      |g p 0 s - omega p| ≤ bound * (s - sStar p) ^ 2 :=
  GKSharp.fixed_s_quadratic_error_proved p hp hp2

/-- sec4a_criterion.tex:63–64; exact two one-sided cosine branch derivatives. -/
theorem cosine_kink_derivatives (qq KK : ℝ) :
    HasDerivAt (fun t : ℝ => KK * Real.cos (qq * t)) (-KK * qq * Real.sin (qq * Real.pi)) Real.pi ∧
    HasDerivAt (fun t : ℝ => KK * Real.cos (qq * (t - 2 * Real.pi)))
      (KK * qq * Real.sin (qq * Real.pi)) Real.pi :=
  GKSharp.cosine_kink_derivatives_proved qq KK

/-- sec5f_strip.tex l.19-20: "Put δ = 1 − λ and ρ = 1 − sδ with s ∈ (0,1)"; "h = δ min_{0<s<1} g(δ, s)"
(the minimum is attained). -/
theorem rescaled_minimum (p delta : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hd : delta ∈ Ioo (0 : ℝ) 1) :
    ∃ s ∈ Ioo (0 : ℝ) 1, h p (1 - delta) = delta * g p delta s ∧
      ∀ u ∈ Ioo (0 : ℝ) 1, g p delta s ≤ g p delta u :=
  GKSharp.rescaled_minimum_proved p delta hp hp2 hd

/-- sec5f_strip.tex l.20: "h = δ min_{0<s<1} g(δ, s)": positivity of g for every s ∈ (0,1) gives h > 0
(Proposition 5.14 (label strip), l.44). -/
theorem h_positive_of_g (p delta : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hd : delta ∈ Ioo (0 : ℝ) 1) (hg : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < g p delta s) :
    0 < h p (1 - delta) :=
  GKSharp.h_positive_of_g_proved p delta hp hp2 hd hg

/-- Proposition 5.14 (label strip), sec5f_strip.tex l.44: "Let p₀ ≤ p ≤ 1.268 and 0 < λ < 1. Then h(λ, p) > 0." -/
theorem strip_h_positive (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hc : CheckCornerDerivatives) (ht : CheckCornerTails)
    (hb : CheckStripBulkMiddle) (hbt : CheckStripBulkTails)
    (p lam : ℝ) (hp : p ∈ Icc p0 (317 / 250)) (hlam : lam ∈ Ioo (0 : ℝ) 1) :
    0 < h p lam :=
  GKSharp.strip_h_positive_proved hn hr hc ht hb hbt p lam hp hlam

/-- sec5f_strip.tex l.74: "For p₀ ≤ p < 3 − √3 we have p > p_c, so λ_loc = 1". -/
theorem pc_lt_p0 (hn : CheckOmegaNeg) (hr : CheckOmegaRoot) (hc : CheckLocalF) : pc < p0 :=
  GKSharp.pc_lt_p0_proved hn hr hc

end MoreThresholdAndStrip

section ContactAndLiftSupport
open Set GKSharp.Threshold

/-- sec4b_failure.tex:27–30 ("C = GK is the maximum of |w| on this ray"; contact radius r); the actual matrix norm and chosen contact radius. -/
theorem contact_gk_radius (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    rContact p lam = cs p * (gk p lam ^ 2 - lam) / (gk p lam ^ 2 - 1) ∧
      gk p lam ^ 2 = (rContact p lam ^ 2 - lam ^ 2) / (rContact p lam ^ 2 - 1) :=
  GKSharp.contact_gk_radius p lam hp hp2 hlam

/-- sec4b_failure.tex:27–28 ("C = GK is the maximum of |w| on this ray (Lemma 4.1)"); squared gap identity supporting the ray maximum. -/
theorem contact_ray_squared_gap (p lam x : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    gk p lam ^ 2 * (x ^ 2 - 2 * cs p * x + 1) -
        (x ^ 2 - 2 * lam * cs p * x + lam ^ 2) =
      (gk p lam ^ 2 - 1) * (x - rContact p lam) ^ 2 :=
  GKSharp.contact_ray_squared_gap p lam x hp hp2 hlam

/-- sec4b_failure.tex:27–28 ("On the ray t = θ₀, G ≥ 0 if and only if |w| ≤ C, and C = GK is the maximum of |w| on this ray"); the equivalence is inside the positive-radius implication. -/
theorem contact_ray_max (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    (∀ r : ℝ, 0 < r →
      ‖mobContact lam ((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)))‖ ≤ gk p lam) ∧
    (∀ r : ℝ, 0 < r →
      (‖mobContact lam ((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)))‖ = gk p lam ↔
        r = rContact p lam)) :=
  GKSharp.contact_ray_max_proved p lam hp hp2 hlam

/-- sec4a_criterion.tex:63–64; actual wrapped cosine, including continuity and periodicity. -/
theorem wrapped_cosine_trigconvex (qq KK : ℝ) (hq : qq ∈ Ioo (0 : ℝ) 1) (hK : 0 ≤ KK) :
    let f := fun t : ℝ => KK * Real.cos (qq * Complex.arg (Complex.exp (Complex.I * (t : ℂ))))
    Continuous f ∧ Function.Periodic f (2 * Real.pi) ∧ QTrigConvex qq f :=
  GKSharp.wrapped_cosine_trigconvex_proved qq KK hq hK

/-- sec4a_criterion.tex:67–68; actual obstacle contact forces the sinusoidal arch. -/
theorem arch_sinusoid (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) (f : ℝ → ℝ)
    (hf : Continuous f) (hq : QTrigConvex (q p) f)
    (hminor : ∀ t : ℝ, f t ≤ Threshold.obstacle p lam t) :
    f (-theta p) = 0 ∧ f (theta p) = 0 ∧
    ∃ aa : ℝ, ∀ t ∈ Icc (-theta p) (theta p), f t = aa * Real.cos (q p * t) :=
  GKSharp.arch_sinusoid_proved p lam hp hp2 hlam f hf hq hminor

/-- sec4b_failure.tex:85 ("For λ ≤ 0 the map r ↦ r + λ/r increases on (0, ∞)"); negative-lambda radial monotonicity. -/
theorem negative_contact_unique (lam : ℝ) (hlam : lam ∈ Ioc (-1 : ℝ) 0) :
    StrictMonoOn (fun r : ℝ => r + lam / r) (Ioi 0) :=
  GKSharp.negative_contact_unique_proved lam hlam

/-- sec4b_failure.tex:57–72 (the expansion of l.57–65 equals the display of l.68–72: "The second identity and c₀² + s₀² = 1 now yield"); scalar collection only, before the analytic Schur identity. -/
theorem contact_expanded_factorization (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let r := rContact p lam
    let v := vContact p lam
    let D := dOne p lam
    2 * p * lam * (1 - lam) / (r * v * D)
      + p * (1 - lam) ^ 2 / (sn p ^ 2 * v ^ 2)
      - (1 - lam) * cs p / (sn p ^ 2 * v)
      - (1 - lam) / (cs p * v) *
          (sigmaContact p lam / v - p * ((1 - lam / r * cs p) / D) + p / 2) ^ 2
      = bZero p lam * signBracket p lam :=
  GKSharp.contact_expanded_factorization p lam hp hp2 hlam

/-- Alternative lift-route support (route R4): a negative disc integral of a continuous M with M(0) = 0 stays
negative on a smaller root-free circle. It supports the lift step of sec2_obstacle.tex l.82-85 ("write g = ζ^k B h
with k ≥ 1, B a finite Blaschke product and h zero-free in the open disc"); it does not assert that printed
Blaschke/square-root step. -/
theorem disc_rescale (M : ℂ → ℝ) (hM : Continuous M) (hM0 : M 0 = 0) (g : Polynomial ℂ)
    (hneg : ∫ t in (0 : ℝ)..(2 * Real.pi), M (g.eval (unitPoint t)) < 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ (∀ t : ℝ, g.eval ((r : ℂ) * unitPoint t) ≠ 0) ∧
      ∫ t in (0 : ℝ)..(2 * Real.pi), M (g.eval ((r : ℂ) * unitPoint t)) < 0 :=
  GKSharp.disc_rescale M hM hM0 g hneg

/-- Alternative lift-route support (route R4): trigonometric near-minimizers for a continuous F whose minimum μ is
attained in a bounded range. It supports sec2_obstacle.tex l.90-94 ("fix ε > 0. For each t choose y_t ∈ [−Y₀, Y₀] with
Γ_C(y_t, t) < m_C(t) + ε"); it does not assert the printed Fejér construction or the full polynomial-disc bound. -/
theorem exists_trig_near_min (F : ℝ → ℝ → ℝ) (hF : Continuous (Function.uncurry F))
    (mu : ℝ → ℝ) (hmu : Continuous mu) (R : ℝ)
    (hmin : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi), ∃ v ∈ Icc (-R) R, F t v = mu t)
    (hle : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi), ∀ v : ℝ, mu t ≤ F t v)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ c : ℤ →₀ ℂ, ∫ t in (0 : ℝ)..(2 * Real.pi), F t (trig c t).re ≤
      (∫ t in (0 : ℝ)..(2 * Real.pi), mu t) + eps :=
  GKSharp.exists_trig_near_min F hF mu hmu R hmin hle eps heps

end ContactAndLiftSupport

/-- sec2_obstacle.tex l.58-60: "Γ_C(y, t) ≥ (C^p − 1 + o(1)) e^{qy} as y → +∞ and Γ_C(y,t) ≥ (C^p − |ρ|^p + o(1)) e^{−qy}
as y → −∞, uniformly in t; so the infimum is attained in a fixed interval [−Y₀, Y₀]". The row states both
limits, uniformly in every real angle, for C > max(1, |ρ|). -/
theorem slice_O11 {p : ℝ} (hp : 1 < p) (C : ℝ) (rho : ℂ) (hC : max 1 ‖rho‖ < C) :
    (∀ eps : ℝ, 0 < eps → ∃ Y : ℝ, ∀ y t : ℝ, Y < y →
      |gamma p C rho y t / Real.exp (p / 2 * y) - (C ^ p - 1)| < eps) ∧
    (∀ eps : ℝ, 0 < eps → ∃ Y : ℝ, ∀ y t : ℝ, y < Y →
      |gamma p C rho y t / Real.exp (-(p / 2) * y) - (C ^ p - ‖rho‖ ^ p)| < eps) ∧
    UniformCoercive p C rho :=
  GKSharp.Asymptotics.slice_O11_proved hp C rho hC

section ContactDerivativesAndDisc
open Set GKSharp.Threshold

/-- sec4b_failure.tex:38–41 ("Both χ and L are harmonic in (y, t), so L_tt = −L_yy"); actual contact harmonicity and G derivatives. -/
theorem contact_harmonic_derivatives (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let t := theta p
    let LL := logGap p lam
    let PP := weightP p lam y t
    let GG := fun y t => bigG p (gk p lam) lam (zeta y t)
    LL y t = 0 ∧ dy LL y t = 0 ∧ dtt LL y t = -dyy LL y t ∧
    dt GG y t = p * PP * dt LL y t ∧
    dyy GG y t = p * PP * dyy LL y t ∧
    dty GG y t = p * PP * (dty LL y t + p * dy (chi lam) y t * dt LL y t) ∧
    dtt GG y t = p * PP * (dtt LL y t + p * dt LL y t ^ 2 +
      2 * p * dt (chi lam) y t * dt LL y t) :=
  GKSharp.contact_harmonic_derivatives_proved p lam hp hp2 hlam

/-- sec4b_failure.tex:46–49 ("In particular ∂²_yΓ_C = e^{−qy}p𝒫 L_yy > 0"); actual partial derivative values and strictly positive Gamma_yy. -/
theorem contact_derivative_values (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let t := theta p
    let v := vContact p lam
    dt (logGap p lam) y t = -(1 - lam) / (sn p * v) ∧
    dyy (logGap p lam) y t = (1 - lam) * cs p / (sn p ^ 2 * v) ∧
    dty (logGap p lam) y t = (1 - lam) * sigmaContact p lam / (sn p * v ^ 2) ∧
    dy (chi lam) y t = (1 - lam / rContact p lam * cs p) / dOne p lam ∧
    dt (chi lam) y t = -(lam / rContact p lam * sn p) / dOne p lam ∧
    0 < dyy (gammaGK p lam) y t :=
  GKSharp.contact_derivative_values_proved p lam hp hp2 hlam

/-- sec5f_strip.tex:23 ("C = C(δ) is the root near 1 of s₀C² − δC − s₀(1 − δ) = 0"); the positive root, for both signs of δ. -/
theorem sec5_cDelta_quadratic (p delta : ℝ) (hp : 1 < p) (hd : delta < 1) :
    sn p * cDelta p delta ^ 2 - delta * cDelta p delta - sn p * (1 - delta) = 0 ∧ 0 < cDelta p delta :=
  GKSharp.cDelta_quadratic_proved p delta hp hd

/-- sec5f_strip.tex:61 ("(C^p − 1)/(C − 1) = pE(−pL)/E(−L) with L = log C"); removable values at x = 1 and p = 0 included. -/
theorem sec5_powSlope_exprel (p x : ℝ) (hx : 0 < x) :
    powSlope p x = p * exprel (-p * Real.log x) / exprel (-Real.log x) :=
  GKSharp.powSlope_exprel_proved p x hx

/-- Theorem 2.2 (label R),"Only if", the lift of g and the choice of y, sec2_obstacle.tex l.82-95; conclusion l.94-95:
"Since ε>0 is arbitrary, ∫_T M(g) dθ/(2π) ≥ 0 for every polynomial g with g(0) = 0, where M(ζ) = |ζ|^q m_C(arg ζ),
M(0) = 0, is continuous on ℂ". The Lean
proof takes the alternative lift (route R4), not the printed Blaschke/square-root/Fejér steps. -/
theorem slice_O24 {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    (P : RieszProjection p) (C : ℝ) (rho : ℂ) (hC : max 1 ‖rho‖ < C)
    (hbound : pencilNorm P rho ≤ C) :
    Continuous (homogeneousObstacle p C rho) ∧ homogeneousObstacle p C rho 0 = 0 ∧
      PolynomialDiscBound (homogeneousObstacle p C rho) :=
  GKSharp.slice_O24_proved hp P C rho hC hbound

end ContactDerivativesAndDisc

/-- sec2_obstacle.tex l.67-68: "φ is q-subtrigonometric if and only if φ is continuous and φ'' + q²φ ≥ 0" (chord form of
trigonometric q-convexity, Levin Lecture 8). Throughout sec2, q = p/2 > 1/2 (P019_paper.tex l.58). -/
theorem sec2_qsub_iff_trigconvex {q : ℝ} (hq : 1 / 2 < q) {φ : ℝ → ℝ} :
    QSubtrig q φ ↔ Function.Periodic φ (2 * Real.pi) ∧ Continuous φ ∧ TrigConvex q φ :=
  TheoremRIf.qsub_iff_continuous_trigconvex hq

/-- The chord form `TrigConvex q f` is the shared `Threshold.QTrigConvex q f` (q > 0). Bridge for route R10
(Lemma 2.3 (label chord), sec2_obstacle.tex l.106-108: "Let φ be q-subtrigonometric, c ∈ ℝ and 0 < s ≤ π/q. Then
φ(c − s) + φ(c + s) ≥ 2 cos(qs) φ(c)"). -/
theorem trigconvex_iff_QTrigConvex {q : ℝ} (hq : 0 < q) (f : ℝ → ℝ) : TrigConvex q f ↔ Threshold.QTrigConvex q f :=
  TheoremRIf.trigConvex_iff_qTrigConvex hq f

/-- sec2_obstacle.tex l.67-69: "φ is q-subtrigonometric if and only if φ is continuous and φ″ + q²φ ≥ 0 in
the sense of distributions on ℝ (“trigonometrically q-convex” functions, Levin, Lecture 8)". This row is the
"only if" half, with q-convexity in its three-point sine form `Threshold.QTrigConvex`, for q > 1/2
(q = p/2, P019_paper.tex l.58); used in sec4a_criterion.tex l.66-74. -/
theorem qsub_continuous_trigconvex (qq : ℝ) (hq : 1 / 2 < qq)
    (phi : ℝ → ℝ) (hphi : QSubtrig qq phi) : Continuous phi ∧ Threshold.QTrigConvex qq phi :=
  TheoremRIf.qsub_continuous_trigconvex_proved qq hq phi hphi

/-- sec4a_criterion.tex l.63-64: "The 2π-periodic extension of t ↦ K cos(q|t|), |t| ≤ π, is q-subtrigonometric: it
solves φ″ + q²φ = 0 except at the odd multiples of π, and there its derivative jumps from −Kq sin(qπ) to
+Kq sin(qπ), an upward jump" (K ≥ 0, 1 < p < 2; the row writes the function as K cos(q arg e^{it})). -/
theorem sec4_cosine_qsub (p KK : ℝ) (hp : 1 < p) (hp2 : p < 2) (hK : 0 ≤ KK) :
    QSubtrig (Threshold.q p) (fun t : ℝ => KK * Real.cos
      (Threshold.q p * Complex.arg (Complex.exp (Complex.I * (t : ℂ))))) :=
  TheoremRIf.sec4_cosine_qsub_proved p KK hp hp2 hK

/-- sec2_obstacle.tex l.76-77: "S(ζ) = |ζ|^q φ(arg ζ) is subharmonic on ℂ \ {0} and tends to 0 at 0 (φ is
bounded), so it extends subharmonically to ℂ with S(0) = 0". Range q > 1/2: P019_paper.tex l.58 "q = p/2",
1 < p < ∞. -/
theorem slice_O19 (q : ℝ) (hq : 1 / 2 < q) (φ : ℝ → ℝ) (hφ : QSubtrig q φ) :
    Continuous (angularPotential q φ) ∧ angularPotential q φ 0 = 0 ∧
      IsSubharmonic (fun z => (angularPotential q φ z : EReal)) :=
  TheoremRIf.removable_origin hq hφ

/-- sec2_obstacle.tex l.77-80: "Ψ(z, w) = S(zw) is plurisubharmonic and Ψ ≤ G_C ... where zw = 0, Ψ = 0 ≤ G_C ...
For polynomials with w(0) = 0 the sub-mean-value property ... gives ∫_T G_C(z, w) dθ/(2π) ≥ ∫_T Ψ(z, w) dθ/(2π) ≥
Ψ(z(0), 0) = 0". -/
theorem slice_O20 {p : ℝ} (hp : 1 < p) (C : ℝ) (ρ : ℂ) (hC : max 1 ‖ρ‖ < C)
    (φ : ℝ → ℝ) (hφ : QSubtrig (p / 2) φ) (hle : ∀ t, φ t ≤ obstacle p C ρ t) :
    IsPSH (fun zw => (angularPotential (p / 2) φ (zw.1 * zw.2) : EReal)) ∧
    (∀ z w : ℂ, angularPotential (p / 2) φ (z * w) ≤ pairObstacle p C ρ z w) ∧
    PolynomialPairBound p C ρ :=
  TheoremRIf.slice_O20_proved hp C ρ hC φ hφ hle

/-- Theorem 2.2 (label R),sec2_obstacle.tex l.72-73: "N_p(ρ) ≤ C if and only if there is a q-subtrigonometric φ with
φ ≤ m_C on ℝ". This row is the "if" direction (proof l.76-80), for 1 < p < ∞, ρ ∈ ℂ, C > max(1, |ρ|), q = p/2. -/
theorem thmR_if {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) (ρ : ℂ) (C : ℝ)
    (hC : max 1 ‖ρ‖ < C) :
    (∃ φ : ℝ → ℝ, QSubtrig (p / 2) φ ∧ ∀ t, φ t ≤ obstacle p C ρ t) → pencilNorm P ρ ≤ C :=
  TheoremRIf.thmR_if hp P ρ hC

/-- Theorem 2.2 (label R),"Only if", the largest minorant M̲, sec2_obstacle.tex l.98-101: "M̲(τζ) = τ^q M̲(ζ). Hence
M̲(ζ) = |ζ|^q φ(arg ζ)"; "If φ(t₀) = −∞, then M̲ = −∞ on a ray; this is impossible, since a ray is not polar and
M̲ ≢ −∞"; "Thus φ is finite and its homogeneous extension is the subharmonic function M̲; by Definition 2.1, it is
q-subtrigonometric". The row: any q-homogeneous subharmonic V with V(0) ≥ 0, q > 1/2 (q = p/2, P019_paper.tex l.58);
it also states that φ is continuous (proved). -/
theorem slice_O27 (q : ℝ) (hq : 1 / 2 < q) (V : ℂ → EReal) (hV : IsSubharmonic V)
    (h0 : 0 ≤ V 0)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z) :
    (∀ t : ℝ, V (unitPoint t) ≠ ⊥) ∧ ∃ phi : ℝ → ℝ, Continuous phi ∧ QSubtrig q phi ∧
      ∀ z : ℂ, V z = (angularPotential q phi z : EReal) :=
  GKSharp.slice_O27_proved q hq V hV h0 hhom

/-- sec2_obstacle.tex:82–101 (proof of Theorem 2.2 (label R), "Only if"); the proof uses the cited [HKV, Theorem 2.1], l.97. -/
theorem thmR_only_if {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p)
    (rho : ℂ) (C : ℝ) (hC : max 1 ‖rho‖ < C) (hbound : pencilNorm P rho ≤ C) :
    ∃ phi : ℝ → ℝ, QSubtrig (p / 2) phi ∧ ∀ t, phi t ≤ obstacle p C rho t :=
  GKSharp.thmR_only_if hp P rho hC hbound

/-- sec2_obstacle.tex:73–74 ("Hence N_p(ρ) = inf{C : such a φ exists}"); exact infimum assembly including the norm=max boundary. -/
theorem slice_O28 {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) (rho : ℂ)
    (hlo : max 1 ‖rho‖ ≤ pencilNorm P rho)
    (hiff : ∀ C : ℝ, max 1 ‖rho‖ < C → (pencilNorm P rho ≤ C ↔
      ∃ phi : ℝ → ℝ, QSubtrig (p / 2) phi ∧ ∀ t, phi t ≤ obstacle p C rho t)) :
    pencilNorm P rho = sInf {C : ℝ | max 1 ‖rho‖ < C ∧ ∃ phi : ℝ → ℝ,
      QSubtrig (p / 2) phi ∧ ∀ t, phi t ≤ obstacle p C rho t} :=
  GKSharp.slice_O28_proved P rho hlo hiff

/-- Theorem 2.2 (label R),sec2_obstacle.tex:71–74 (proof l.75–101): "Then N_p(ρ) ≤ C if and only if there is a q-subtrigonometric
φ with φ ≤ m_C on ℝ. Hence N_p(ρ) = inf{C : such a φ exists}" (all 1 < p < ∞, all complex ρ). The "only if" part of the
proof uses the cited [HKV, Theorem 2.1], l.97. -/
theorem slice_O18 {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p)
    (rho : ℂ) (C : ℝ) (hC : max 1 ‖rho‖ < C) :
    (pencilNorm P rho ≤ C ↔ ∃ phi : ℝ → ℝ, QSubtrig (p / 2) phi ∧ ∀ t, phi t ≤ obstacle p C rho t) ∧
    pencilNorm P rho = sInf {D : ℝ | max 1 ‖rho‖ < D ∧ ∃ phi : ℝ → ℝ,
      QSubtrig (p / 2) phi ∧ ∀ t, phi t ≤ obstacle p D rho t} :=
  GKSharp.slice_O18_proved hp P rho C hC


section DifferentialAndCoverage
open Set Filter GKSharp.Threshold
open scoped Topology ContDiff

/-- Proposition 5.12 (label red), proof, the real segment I, sec5d_monotone.tex l.132-134: "Φ′(ρ) = −(1−λ)^p pρ^{p−1} − KqQ_ℝ^{q−1}(1 + λ − 2ρ)";
"For ρ ≤ ρ₁ := (1+λ)/2 both terms of the middle expression are ≤ 0, the first < 0" (K ≥ 0, Q_ℝ = (ρ−λ)(1−ρ) > 0). -/
theorem reduction_phi_neg_below_mid {p C K lam ρ : ℝ}
    (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hρ0 : 0 < ρ) (hQ : 0 < (ρ - lam) * (1 - ρ))
    (hK : 0 ≤ K) (hρ1 : ρ ≤ (1 + lam) / 2) :
    -(1 - lam) ^ p * p * ρ ^ (p - 1) -
      K * (p / 2) * ((ρ - lam) * (1 - ρ)) ^ (p / 2 - 1) * (1 + lam - 2 * ρ) < 0 :=
  GKSharp.Proofs.RealSegmentSign.reduction_phi_neg_below_mid_proved (C := C) hp1 hp2 hl hl1 hρ0 hQ hK hρ1

/-- (5.3), sec5_sharp_inequality.tex l.35-39 (`1 < p < 2`, `−1 ≤ λ < 1`, `ρ > 0`, `0 < φ < π`): "Im Q > 0
and f_ρ is smooth"; "f_ρ′(φ) = −q|Q|^{q−1} Im(v̄ w)", `θ = arg Q`, `v = e^{iω} + λe^{−iω}`, `ω = (1−q)θ`.
(The second form of (5.3) and "f′ = 0 iff D = 0" are the row `eq_5_3_second`.) -/
theorem eq_5_3 {p lam ρ φ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam)
    (hl1 : lam < 1) (hρ : 0 < ρ) (hφ0 : 0 < φ) (hφ : φ < Real.pi) :
    0 < (mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))).im ∧
    ContDiffAt ℝ ∞ (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ ∧
    HasDerivAt (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2))
      (-(p / 2) * ‖mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))‖ ^ (p / 2 - 1) *
        (conj (curveV p lam (Complex.arg (mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))))) *
          ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))).im) φ :=
  GKSharp.Proofs.EllipseCalculus.eq_5_3_proved hp1 hp2 hl hl1 hρ hφ0 hφ

/-- Lemma 5.4 (label A), (5.6), sec5_sharp_inequality.tex l.64-67: at every critical point of `f_ρ` in `(0, π)`,
"f_ρ″ = q|Q|^{q−2}τ²(1−λ)²[(1−q)(1+λ)² cos(qθ) − |v|² sin ω/sin θ] < 0", `τ = ρ/|v|`. (The bracket is
`lemmaA_bracket`.) -/
theorem eq_5_6 {p lam ρ φ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam)
    (hl1 : lam < 1) (hρ : 0 < ρ) (hφ0 : 0 < φ) (hφ : φ < Real.pi)
    (hcrit : deriv (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ = 0) :
    let Q := mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
    let θ := Complex.arg Q
    let τ := ρ / ‖curveV p lam θ‖
    HasDerivAt (deriv fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2))
      (p / 2 * ‖Q‖ ^ (p / 2 - 2) * τ ^ 2 * (1 - lam) ^ 2 *
        ((1 - p / 2) * (1 + lam) ^ 2 * Real.cos (p / 2 * θ) -
          ‖curveV p lam θ‖ ^ 2 * (Real.sin ((1 - p / 2) * θ) / Real.sin θ))) φ ∧
    p / 2 * ‖Q‖ ^ (p / 2 - 2) * τ ^ 2 * (1 - lam) ^ 2 *
      ((1 - p / 2) * (1 + lam) ^ 2 * Real.cos (p / 2 * θ) -
        ‖curveV p lam θ‖ ^ 2 * (Real.sin ((1 - p / 2) * θ) / Real.sin θ)) < 0 :=
  GKSharp.Proofs.CriticalMaximum.eq_5_6_proved hp1 hp2 hl hl1 hρ hφ0 hφ hcrit

/-- sec5d_monotone.tex l.80 (proof of Lemma 5.10 (label Bplus)): "and 4λ/(1+λ)² < 1 it suffices to show that Ψ_m ≥ m² − 1". -/
theorem sec5d_lambda_threshold_lt_one {lam : ℝ} (hl : -1 < lam) (hl1 : lam < 1) :
    4 * lam / (1 + lam) ^ 2 < 1 :=
  GKSharp.sec5d_lambda_threshold_lt_one_proved hl hl1

/-- sec5d_monotone.tex l.85-86 (proof of Lemma 5.10 (label Bplus)): "The k = 1 bracket is −(ε² − 4ε + 1) ≥ 0 for ε ≥ 2 − √3". -/
theorem sec5d_Bplus_first_bracket {eps : ℝ} (he : 2 - Real.sqrt 3 ≤ eps) (he1 : eps < 1) :
    1 + eps ^ 2 - 2 * (1 - eps) ^ 2 = -(eps ^ 2 - 4 * eps + 1) ∧
    0 ≤ 1 + eps ^ 2 - 2 * (1 - eps) ^ 2 :=
  GKSharp.sec5d_Bplus_first_bracket_proved he he1

/-- sec5d_monotone.tex l.86 (proof of Lemma 5.10 (label Bplus)): "for k ≥ 2, 2(1−ε)^{2k} ≤ 2(4 − 2√3)² < 0.58". -/
theorem sec5d_Bplus_higher_bracket {eps : ℝ} (he : 2 - Real.sqrt 3 ≤ eps) (he1 : eps < 1)
    {k : ℕ} (hk : 2 ≤ k) :
    2 * (1 - eps) ^ (2 * k) ≤ 2 * (4 - 2 * Real.sqrt 3) ^ 2 ∧
    2 * (4 - 2 * Real.sqrt 3) ^ 2 < (58 / 100 : ℝ) :=
  GKSharp.sec5d_Bplus_higher_bracket_proved he he1 hk

/-- sec5d_monotone.tex l.81 (proof of Lemma 5.10 (label Bplus)): "log(1−u) = −∑_k u^k/k". -/
theorem sec5d_log_series {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun k : ℕ => u ^ (k + 1) / ((k : ℝ) + 1)) (-Real.log (1 - u)) :=
  GKSharp.sec5d_log_series_proved hu hu1

/-- sec5d_monotone.tex l.81 (proof of Lemma 5.10 (label Bplus)): "by sin y = y∏_n (1 − y²/(nπ)²)", as a convergent product for
sin x / x. -/
theorem sec5d_euler_sine_product {x : ℝ} (hx : 0 < x) (hxπ : x < Real.pi) :
    HasProd (fun n : ℕ => 1 - x ^ 2 / (((n : ℝ) + 1) * Real.pi) ^ 2) (Real.sin x / x) :=
  GKSharp.sec5d_euler_sine_product_proved hx hxπ

/-- sec4a_criterion.tex l.72-73: "at θ₀ this sinusoid is K cos(qt), since φ(θ₀)=0 and φ′(θ₀⁺)=−Kq, and [θ₀, π] has length
π − π/p < π/q". -/
theorem sec4_arch_interval_length (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    Real.pi - Real.pi / p < Real.pi / q p :=
  GKSharp.sec4_arch_interval_length_proved p hp hp2

/-- sec4a_criterion.tex l.90: "The value s_* minimizes s ↦ (A+s)/(s(1−s))^q, which tends to +∞ at both
ends and has one critical point". -/
theorem sec4_omegaFirst_unique_critical (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ∀ s ∈ Ioo (0 : ℝ) 1, deriv (omegaFirst p) s = 0 ↔ s = sStar p :=
  GKSharp.sec4_omegaFirst_unique_critical_proved p hp hp2

/-- sec4b_failure.tex l.28-29 (on the ray t = θ₀, ζ = re^{iθ₀}, every r > 0):
"Re[(ζ + λ)(ζ + 1)/ζ] = 1 + λ − c₀(r + λ/r)". -/
theorem sec4_contact_ray_real_part (p lam r : ℝ) (hr : 0 < r) :
    (((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)) + lam) *
        ((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)) + 1) /
      ((r : ℂ) * Complex.exp (Complex.I * (theta p : ℂ)))).re =
      1 + lam - cs p * (r + lam / r) :=
  GKSharp.sec4_contact_ray_real_part_proved p lam r hr

/-- sec4b_failure.tex l.100-101 (proof of Lemma 4.6 (label Pc), the range [3/2, 2)):
"F/η² ≤ 1/(p−1) − (π/p)²(1 − x²/6)² ≤ 2 − (π²/4)(1 − π²/216)² < −0.24" (the last numerical inequality). -/
theorem sec4_localF_endpoint_constant :
    2 - (Real.pi ^ 2 / 4) * (1 - Real.pi ^ 2 / 216) ^ 2 < -(6 / 25 : ℝ) :=
  GKSharp.sec4_localF_endpoint_constant_proved

/-- sec4b_failure.tex l.112: "For fixed 1 < p < 2, the functions λ ↦ GK_p(λ) and λ ↦ K are
continuous on (−1, 1)." -/
theorem sec4_gk_kconst_continuous (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ContinuousOn (fun lam : ℝ => gk p lam) (Ioo (-1 : ℝ) 1) ∧
      ContinuousOn (kConst p) (Ioo (-1 : ℝ) 1) :=
  GKSharp.sec4_gk_kconst_continuous_proved p hp hp2

/-- sec4a_criterion.tex l.86-88: "At the point ρ_* = 1 − s_*δ we have Q(ρ_*) = s_*(1−s_*)δ² exactly
and (C^p − ρ_*^p)/δ → p(A + s_*), so limsup_{δ→0} m_GK(0)/δ ≤ p(A + s_*)/(s_*(1−s_*))^q" (stated in ε form).
The direct witness route is route difference R3. -/
theorem sec4_limsup_axis (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ∀ eps > 0, ∀ᶠ delta in 𝓝[>] (0 : ℝ),
      Threshold.obstacle p (1 - delta) 0 / delta ≤ omegaFirst p (sStar p) + eps :=
  GKSharp.sec4_limsup_axis_proved p hp hp2

/-- sec5_sharp_inequality.tex l.19 (`1 < p < 2`, `q = p/2`): "x ↦ Re x^q is nondecreasing on ℝ, since cos(qπ) < 0"
(Re x^q = |x|^q cos(q arg x), P019_paper.tex l.139). (Continuity on ℂ is `reQPow_continuous`.) -/
theorem sec5_reQPow_monotone {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    Monotone (fun x : ℝ => reQPow (x : ℂ) (p / 2)) :=
  GKSharp.sec5_reQPow_monotone_proved hp1 hp2

/-- (E3), sec5_sharp_inequality.tex l.95-96: "Q(ρ) − Q(−ρ) = 2(1+λ)ρ ≥ 0 (both real) gives max f_ρ = f_ρ(0)" (Q at
w = ±ρ; the row's `Q(φ) = Q(ρe^{iφ})`, so these are `Q 0`, `Q π`; with `sec5_reQPow_monotone`: `f_ρ(π) ≤ f_ρ(0)`). -/
theorem sec5_Q_ends {p lam ρ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (_hl1 : lam < 1)
    (hρ : 0 < ρ) :
    let Q : ℝ → ℂ := fun φ => mobQ lam ((ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
    (Q 0).im = 0 ∧ (Q Real.pi).im = 0 ∧ Q 0 - Q Real.pi = ((2 * (1 + lam) * ρ : ℝ) : ℂ) ∧
    0 ≤ 2 * (1 + lam) * ρ ∧
    reQPow (Q Real.pi) (p / 2) ≤ reQPow (Q 0) (p / 2) :=
  GKSharp.sec5_Q_ends_proved hp1 hp2 hl _hl1 hρ

/-- Lemma 5.5 (label contact), sec5_sharp_inequality.tex l.111-113 (`1 < p < 2`, `−1 ≤ λ < 1`, `C = GK_p(λ)`, `K` of
eq:K, `θ₀ = π/p`): "We have ρ(θ₀) = C, Λ(θ₀) = 0 and K_f(θ₀) = K. Moreover z_* := z_{θ₀} = 1/ζ_* with ζ_* = r_*e^{iθ₀}
(Lemma 4.1), so |z_*| = 1/r_*" (`r_*` = contactRadius). -/
theorem lemma_contact {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    ‖mobW lam (curveZ p lam (Real.pi / p))‖ = gk p lam ∧
    critD p (gk p lam) (kConst p lam) lam (curveZ p lam (Real.pi / p)) = 0 ∧
    curveKf p lam (Real.pi / p) = kConst p lam ∧
    curveZ p lam (Real.pi / p) =
      1 / ((contactRadius p lam : ℂ) * Complex.exp (((Real.pi / p : ℝ) : ℂ) * Complex.I)) ∧
    ‖curveZ p lam (Real.pi / p)‖ = 1 / contactRadius p lam :=
  ⟨contact_rho hp1 hp2 hl hl1, contact_Lambda hp1 hp2 hl hl1 _, contact_Kf hp1 hp2 hl hl1,
    (contact_point hp1 hp2 hl hl1).1, (contact_point hp1 hp2 hl hl1).2⟩

end DifferentialAndCoverage


section InstalledContactC1

open Set Filter GKSharp.Threshold
open scoped Topology ContDiff

/-- sec4b_failure.tex l.30-33: "So the contact point is ζ_* = re^{iθ₀} with r + λ/r = σ := (1+λ)/c₀, r > 1
the larger root"; l.31 "At the contact point, Γ_C = ∂_yΓ_C = 0 at (y_*, θ₀), y_* = log r"; "∂²_yΓ_C(y_*, θ₀) > 0". -/
theorem contact_spec (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    1 < rContact p lam ∧ |lam| < rContact p lam ∧ 0 < vContact p lam ∧
    rContact p lam + lam / rContact p lam = sigmaContact p lam ∧
    gammaGK p lam (yContact p lam) (theta p) = 0 ∧
    dy (gammaGK p lam) (yContact p lam) (theta p) = 0 ∧
    0 < dyy (gammaGK p lam) (yContact p lam) (theta p) :=
  GKSharp.contact_spec_proved p lam hp hp2 hlam

/-- sec4b_failure.tex l.40-41: "Since also G = G_y = 0 there, e^{qy}∂²_tΓ_C = G_tt, e^{qy}∂²_yΓ_C = G_yy
and e^{qy}∂_t∂_yΓ_C = G_ty − qG_t". -/
theorem sec4_contact_gamma_scaling (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let t := theta p
    let GG := fun y t => bigG p (gk p lam) lam (zeta y t)
    Real.exp (q p * y) * dtt (gammaGK p lam) y t = dtt GG y t ∧
    Real.exp (q p * y) * dyy (gammaGK p lam) y t = dyy GG y t ∧
    Real.exp (q p * y) * dty (gammaGK p lam) y t = dty GG y t - q p * dt GG y t :=
  GKSharp.contact_gamma_scaling_proved p lam hp hp2 hlam

/-- sec4b_failure.tex l.35-42: "μ_*″ = ∂²_tΓ_C − (∂_t∂_yΓ_C)²/∂²_yΓ_C" and, from the exponential scaling, (4.3):
"e^{qy_*}μ_*″(θ₀)/(p𝒫) =[L_yy(2pχ_tL_t + pL_t²) − L_yy² − (L_ty + L_t(pχ_y − q))²]/L_yy". -/
theorem contact_schur_identity (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let t := theta p
    let LL := logGap p lam
    Real.exp (q p * y) * muSecond p lam / (p * weightP p lam y t) =
      (dyy LL y t * (2 * p * dt (chi lam) y t * dt LL y t + p * dt LL y t ^ 2) -
        dyy LL y t ^ 2 - (dty LL y t + dt LL y t * (p * dy (chi lam) y t - q p)) ^ 2) /
        dyy LL y t :=
  GKSharp.contact_schur_identity_proved p lam hp hp2 hlam

/-- sec4b_failure.tex l.57-65: "Substituting (4.4) into (4.3) first yields" the displayed expansion of
e^{qy_*}μ_*″(θ₀)/(p𝒫). -/
theorem contact_schur_expanded (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let r := rContact p lam
    let v := vContact p lam
    Real.exp (q p * y) * muSecond p lam / (p * weightP p lam y (theta p)) =
      2 * p * lam * (1 - lam) / (r * v * dOne p lam) +
      p * (1 - lam) ^ 2 / (sn p ^ 2 * v ^ 2) - (1 - lam) * cs p / (sn p ^ 2 * v) -
      (1 - lam) / (cs p * v) *
        (sigmaContact p lam / v - p * dy (chi lam) y (theta p) + p / 2) ^ 2 :=
  GKSharp.contact_schur_expanded_proved p lam hp hp2 hlam

/-- sec4b_failure.tex l.68-77: "Put B₀ = δ(1+λ)²/(c₀³s₀²v³) > 0" (`δ = 1 − λ`); "The second identity and
c₀² + s₀² = 1 now yield e^{qy_*}μ_*″(θ₀)/(p𝒫) = B₀[(p−1)(1 − 4λc₀⁴/(1+λ)²) − p²s₀²/4]";
"Thus μ_*″(θ₀) < 0 if and only if (pp′/4)s₀² + 4λc₀⁴/(1+λ)² > 1"; and l.86 (proof of Corollary 4.5):
"\eqref{eq:signid} holds for every $\lambda\in(-1,1)$ (the same computation)" (the hypothesis `λ ∈ (−1, 1)` is this
range). -/
theorem contact_sign_factorization (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    0 < bZero p lam ∧
    Real.exp (q p * yContact p lam) * muSecond p lam /
      (p * weightP p lam (yContact p lam) (theta p)) = bZero p lam * signBracket p lam ∧
    (muSecond p lam < 0 ↔ 1 < localTest p lam) :=
  GKSharp.contact_sign_factorization_proved p lam hp hp2 hlam

/-- Corollary 4.5 (label L0), sec4b_failure.tex l.81-82: "Let 1<p<2 and −1 < λ ≤ 0, and let μ_* be defined as in the
proof of Theorem 4.4. Then μ_*″(θ₀) > 0." (proof l.85-88). -/
theorem corollary_L0 (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioc (-1 : ℝ) 0) : 0 < muSecond p lam :=
  GKSharp.corollary_L0_proved p lam hp hp2 hlam

/-- sec4b_failure.tex l.33-35: "By the implicit function theorem there is a smooth branch y_*(t) of ∂_yΓ_C = 0
near θ₀, and m_C(t) ≤ μ_*(t) := Γ_C(y_*(t), t) with μ_*(θ₀) = 0". -/
theorem contact_envelope (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    ∃ branch : ℝ → ℝ, ∃ eps > 0,
      branch (theta p) = yContact p lam ∧
      ContDiffOn ℝ ∞ branch (Ioo (theta p - eps) (theta p + eps)) ∧
      (∀ t ∈ Ioo (theta p - eps) (theta p + eps),
        dy (gammaGK p lam) (branch t) t = 0 ∧
        Threshold.obstacle p lam t ≤ gammaGK p lam (branch t) t) ∧
      deriv (deriv (fun t => gammaGK p lam (branch t) t)) (theta p) = muSecond p lam :=
  GKSharp.contact_envelope_proved p lam hp hp2 hlam

/-- sec4b_failure.tex l.35-36: "The odd terms cancel, so m_C(θ₀ − s) + m_C(θ₀ + s) ≤ μ_*″(θ₀)s² + O(s⁴).
It therefore suffices to prove that (4.2) implies μ_*″(θ₀) < 0." (Lean: μ_*″(θ₀) < 0 gives a small s ≠ 0 with a negative
pair, from the smooth branch.) -/
theorem negative_pair_of_muSecond (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) (hmu : muSecond p lam < 0) :
    ∃ eps > 0, ∀ s ∈ Ioo (0 : ℝ) eps,
      Threshold.obstacle p lam (theta p - s) + Threshold.obstacle p lam (theta p + s) < 0 :=
  GKSharp.negative_pair_of_muSecond_proved p lam hp hp2 hlam hmu

/-- sec4b_failure.tex l.113: "The coercivity in Section 2.2 is locally uniform in λ with C = GK_p(λ) > max(1, |λ|),
so the infimum defining m_GK(0) can locally be restricted to a common compact interval in y." -/
theorem sec4_coercive_local_uniform (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    ∃ eps > 0, Icc (lam - eps) (lam + eps) ⊆ Ioo (-1 : ℝ) 1 ∧
      (∀ B : ℝ, ∃ Y > 0, ∀ ll ∈ Icc (lam - eps) (lam + eps),
        ∀ y t : ℝ, Y ≤ |y| → B ≤ gammaGK p ll y t) ∧
      (∃ Y > 0, ∀ ll ∈ Icc (lam - eps) (lam + eps),
        ∃ yy ∈ Icc (-Y) Y, Threshold.obstacle p ll 0 = gammaGK p ll yy 0 ∧
          ∀ y : ℝ, gammaGK p ll yy 0 ≤ gammaGK p ll y 0) :=
  GKSharp.sec4_coercive_local_uniform_proved p lam hp hp2 hlam

/-- sec4b_failure.tex l.114: "Joint continuity of Γ_C(y, 0) then implies that λ ↦ m_GK(0), and hence
λ ↦ h(λ, p), is continuous." -/
theorem sec4_mGK0_h_continuous (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ContinuousOn (fun lam : ℝ => Threshold.obstacle p lam 0) (Ioo (-1 : ℝ) 1) ∧
      ContinuousOn (h p) (Ioo (-1 : ℝ) 1) :=
  GKSharp.sec4_mGK0_h_continuous_proved p hp hp2

/-- sec4b_failure.tex l.114: "λ ↦ h(λ, p), is continuous" (on (−1, 1); used for the smallest zero of h(·, p), l.118). -/
theorem sec4_h_continuousOn (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ContinuousOn (h p) (Ioo (-1 : ℝ) 1) :=
  GKSharp.sec4_h_continuousOn_proved p hp hp2

/-- sec4b_failure.tex l.38: "write G = 𝒫(e^{pL} − 1) with 𝒫 = e^{pχ}, χ = log|ζ + λ|, L = log C − log|w|." -/
theorem sec4_contact_G_factor (p lam y t : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1)
    (hz : zeta y t + (lam : ℂ) ≠ 0) (hz1 : zeta y t + 1 ≠ 0) :
    bigG p (gk p lam) lam (zeta y t) =
      weightP p lam y t * (Real.exp (p * logGap p lam y t) - 1) :=
  GKSharp.sec4_contact_G_factor_proved p lam y t hp hp2 hlam hz hz1

/-- sec4b_failure.tex l.44-45: "There (ζ + λ)(ζ + 1)/ζ = is₀v, so ℓ′ = −i(1 − λ)/(s₀v) and
ℓ″ = (1 − λ)(ζ − λ/ζ)/(s₀v)² with ζ_* − λ/ζ_* = −c₀v + is₀σ" (ℓ′ is the printed local-log derivative of l.28;
no global log branch is used). -/
theorem sec4_contact_complex_values (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let zz : ℂ := (rContact p lam : ℂ) * Complex.exp (Complex.I * (theta p : ℂ))
    let uu : ℂ := (yContact p lam : ℂ) + Complex.I * (theta p : ℂ)
    let vv : ℂ := ((sn p * vContact p lam : ℝ) : ℂ)
    (zz + (lam : ℂ)) * (zz + 1) / zz = Complex.I * vv ∧
    (1 - (lam : ℂ)) * zz / ((zz + (lam : ℂ)) * (zz + 1)) =
      -Complex.I * (((1 - lam) / (sn p * vContact p lam) : ℝ) : ℂ) ∧
    deriv (fun u : ℂ => (1 - (lam : ℂ)) * Complex.exp u /
      ((Complex.exp u + (lam : ℂ)) * (Complex.exp u + 1))) uu =
      (1 - (lam : ℂ)) * (zz - (lam : ℂ) / zz) / vv ^ 2 ∧
    zz - (lam : ℂ) / zz = -((cs p * vContact p lam : ℝ) : ℂ) +
      Complex.I * ((sn p * sigmaContact p lam : ℝ) : ℂ) :=
  GKSharp.sec4_contact_complex_values_proved p lam hp hp2 hlam

/-- Consequence (E1), sec5_sharp_inequality.tex l.88: "For each ρ > 0, f_ρ has at most one critical
point in (0, π)". -/
theorem sec5_A1 {p lam ρ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) (hρ : 0 < ρ) :
    Set.Subsingleton {φ | φ ∈ Set.Ioo 0 Real.pi ∧ deriv (fun x => fRho p lam ρ x) φ = 0} :=
  GKSharp.sec5_A1_proved hp1 hp2 hl hl1 hρ

end InstalledContactC1


section SectionThreeComplete

open Filter
open scoped Topology

/-- Chord inequality, sec2_obstacle.tex:106–108; q=p/2>1/2. Route R10 records the elementary trig-convex proof. -/
theorem slice_O30 (q : ℝ) (hq : 1 / 2 < q) (φ : ℝ → ℝ) (hφ : QSubtrig q φ)
    (c s : ℝ) (hs : 0 < s ∧ s ≤ Real.pi / q) :
    2 * Real.cos (q * s) * φ c ≤ φ (c - s) + φ (c + s) :=
  ChordGK.slice_O30_proved q hq φ hφ c s hs

/-- The window, sec3_nonreal.tex l.23-26 (`C > max(1, |ρ|)`, `ρ ≠ 1`): "m_C(t) < 0 exactly when the ray
arg ζ = t meets U_C, and m_C(t) = 0 when the ray is tangent to ∂U_C (the infimum is then attained at the tangent
point). So {t : m_C(t) < 0} is the open window (arg c − ψ, arg c + ψ)". (The cosine form is the window mod 2π;
`ψ ∈ (0, π/2)` is `eq_3_3`.) -/
theorem sec3_window {p C : ℝ} (hp : 1 < p) {ρ : ℂ} (hρ : ρ ≠ 1) (hC : max 1 ‖ρ‖ < C) :
    (∀ t : ℝ, obstacle p C ρ t < 0 ↔ ∃ r : ℝ, 0 < r ∧ obstacleG p C ρ ((r : ℂ) * unitPoint t) < 0) ∧
    (∀ t : ℝ, obstacle p C ρ t < 0 ↔
      Real.cos (windowHalfAngle C ρ) < Real.cos (t - Complex.arg (diskCentre C ρ))) ∧
    (∀ t : ℝ, Real.cos (t - Complex.arg (diskCentre C ρ)) = Real.cos (windowHalfAngle C ρ) →
      obstacle p C ρ t = 0 ∧ ∃ r : ℝ, 0 < r ∧ obstacleG p C ρ ((r : ℂ) * unitPoint t) = 0 ∧
        obstacle p C ρ t = r ^ (-(p / 2)) * obstacleG p C ρ ((r : ℂ) * unitPoint t)) :=
  GKSharp.Sec3Geom.sec3_window_proved hp hρ hC

/-- sec3_nonreal.tex l.23: "G(re^{it})/r^q → +∞ as r → 0 and as r → ∞" (`C > max(1, |ρ|)`, every
complex `ρ` and every angle `t`). -/
theorem sec3_radial_limits {p C : ℝ} (hp : 1 < p) {ρ : ℂ} (hC : max 1 ‖ρ‖ < C) (t : ℝ) :
    Tendsto (fun r : ℝ => obstacleG p C ρ ((r : ℂ) * unitPoint t) / r ^ (p / 2)) (𝓝[>] 0) atTop ∧
    Tendsto (fun r : ℝ => obstacleG p C ρ ((r : ℂ) * unitPoint t) / r ^ (p / 2)) atTop atTop :=
  GKSharp.Sec3Geom.sec3_radial_limits_proved hp hC t

/-- Theorem 3.2 (label A), proof, the two contact points, sec3_nonreal.tex l.50-53 (`C = GK_p(ρ)`, `ρ ≠ 1`): "The two
tangent lines from 0 to ∂U_C touch it at ζ₁, ζ₂ ... these points have the same modulus r = (|c|² − R²)^{1/2} and the
arguments arg c ∓ ψ ... After a relabeling ... t₂ ≡ t₁ + 2π/p (mod 2π) ... m_C(t₁) = m_C(t₂) = 0, attained at
radius r". -/
theorem thmA_step1 {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {ρ : ℂ} (hρ : ρ ≠ 1) :
    let C := gk p ρ
    let c := diskCentre C ρ
    let r := Real.sqrt (‖c‖ ^ 2 - diskRadiusSq C ρ)
    let t₁ := Complex.arg c - windowHalfAngle C ρ
    let t₂ := Complex.arg c + windowHalfAngle C ρ
    0 < r ∧ obstacleG p C ρ ((r : ℂ) * unitPoint t₁) = 0 ∧ obstacleG p C ρ ((r : ℂ) * unitPoint t₂) = 0 ∧
    obstacle p C ρ t₁ = 0 ∧ obstacle p C ρ t₂ = 0 ∧
    ∃ k : ℤ, t₂ = t₁ + 2 * Real.pi / p + 2 * Real.pi * k ∨ t₁ = t₂ + 2 * Real.pi / p + 2 * Real.pi * k :=
  GKSharp.Sec3Geom.thmA_step1_proved hp hp2 hρ

/-- Theorem 3.2 (label A), proof, the bound at the fixed radius r, sec3_nonreal.tex l.55-56 (data of `thmA_step1`,
`μ(t) = G(re^{it})/r^q`, the paper's `μ`): "m_C ≤ μ and μ(t₁) = μ(t₂) = 0, so M(t) := m_C(t) + m_C(t + 2π/p) ≤ M̃(t) :=
μ(t) + μ(t + 2π/p), M̃(t₁) = 0" (`t₁` after the relabeling of `thmA_step1`). -/
theorem thmA_step2 {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {ρ : ℂ} (hρ : ρ ≠ 1) :
    let C := gk p ρ
    let c := diskCentre C ρ
    let r := Real.sqrt (‖c‖ ^ 2 - diskRadiusSq C ρ)
    let t₁ := Complex.arg c - windowHalfAngle C ρ
    let t₂ := Complex.arg c + windowHalfAngle C ρ
    let μ := fun t : ℝ => obstacleG p C ρ ((r : ℂ) * unitPoint t) / r ^ (p / 2)
    (∀ t : ℝ, obstacle p C ρ t ≤ μ t) ∧ μ t₁ = obstacle p C ρ t₁ ∧ μ t₁ = 0 ∧
    μ t₂ = obstacle p C ρ t₂ ∧ μ t₂ = 0 ∧
    (∀ t : ℝ, obstacle p C ρ t + obstacle p C ρ (t + 2 * Real.pi / p) ≤ μ t + μ (t + 2 * Real.pi / p)) ∧
    ∀ s s' : ℝ, (s = t₁ ∧ s' = t₂ ∨ s = t₂ ∧ s' = t₁) → (∃ k : ℤ, s' = s + 2 * Real.pi / p + 2 * Real.pi * k) →
      μ s + μ (s + 2 * Real.pi / p) = 0 :=
  GKSharp.Sec3Geom.thmA_step2_proved hp hp2 hρ

/-- Theorem 3.2 (label A), proof, the first-order term, sec3_nonreal.tex l.58-66 (data of `thmA_step1`,
`ζ_k = r e^{it_k}`): "|μ′(t_k)| = p|1 − ρ| r^{1−q} C^{p−1} |ζ_k + 1|^{p−2} > 0. The signs of μ′(t₁) and μ′(t₂) are
opposite ... Hence M̃′(t₁) = ±p|1 − ρ| r^{1−q}
C^{p−1}(|ζ₁ + 1|^{p−2} − |ζ₂ + 1|^{p−2})" (`M̃(t) = μ(t) + μ(t + 2π/p)` at the relabelled `t₁`; `μ` is
2π-periodic, so `M̃′(t₁) = μ′(t₁) + μ′(t₂)`). -/
theorem thmA_step3 {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {ρ : ℂ} (hρ : ρ ≠ 1) :
    let C := gk p ρ
    let c := diskCentre C ρ
    let r := Real.sqrt (‖c‖ ^ 2 - diskRadiusSq C ρ)
    let t₁ := Complex.arg c - windowHalfAngle C ρ
    let t₂ := Complex.arg c + windowHalfAngle C ρ
    let ζ₁ : ℂ := (r : ℂ) * unitPoint t₁
    let ζ₂ : ℂ := (r : ℂ) * unitPoint t₂
    let μ := fun t : ℝ => obstacleG p C ρ ((r : ℂ) * unitPoint t) / r ^ (p / 2)
    let K₀ := p * ‖1 - ρ‖ * r ^ (1 - p / 2) * C ^ (p - 1)
    |deriv μ t₁| = K₀ * ‖ζ₁ + 1‖ ^ (p - 2) ∧ 0 < K₀ * ‖ζ₁ + 1‖ ^ (p - 2) ∧
    |deriv μ t₂| = K₀ * ‖ζ₂ + 1‖ ^ (p - 2) ∧ 0 < K₀ * ‖ζ₂ + 1‖ ^ (p - 2) ∧
    deriv μ t₁ * deriv μ t₂ < 0 ∧
    (∀ s s' : ℝ, (s = t₁ ∧ s' = t₂ ∨ s = t₂ ∧ s' = t₁) → (∃ k : ℤ, s' = s + 2 * Real.pi / p + 2 * Real.pi * k) →
      HasDerivAt (fun t => μ t + μ (t + 2 * Real.pi / p)) (deriv μ t₁ + deriv μ t₂) s) ∧
    (deriv μ t₁ + deriv μ t₂ = K₀ * (‖ζ₁ + 1‖ ^ (p - 2) - ‖ζ₂ + 1‖ ^ (p - 2)) ∨
      deriv μ t₁ + deriv μ t₂ = -(K₀ * (‖ζ₁ + 1‖ ^ (p - 2) - ‖ζ₂ + 1‖ ^ (p - 2)))) :=
  GKSharp.Sec3Geom.thmA_step3_proved hp hp2 hρ

/-- Theorem 3.2 (label A), proof, "This first-order term vanishes only for real ρ", sec3_nonreal.tex l.68-70 (data of
`thmA_step1`): "|ζ₁ + 1| = |ζ₂ + 1| ... the condition becomes c ∈ ℝ, that is, C² − ρ ∈ ℝ, or equivalently ρ ∈ ℝ". -/
theorem thmA_step4 {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {ρ : ℂ} (hρ : ρ ≠ 1) :
    let C := gk p ρ
    let c := diskCentre C ρ
    let r := Real.sqrt (‖c‖ ^ 2 - diskRadiusSq C ρ)
    ‖(r : ℂ) * unitPoint (Complex.arg c - windowHalfAngle C ρ) + 1‖ =
        ‖(r : ℂ) * unitPoint (Complex.arg c + windowHalfAngle C ρ) + 1‖ ↔ ρ.im = 0 :=
  GKSharp.Sec3Geom.thmA_step4_proved hp hp2 hρ

/-- Remark (real ratios), sec3_nonreal.tex l.76-78: "For real ρ = λ the configuration is symmetric about the
real axis and M̃′(t₁) = 0" (data of `thmA_step1` at `ρ = λ ≠ 1`; `t₁` after the relabeling). -/
theorem thmA_remark_real {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) {lam : ℝ} (hl : lam ≠ 1) :
    let C := gk p lam
    let c := diskCentre C lam
    let r := Real.sqrt (‖c‖ ^ 2 - diskRadiusSq C lam)
    let t₁ := Complex.arg c - windowHalfAngle C lam
    let t₂ := Complex.arg c + windowHalfAngle C lam
    let μ := fun t : ℝ => obstacleG p C lam ((r : ℂ) * unitPoint t) / r ^ (p / 2)
    ∀ s s' : ℝ, (s = t₁ ∧ s' = t₂ ∨ s = t₂ ∧ s' = t₁) → (∃ k : ℤ, s' = s + 2 * Real.pi / p + 2 * Real.pi * k) →
      HasDerivAt (fun t => μ t + μ (t + 2 * Real.pi / p)) 0 s :=
  GKSharp.Sec3Geom.thmA_remark_real_proved hp hp2 hl

/-- The arch inequality, sec3_nonreal.tex l.15-16: "A 2π-periodic q-subtrigonometric function φ satisfies the arch
inequality φ(t) + φ(t + π/q) ≥ 0 for all t [HKV, Proposition 3.4(1)] (it is also Lemma 2.3 with s = π/(2q))". (`QSubtrig`
includes 2π-periodicity; Lemma 2.3 (label chord), sec2_obstacle.tex l.106-108, allows every `0 < s ≤ π/q`. The range `q > 1/2`
is the standing `q = p/2` (P019_paper.tex l.58) with the section's `p > 1`, sec3_nonreal.tex l.11.) -/
theorem sec3_arch {q : ℝ} (hq : 1 / 2 < q) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) (t : ℝ) :
    0 ≤ φ t + φ (t + Real.pi / q) :=
  GKSharp.Sec3Geom.sec3_arch_given @slice_O30 hq hφ t

/-- (3.1), sec3_nonreal.tex l.16-17: "With Theorem 2.2 this gives the arch test: for every C > max(1, |ρ|),
m_C(t₁) + m_C(t₁ + 2π/p) < 0 for some t₁ ⟹ ‖P₊ + ρP₋‖_p > C". (`hC` stays: `obstacle` is a real `sInf`.) -/
theorem eq_3_2 {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) (ρ : ℂ)
    {C : ℝ} (hC : max 1 ‖ρ‖ < C)
    (h : ∃ t₁ : ℝ, obstacle p C ρ t₁ + obstacle p C ρ (t₁ + 2 * Real.pi / p) < 0) :
    C < pencilNorm P ρ :=
  GKSharp.Sec3Geom.eq_3_2_given @slice_O18 @sec3_arch hp P ρ hC h

/-- Theorem 3.2 (label A), sec3_nonreal.tex l.44-46 (Section 3: `1 < p`): "Let p ≠ 2 and ρ ∈ ℂ ∖ ℝ. Then
‖P₊ + ρP₋‖_p > GK_p(ρ)". -/
theorem thm_A {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p ≠ 2)
    (P : RieszProjection p) {ρ : ℂ} (hρ : ρ.im ≠ 0) : gk p ρ < pencilNorm P ρ :=
  GKSharp.Sec3Geom.thm_A_given @eq_3_2 hp hp2 P hρ

end SectionThreeComplete


section MonotoneCurveRows

/-- sec5d_monotone.tex l.36: "From cot x − cot y = sin(y − x)/(sin x sin y)". -/
theorem sec5d_cot_difference (x y : ℝ) (hx : Real.sin x ≠ 0) (hy : Real.sin y ≠ 0) :
    Real.cot x - Real.cot y = Real.sin (y - x) / (Real.sin x * Real.sin y) := by
  apply GKSharp.sec5d_cot_difference_proved <;> assumption

/-- sec5d_monotone.tex l.38: "Finally, cos(a − b) + cos(a + b) = 2 cos a cos b and cos(a − b) − cos(a + b) =
2 sin a sin b are positive". -/
theorem sec5d_cos_sum_difference (a b : ℝ) (hab : 0 < b ∧ b < a ∧ a < Real.pi / 2) :
    Real.cos (a - b) + Real.cos (a + b) = 2 * Real.cos a * Real.cos b ∧
    Real.cos (a - b) - Real.cos (a + b) = 2 * Real.sin a * Real.sin b ∧
    0 < Real.cos (a - b) + Real.cos (a + b) ∧
    0 < Real.cos (a - b) - Real.cos (a + b) := by
  apply GKSharp.sec5d_cos_sum_difference_proved <;> assumption

/-- sec5d_monotone.tex l.30 (sign formula): "and the denominator is positive"; l.38-39: "cos(a − b) − X cos(a + b) > 0
for |X| ≤ 1". -/
theorem sec5d_denominator_positive {p θ X : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) (hX : |X| ≤ 1) :
    0 < Real.cos ((1 - p / 2) * θ) - X * Real.cos (p / 2 * θ) ∧
    0 < monoSignDenominator p θ X := by
  apply GKSharp.sec5d_denominator_positive_proved <;> assumption

/-- sec5d_monotone.tex l.40: "the derivative of sin(γ−b)/sin(γ+b) with respect to γ is sin(2b)/sin²(γ+b) > 0". -/
theorem sec5d_gamma_ratio_derivative {p θ g : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2) :
    HasDerivAt (fun x => Real.sin (x - (p - 1) * (θ / 2)) / Real.sin (x + (p - 1) * (θ / 2)))
      (Real.sin ((p - 1) * θ) / Real.sin (g + (p - 1) * (θ / 2)) ^ 2) g ∧
    0 < Real.sin ((p - 1) * θ) / Real.sin (g + (p - 1) * (θ / 2)) ^ 2 := by
  apply GKSharp.sec5d_gamma_ratio_derivative_proved <;> assumption

/-- sec5d_monotone.tex l.57: "Let σ = √(1 − X²) sin ω and ν = c_q − X d_ω. Since cos(2γ ∓ ω) = X d_ω ± σ". -/
theorem sec5d_sigma_cosine {p θ g : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2) :
    Real.cos (2 * g - (1 - p / 2) * θ) =
      Real.cos (2 * g) * Real.cos ((1 - p / 2) * θ) + monoSigma p θ g ∧
    Real.cos (2 * g + (1 - p / 2) * θ) =
      Real.cos (2 * g) * Real.cos ((1 - p / 2) * θ) - monoSigma p θ g := by
  apply GKSharp.sec5d_sigma_cosine_proved <;> assumption

/-- sec5d_monotone.tex l.71-72 (proof of Lemma 5.9 (label Bneg), −1 < λ ≤ 0): "The right side in Lemma ... is ≤ 0";
"ω < mω < π − ω" (the row's variable `α` is ω). -/
theorem sec5d_B_angle_threshold {m α lam : ℝ} (hm : 1 < m)
    (hα : 0 < α ∧ α < Real.pi / (m + 1)) (hl : -1 < lam) (hl0 : lam ≤ 0) :
    α < m * α ∧ m * α < Real.pi - α ∧
    4 * (m ^ 2 - 1) * lam / (1 + lam) ^ 2 ≤ 0 := by
  apply GKSharp.sec5d_B_angle_threshold_proved <;> assumption

/-- sec5d_monotone.tex l.16-17: "the radius r = R(θ) ∈ (0,1) is written as r = sin(γ − b)/sin(γ + b) with
γ ∈ (b, π/2)" (and γ is unique there). -/
theorem sec5d_gamma_spec {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (p - 1) * (θ / 2) < curveGamma p lam θ ∧ curveGamma p lam θ < Real.pi / 2 ∧
    curveR p lam θ = Real.sin (curveGamma p lam θ - (p - 1) * (θ / 2)) /
      Real.sin (curveGamma p lam θ + (p - 1) * (θ / 2)) ∧
    ∀ g ∈ Set.Ioo ((p - 1) * (θ / 2)) (Real.pi / 2),
      curveR p lam θ = Real.sin (g - (p - 1) * (θ / 2)) / Real.sin (g + (p - 1) * (θ / 2)) →
        g = curveGamma p lam θ := by
  apply GKSharp.sec5d_gamma_spec_proved <;> assumption

/-- sec5d_monotone.tex l.20: "Hence λ < 0 for γ > a, λ = 0 at γ = a, and λ > 0 for γ < a". -/
theorem sec5d_lambda_gamma_sign {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (lam < 0 ↔ θ / 2 < curveGamma p lam θ) ∧
    (lam = 0 ↔ curveGamma p lam θ = θ / 2) ∧
    (0 < lam ↔ curveGamma p lam θ < θ / 2) := by
  apply GKSharp.sec5d_lambda_gamma_sign_proved <;> assumption

/-- sec5d_monotone.tex l.57-59: "(5.9) reads μ = (ν − σ)/(ν + σ), i.e. ν = ((1 − λ)/(1 + λ)) σ; here
ν + σ = 2 sin(γ + a) sin(γ − b) > 0". -/
theorem sec5d_nu_sigma_relation {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    -lam = (monoNu p θ (curveGamma p lam θ) - monoSigma p θ (curveGamma p lam θ)) /
      (monoNu p θ (curveGamma p lam θ) + monoSigma p θ (curveGamma p lam θ)) ∧
    monoNu p θ (curveGamma p lam θ) = (1 - lam) / (1 + lam) * monoSigma p θ (curveGamma p lam θ) ∧
    monoNu p θ (curveGamma p lam θ) + monoSigma p θ (curveGamma p lam θ) =
      2 * Real.sin (curveGamma p lam θ + θ / 2) * Real.sin (curveGamma p lam θ - (p - 1) * (θ / 2)) ∧
    0 < monoNu p θ (curveGamma p lam θ) + monoSigma p θ (curveGamma p lam θ) := by
  apply GKSharp.sec5d_nu_sigma_relation_proved <;> assumption

/-- sec5d_monotone.tex l.59-60: "Then c_q² + d_ω² − 2c_q d_ω X = ν² + σ²cot²ω, c_q/d_ω − X = ν/d_ω and W₀ − W = ε sin² 2ω". -/
theorem sec5d_factorization_dictionary {p θ g : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2) :
    Real.cos (p / 2 * θ) ^ 2 + Real.cos ((1 - p / 2) * θ) ^ 2 -
        2 * Real.cos (p / 2 * θ) * Real.cos ((1 - p / 2) * θ) * Real.cos (2 * g) =
      monoNu p θ g ^ 2 + monoSigma p θ g ^ 2 * Real.cot ((1 - p / 2) * θ) ^ 2 ∧
    Real.cos (p / 2 * θ) / Real.cos ((1 - p / 2) * θ) - Real.cos (2 * g) =
      monoNu p θ g / Real.cos ((1 - p / 2) * θ) ∧
    (1 - (p - 1)) ^ 2 * Real.sin θ * Real.sin ((p - 1) * θ) - monoW (p - 1) θ =
      (p - 1) * Real.sin (2 * ((1 - p / 2) * θ)) ^ 2 := by
  apply GKSharp.sec5d_factorization_dictionary_proved <;> assumption

/-- sec5d_monotone.tex l.60-61: "so (5.10) becomes Π(X) = σ²cot²ω/d_ω² [W − 4ε((1−λ)/(1+λ))² sin⁴ω]", with a
positive prefactor. -/
theorem sec5d_Pi_factorization {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ)) =
      monoPiPrefactor p θ (curveGamma p lam θ) *
        (monoW (p - 1) θ - 4 * (p - 1) * ((1 - lam) / (1 + lam)) ^ 2 * Real.sin ((1 - p / 2) * θ) ^ 4) ∧
    0 < monoPiPrefactor p θ (curveGamma p lam θ) := by
  apply GKSharp.sec5d_Pi_factorization_proved <;> assumption

/-- sec5d_monotone.tex l.33: "Let M = log|sin(γ − a)| + log sin(γ + b) − log sin(γ + a) − log sin(γ − b), so the level set
is M = log|μ|" (μ = −λ). -/
theorem sec5d_M_level {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hl0 : lam ≠ 0) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    monoLogM p (θ / 2) (curveGamma p lam θ) = Real.log |lam| := by
  apply GKSharp.sec5d_M_level_proved <;> assumption

/-- sec5d_monotone.tex l.36-37 (proof of the sign formula): "M_γ = sin(a − b)[sin(γ + a) sin(γ + b) +
sin(γ − a) sin(γ − b)]/S = sin(a − b)[cos(a−b) − X cos(a+b)]/S". -/
theorem sec5d_M_gamma_formula {p θ g : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2) (hga : g ≠ θ / 2) :
    HasDerivAt (monoLogM p (θ / 2))
      (Real.sin ((1 - p / 2) * θ) *
        (Real.cos ((1 - p / 2) * θ) - Real.cos (2 * g) * Real.cos (p / 2 * θ)) /
        monoS p (θ / 2) g) g ∧
    deriv (monoLogM p (θ / 2)) g = Real.sin ((1 - p / 2) * θ) *
      (Real.sin (g + θ / 2) * Real.sin (g + (p - 1) * (θ / 2)) +
        Real.sin (g - θ / 2) * Real.sin (g - (p - 1) * (θ / 2))) / monoS p (θ / 2) g := by
  apply GKSharp.sec5d_M_gamma_formula_proved <;> assumption

/-- sec5d_monotone.tex l.63-64: "Since 1 − (1−λ)²/(1+λ)² = 4λ/(1+λ)², the sign of Π is the sign of
4(m²−1)λ/(1+λ)² − Ψ_m(ω)". -/
theorem sec5d_Pi_Psi_sign {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    1 - (1 - lam) ^ 2 / (1 + lam) ^ 2 = 4 * lam / (1 + lam) ^ 2 ∧
    SignType.sign (monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ))) =
      SignType.sign (4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 -
        monoPsi (p / (2 - p)) ((1 - p / 2) * θ)) := by
  apply GKSharp.sec5d_Pi_Psi_sign_proved <;> assumption

/-- sec5d_monotone.tex l.20-21: "Inserting them [the three identities of l.20] in the second expression of (5.7) for K_f
gives K_f = 2(1 + μ) exp L(a, γ)" (μ = −λ,
a = θ/2); in particular K_f > 0. -/
theorem sec5d_Kf_log_form {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    curveKf p lam θ = 2 * (1 - lam) * Real.exp (monoLogL p (θ / 2) (curveGamma p lam θ)) ∧
    0 < curveKf p lam θ := by
  apply GKSharp.sec5d_Kf_log_form_proved <;> assumption

end MonotoneCurveRows


section InverseGradientsAndScalarDuality

open Set GKSharp.Threshold GKSharp.ComputerChecked

/-- (5.3) second form and l.39-40, sec5_sharp_inequality.tex l.37-42 (`w = ρe^{iφ}`, `θ = arg Q`; `z` is
the inverse of the Möbius map, `z = (1 − w)/(w − λ)`): "z = re^{−iθ} by (5.1)"; "f_ρ′(φ) = −q(1−λ)|Q|^{q−1}/|1+z|² ·
D(θ, r)"; "f_ρ′(φ) = 0 if and only if w = τv with τ = ρ/|v| > 0, if and only if D(θ, r) = 0". -/
theorem eq_5_3_second {p lam ρ φ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hρ : 0 < ρ) (hφ0 : 0 < φ) (hφ : φ < Real.pi) :
    let f := fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)
    let w : ℂ := (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
    let θ := Complex.arg (mobQ lam w)
    let z : ℂ := (1 - w) / (w - lam)
    z = (‖z‖ : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I) ∧
    HasDerivAt f (-(p / 2) * (1 - lam) * ‖mobQ lam w‖ ^ (p / 2 - 1) / ‖1 + z‖ ^ 2 * curveD p lam θ ‖z‖) φ ∧
    (deriv f φ = 0 ↔ w = ((ρ / ‖curveV p lam θ‖ : ℝ) : ℂ) * curveV p lam θ) ∧
    (deriv f φ = 0 ↔ curveD p lam θ ‖z‖ = 0) := by
  apply GKSharp.Proofs.InverseCritical.eq_5_3_second_proved <;> assumption

/-- sec5_sharp_inequality.tex l.101-102 (`Im w > 0`, `θ = arg Q(w)`, `ω = (1−q)θ`, `v = e^{iω} + λe^{−iω}`;
real gradients on `ℂ = ℝ²` as vectors, `dF(h) = ⟪∇F, h⟫_ℝ`): "(∂ₓ + i∂ᵧ) Re Q^q = q[Q^{q−1}(λ − w) +
conj(Q^{q−1})(1 − w)] = q|Q|^{q−1}(v − 2w cos ω), and the gradient of |w|^p is p|w|^{p−2}w". -/
theorem sec5_grad_parts {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    {w : ℂ} (hw : 0 < w.im) :
    let θ := Complex.arg (mobQ lam w)
    HasFDerivAt (fun u : ℂ => reQPow (mobQ lam u) (p / 2))
      (innerSL ℝ ((((p / 2) * ‖mobQ lam w‖ ^ (p / 2 - 1) : ℝ) : ℂ) *
        (curveV p lam θ - 2 * w * ((Real.cos ((1 - p / 2) * θ) : ℝ) : ℂ))) : ℂ →L[ℝ] ℝ) w ∧
    HasFDerivAt (fun u : ℂ => ‖u‖ ^ p) (innerSL ℝ (((p * ‖w‖ ^ (p - 2) : ℝ) : ℂ) * w) : ℂ →L[ℝ] ℝ) w := by
  apply GKSharp.Proofs.RealGradients.sec5_grad_parts_proved <;> assumption

/-- sec5_sharp_inequality.tex l.56-57: "So the critical points of f_ρ in (0, π) are the points w(θ) with
ρ(θ) = ρ and, for λ > 0, their inversion images λ/w̄(θ) with λ/ρ(θ) = ρ" (the moduli conditions follow from the
equalities of points). -/
theorem sec5_critical_points {p lam ρ φ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hρ : 0 < ρ) (hφ0 : 0 < φ) (hφ : φ < Real.pi) :
    deriv (fun x : ℝ => reQPow (mobQ lam ((ρ : ℂ) * Complex.exp ((x : ℂ) * Complex.I))) (p / 2)) φ = 0 ↔
      (∃ θ ∈ Set.Ioo 0 Real.pi, (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = mobW lam (curveZ p lam θ)) ∨
      (0 < lam ∧ ∃ θ ∈ Set.Ioo 0 Real.pi,
        (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) = (lam : ℂ) / conj (mobW lam (curveZ p lam θ))) := by
  apply GKSharp.Proofs.CriticalClassification.sec5_critical_points_proved <;> assumption

/-- sec4b_failure.tex l.15: "for p > 2 the statements below hold with p′ in place of p, by duality
(Section 1)" (the row: the quantities of this subsection, the left side of (4.2), F, T and λ_loc, are unchanged
under p ↔ p′; Theorem 4.4 for p > 2 is the row `sec4_thm_L_dual`). -/
theorem sec4_conditions_dual (p lam : ℝ) (hp : 1 < p) :
    localTest (dual p) lam = localTest p lam ∧ localF (dual p) = localF p ∧
      localD2 (dual p) = localD2 p ∧ lambdaLoc (dual p) = lambdaLoc p := by
  apply GKSharp.sec4_conditions_dual_proved <;> assumption

/-- Lemma 4.6 (label Pc), sec4b_failure.tex l.93-94: "Some λ ∈ (0, 1) satisfies (4.2) if and only if
F(p) := pp′ − 4(1 + cos²(π/p)) > 0, that is, if and only if p < p_c or p > p_c′". -/
theorem sec4_lemma_Pc_full (hc : CheckLocalF) (p : ℝ) (hp : 1 < p) :
    ((∃ lam ∈ Ioo (0 : ℝ) 1, 1 < localTest p lam) ↔ 0 < localF p) ∧
      (0 < localF p ↔ (p < pc ∨ dual pc < p)) := by
  apply GKSharp.sec4_lemma_Pc_full_proved <;> assumption

end InverseGradientsAndScalarDuality


section MonotonicitySeriesLeaves

/-- sec5d_monotone.tex l.81-84: "by sin y = y∏ₙ(1 − y²/(nπ)²) and log(1−u) = −Σₖ uᵏ/k, with ξ_n = θ/(nπ) ∈ (0,1),"
"log ε sin²((1−ε)θ)/((1−ε)² sin θ sin(εθ)) = Σ_{n≥1} Σ_{k≥1} ξ_n^{2k}/k [1 + ε^{2k} − 2(1−ε)^{2k}]" (both summation levels summable). -/
theorem sec5d_Bplus_double_series {eps θ : ℝ} (he : 2 - Real.sqrt 3 ≤ eps) (he1 : eps < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (∀ n : ℕ, Summable (monoDoubleTerm eps θ n)) ∧
    Summable (fun n : ℕ => ∑' k : ℕ, monoDoubleTerm eps θ n k) ∧
    monoLogRatio eps θ = ∑' n : ℕ, ∑' k : ℕ, monoDoubleTerm eps θ n k := by
  apply GKSharp.sec5d_Bplus_double_series_proved <;> assumption

/-- sec5d_monotone.tex l.85-86: "The k = 1 bracket is −(ε² − 4ε + 1) ≥ 0 for ε ≥ 2 − √3; for k ≥ 2,
2(1−ε)^{2k} ≤ 2(4 − 2√3)² < 0.58. So the logarithm is positive and W < 0." -/
theorem sec5d_Bplus_W_negative {p θ : ℝ} (hp1 : 3 - Real.sqrt 3 ≤ p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    0 < monoLogRatio (p - 1) θ ∧ monoW (p - 1) θ < 0 := by
  apply GKSharp.sec5d_Bplus_W_negative_proved <;> assumption

/-- sec5d_monotone.tex l.80-81: "it suffices to show that Ψ_m ≥ m² − 1, that is, W ≤ 0 on (0, π). All of θ, εθ, (1−ε)θ
lie in (0, π)". -/
theorem sec5d_Bplus_scalar_criterion {p θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (monoPsi (p / (2 - p)) ((1 - p / 2) * θ) ≥ (p / (2 - p)) ^ 2 - 1 ↔ monoW (p - 1) θ ≤ 0) ∧
    (p - 1) * θ ∈ Set.Ioo 0 Real.pi ∧ (1 - (p - 1)) * θ ∈ Set.Ioo 0 Real.pi := by
  apply GKSharp.sec5d_Bplus_scalar_criterion_proved <;> assumption

/-- sec5d_monotone.tex l.95: "Let t = sin²ω ... Since (dt/dω)² = 4t(1−t) and d²t/dω² = 2 − 4t" (the row's variable `α` is ω). -/
theorem sec5d_t_derivatives (α : ℝ) :
    HasDerivAt (fun x => Real.sin x ^ 2) (2 * Real.sin α * Real.cos α) α ∧
    (2 * Real.sin α * Real.cos α) ^ 2 = 4 * Real.sin α ^ 2 * (1 - Real.sin α ^ 2) ∧
    deriv (deriv fun x => Real.sin x ^ 2) α = 2 - 4 * Real.sin α ^ 2 := by
  apply GKSharp.sec5d_t_derivatives_proved <;> assumption

/-- sec5d_monotone.tex l.99-101: "Writing Y_m = Σ_{n≥0} yₙtⁿ gives y₀ = 1 and y_{n+1} = (n² − m²)/((n+1)(n+½)) yₙ"
(the recurrence and the initial coefficient as identities of the defined coefficients). -/
theorem sec5d_coefficient_recurrence (m : ℝ) :
    monoCoeffA m 0 = 1 ∧ ∀ n : ℕ,
      monoCoeffA m (n + 1) = ((n : ℝ) ^ 2 - m ^ 2) /
        (((n : ℝ) + 1) * ((n : ℝ) + 1 / 2)) * monoCoeffA m n := by
  apply GKSharp.sec5d_coefficient_recurrence_proved <;> assumption

/-- sec5d_monotone.tex l.109-110: "β_n = 2^{2n+3} m²(m² − 1) ∏_{j=2}^{n+1}(j² − m²)/(2n+4)!"; "For 1 < m < 2 every factor is
positive". -/
theorem sec5d_beta_positive {m : ℝ} (hm : 1 < m) (hm2 : m < 2) (n : ℕ) :
    0 < monoBeta m n := by
  apply GKSharp.sec5d_beta_positive_proved <;> assumption

/-- sec5d_monotone.tex l.110-111: "t increases on (0, π/2) ⊃ (0, π/(m+1))". -/
theorem sec5d_sin_square_strictMono :
    StrictMonoOn (fun α : ℝ => Real.sin α ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
  apply GKSharp.sec5d_sin_square_strictMono_proved <;> assumption

/-- sec5d_monotone.tex l.112-114: "At ω_e = π/(m+1), sin(mω_e) = sin ω_e, so
Ψ_m(ω_e) = (m² − 1)/sin²ω_e > m² − 1 > 4(m² − 1)λ/(1+λ)²". -/
theorem sec5d_U_endpoint {m lam : ℝ} (hm : 1 < m) (hm2 : m < 2) (hl : 0 < lam) (hl1 : lam < 1) :
    Real.sin (m * (Real.pi / (m + 1))) = Real.sin (Real.pi / (m + 1)) ∧
    monoPsi m (Real.pi / (m + 1)) = (m ^ 2 - 1) / Real.sin (Real.pi / (m + 1)) ^ 2 ∧
    m ^ 2 - 1 < monoPsi m (Real.pi / (m + 1)) ∧
    4 * (m ^ 2 - 1) * lam / (1 + lam) ^ 2 < m ^ 2 - 1 := by
  apply GKSharp.sec5d_U_endpoint_proved <;> assumption

/-- sec5d_monotone.tex l.95: "Let t = sin²ω and Y_m(t) = cos(2mω)" (on the printed ω interval; the row's variable `α` is ω). -/
theorem sec5d_Y_coordinate (m : ℝ) {α : ℝ} (hα : 0 < α) (hαπ : α < Real.pi / 2) :
    monoY m (Real.sin α ^ 2) = Real.cos (2 * m * α) := by
  apply GKSharp.sec5d_Y_coordinate_proved <;> assumption

/-- sec5d_monotone.tex l.95-97: "the equation d²Y_m/dω² + 4m²Y_m = 0 becomes t(1−t)Y_m″ + (½ − t)Y_m′ + m²Y_m = 0". -/
theorem sec5d_Y_ode (m : ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    t * (1 - t) * deriv (deriv (monoY m)) t + (1 / 2 - t) * deriv (monoY m) t +
      m ^ 2 * monoY m t = 0 := by
  apply GKSharp.sec5d_Y_ode_proved <;> assumption

/-- sec5d_monotone.tex l.103: "The resulting series has radius of convergence at least 1" (with absolute summability). -/
theorem sec5d_Y_series_convergence (m : ℝ) {t : ℝ} (ht : |t| < 1) :
    Summable (fun n : ℕ => |monoCoeffA m n| * |t| ^ n) := by
  apply GKSharp.sec5d_Y_series_convergence_proved <;> assumption

/-- sec5d_monotone.tex l.99-103: "Writing Y_m = Σ_{n≥0} yₙtⁿ gives y₀ = 1 and" the recurrence; "The resulting series has
radius of convergence at least 1" (Y equals the series on the actual t interval). -/
theorem sec5d_Y_series (m : ℝ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    HasSum (fun n : ℕ => monoCoeffA m n * t ^ n) (monoY m t) := by
  apply GKSharp.sec5d_Y_series_proved <;> assumption

/-- sec5d_monotone.tex l.103-105: "This gives sin²(mω) = ½(1 − Y_m(t)) = Σ_{n≥1}
2^{2n−1} m² ∏_{j=1}^{n−1}(j² − m²)/(2n)! tⁿ". -/
theorem sec5d_sine_square_series (m : ℝ) {α : ℝ} (hα : 0 < α) (hαπ : α < Real.pi / 2) :
    HasSum (fun n : ℕ => monoSinCoeff m (n + 1) * (Real.sin α ^ 2) ^ (n + 1))
      (Real.sin (m * α) ^ 2) := by
  apply GKSharp.sec5d_sine_square_series_proved <;> assumption

/-- sec5d_monotone.tex l.107-109: "Consequently Ψ_m(ω) = (m²t − sin²(mω))/t² = Σ_{n≥0} βₙtⁿ" (with convergence). -/
theorem sec5d_Psi_beta_series {m α : ℝ} (hm : 1 < m) (hm2 : m < 2)
    (hα : 0 < α) (hαπ : α < Real.pi / 2) :
    HasSum (fun n : ℕ => monoBeta m n * (Real.sin α ^ 2) ^ n) (monoPsi m α) := by
  apply GKSharp.sec5d_Psi_beta_series_proved <;> assumption

end MonotonicitySeriesLeaves


section CompleteContactAndCriterion
open Set Real GKSharp.Threshold
open scoped ContDiff

/-- short_v3.70/sec4a_criterion.tex:57–62. “The second equivalence is the definition of $m_C$ after $z \mapsto 1/z$”. -/
theorem obstacle_cos_iff_critD (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) :
    (∀ t ∈ Icc (-Real.pi) Real.pi,
      kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t) ↔
    (∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) := by
  apply GKSharp.obstacle_cos_iff_critD_proved <;> assumption

/-- short_v3.70/sec4a_criterion.tex:69. “By Section~4.1, $m_{\GK}$ is differentiable at $\theta_0$ with $m'_{\GK}(\theta_0)=-Kq$.” The row is stronger: it also gives smoothness near θ₀. Lean takes the derivative by the Section 4.1 route (q15_sec2_envelope_route, slice_O35). -/
theorem obstacle_smooth_contact (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) :
    ∃ eps > 0, ContDiffOn ℝ ∞ (Threshold.obstacle p lam)
      (Ioo (theta p - eps) (theta p + eps)) ∧
      deriv (Threshold.obstacle p lam) (theta p) = -q p * kConst p lam := by
  apply GKSharp.obstacle_smooth_contact_proved <;> assumption

/-- short_v3.70/sec4a_criterion.tex:70–71. “hence $A_{\varphi} = K$ and $\varphi'(\theta_0^+) = -Kq$.” -/
theorem sec4_angular_tangency (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) (ff : ℝ → ℝ) (hf : QSubtrig (q p) ff)
    (hminor : ∀ t, ff t ≤ Threshold.obstacle p lam t) (aa : ℝ)
    (harch : ∀ t ∈ Icc (-theta p) (theta p), ff t = aa * Real.cos (q p * t)) :
    aa = kConst p lam ∧
      HasDerivWithinAt ff (-(kConst p lam) * q p) (Ici (theta p)) (theta p) := by
  apply GKSharp.sec4_angular_tangency_proved <;> assumption

/-- short_v3.70/sec4a_criterion.tex:56–59. “put $C=\GK_p(\lambda)$. Then $\|\Pp + \lambda \Pm\|_p = C$ if and only if $m_{\GK}(t) \ge K \cos(q|t|)$ for all $|t| \le \pi$”, with the second equivalence to nonnegative $\mathcal{D}_C$ on $\mathbb{C}$. -/
theorem sec4_prop_Q (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) :
    1 < p → p < 2 → ∀ lam ∈ Ico (-1 : ℝ) 1,
      (pencilNorm P lam = gk p lam ↔
        ∀ t ∈ Icc (-Real.pi) Real.pi,
          kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t) ∧
      (pencilNorm P lam = gk p lam ↔
        ∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) := by
  apply GKSharp.sec4_prop_Q_proved <;> assumption

/-- short_v3.70/P019_paper.tex:54–55. “Gohberg and Krupnik proved the lower bound $\|\alpha\Pp+\beta\Pm\|_p\ \ge\ \GK_p(\alpha,\beta)$” (here α = 1, β = ρ). Route R11 uses the proved HKV criterion and the existing HV2000 input for conjugate-exponent transport. -/
theorem slice_O04 {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) (ρ : ℂ) :
    gk p ρ ≤ pencilNorm P ρ := by
  apply GKSharp.slice_O04_proved <;> assumption

/-- short_v3.70/sec4a_criterion.tex:21–23, Lemma 4.1 (label E). “$m_C(\pm\theta_0) \ge 0$ if and only if $C \ge \GK_p(\lambda)$”; at equality the zero is attained only at the stated contact radius. -/
theorem slice_O33 {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p < 2) (C lam : ℝ) (hC : 1 < C)
    (hlam : -1 ≤ lam ∧ lam < 1) :
    (0 ≤ obstacle p C (lam : ℂ) (Real.pi / p) ↔ gk p (lam : ℂ) ≤ C) ∧
    (0 ≤ obstacle p C (lam : ℂ) (-(Real.pi / p)) ↔ gk p (lam : ℂ) ≤ C) ∧
    obstacle p (gk p (lam : ℂ)) (lam : ℂ) (Real.pi / p) = 0 ∧
    obstacle p (gk p (lam : ℂ)) (lam : ℂ) (-(Real.pi / p)) = 0 ∧
    ∀ r : ℝ, 0 < r →
      (obstacleG p (gk p (lam : ℂ)) (lam : ℂ) ((r : ℂ) * unitPoint (Real.pi / p)) = 0 ↔
        r = contactRadius p lam) ∧
      (obstacleG p (gk p (lam : ℂ)) (lam : ℂ) ((r : ℂ) * unitPoint (-(Real.pi / p))) = 0 ↔
        r = contactRadius p lam) := by
  apply GKSharp.slice_O33_proved <;> assumption

/-- short_v3.70/sec4a_criterion.tex:37–38. “with $y_*=\log r_*$ we show that $K=-q^{-1}\partial_t\Gamma_C(y_*,\theta_0)=-m_C'(\theta_0)/q$.” The envelope identity is $K=-m_C'(\theta_0)/q$. -/
theorem slice_O35 {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (hp2 : p < 2) (lam : ℝ) (hlam : -1 ≤ lam ∧ lam < 1) :
    DifferentiableAt ℝ (obstacle p (gk p (lam : ℂ)) (lam : ℂ)) (Real.pi / p) ∧
    DifferentiableAt ℝ (fun t => gamma p (gk p (lam : ℂ)) (lam : ℂ)
      (log (contactRadius p lam)) t) (Real.pi / p) ∧
    kConst p lam = -(deriv (fun t => gamma p (gk p (lam : ℂ)) (lam : ℂ)
      (log (contactRadius p lam)) t) (Real.pi / p)) / (p / 2) ∧
    kConst p lam = -(deriv (obstacle p (gk p (lam : ℂ)) (lam : ℂ)) (Real.pi / p)) / (p / 2) := by
  apply GKSharp.slice_O35_proved <;> assumption

end CompleteContactAndCriterion

section CompleteOneVariableAndMonotonicity
open Set Real
open scoped ContDiff

/-- short_v3.70/sec5d_monotone.tex:35. "this gives $2\sin u_1\sin u_2\,\mathcal ES=\Pi(X)$". -/
theorem sec5d_E_identity {p θ g : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi)
    (hg : (p - 1) * (θ / 2) < g ∧ g < Real.pi / 2) (hga : g ≠ θ / 2) :
    2 * Real.sin θ * Real.sin ((p - 1) * θ) * monoE p (θ / 2) g * monoS p (θ / 2) g =
      monoPi (p - 1) θ (Real.cos (2 * g)) := by
  apply GKSharp.sec5d_E_identity_proved <;> assumption

/-- short_v3.70/sec5d_monotone.tex:39. "The explicit root $R(\theta)$ in Section~5.1 is real-analytic in $\lambda$ near zero, and $K_f$ is positive and real-analytic there". -/
theorem sec5d_lambda_zero_analytic {p θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    AnalyticAt ℝ (fun lam => curveR p lam θ) 0 ∧
    AnalyticAt ℝ (fun lam => curveKf p lam θ) 0 ∧ 0 < curveKf p 0 θ := by
  apply GKSharp.sec5d_lambda_zero_analytic_proved <;> assumption

/-- short_v3.70/sec5d_monotone.tex:40–41. "The coordinate $\gamma$ also varies smoothly"; "both sides of the formula in Lemma~5.7 extend continuously to $\lambda=0$". -/
theorem sec5d_lambda_zero_continuity {p θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    ContDiffAt ℝ ∞ (fun lam => curveGamma p lam θ) 0 ∧
    ContinuousAt (fun lam => deriv (fun a => Real.log (curveKf p lam (2 * a))) (θ / 2)) 0 ∧
    ContinuousAt (fun lam => monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ)) /
      monoSignDenominator p θ (Real.cos (2 * curveGamma p lam θ))) 0 := by
  apply GKSharp.sec5d_lambda_zero_continuity_proved <;> assumption

/-- short_v3.70/sec5d_monotone.tex:34. "$d\log K_f/da = \mathcal E/M_\gamma$ with $\mathcal E = L_a M_\gamma - L_\gamma M_a$". -/
theorem sec5d_level_derivative {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hl0 : lam ≠ 0) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    deriv (monoLogM p (θ / 2)) (curveGamma p lam θ) ≠ 0 ∧
    HasDerivAt (fun a => Real.log (curveKf p lam (2 * a)))
      (monoE p (θ / 2) (curveGamma p lam θ) /
        deriv (monoLogM p (θ / 2)) (curveGamma p lam θ)) (θ / 2) := by
  apply GKSharp.sec5d_level_derivative_proved <;> assumption

/-- short_v3.70/sec5d_monotone.tex:27–30, Lemma 5.7 (label signformula). "and the denominator is positive", with the displayed actual logarithmic derivative. -/
theorem lemma_signformula {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    HasDerivAt (fun a => Real.log (curveKf p lam (2 * a)))
      (monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ)) /
        monoSignDenominator p θ (Real.cos (2 * curveGamma p lam θ))) (θ / 2) ∧
    0 < monoSignDenominator p θ (Real.cos (2 * curveGamma p lam θ)) := by
  apply GKSharp.lemma_signformula_proved <;> assumption

/-- short_v3.70/sec5d_monotone.tex:49–51, Lemma 5.8 (label onevar). "$K_f$ increases at $\theta$ if and only if" the displayed strict Psi inequality. -/
theorem lemma_onevar {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    DifferentiableAt ℝ (curveKf p lam) θ ∧
    SignType.sign (deriv (curveKf p lam) θ) =
      SignType.sign (4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 -
        monoPsi (p / (2 - p)) ((1 - p / 2) * θ)) := by
  apply GKSharp.lemma_onevar_proved <;> assumption

/-- short_v3.70/sec5d_monotone.tex:30. "Hence $K_f$ increases exactly where $\Pi(X) > 0$." -/
theorem sec5d_Pi_increase_iff {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (0 < deriv (curveKf p lam) θ ↔ 0 < monoPi (p - 1) θ (Real.cos (2 * curveGamma p lam θ))) := by
  apply GKSharp.sec5d_Pi_increase_iff_proved <;> assumption

/-- short_v3.70/sec5d_monotone.tex:50–51. "$K_f$ increases at $\theta$ if and only if" the displayed Psi threshold inequality. -/
theorem sec5d_onevar_increase_iff {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (0 < deriv (curveKf p lam) θ ↔ monoPsi (p / (2 - p)) ((1 - p / 2) * θ) <
      4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2) := by
  apply GKSharp.sec5d_onevar_increase_iff_proved <;> assumption

/-- short_v3.70/sec5d_monotone.tex:67–68, Lemma 5.9 (label Bneg). "For every $1 < p < 2$ and $\lambda \in (-1, 0]$, $K_f$ is strictly decreasing on $(0, \pi)$." -/
theorem lemma_B {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 < lam) (hl0 : lam ≤ 0) :
    StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) := by
  apply GKSharp.lemma_B_proved @GKSharp.lemma_onevar_proved <;> assumption

/-- short_v3.70/sec5d_monotone.tex:76–77, Lemma 5.10 (label Bplus). The printed threshold implies "$K_f$ is strictly decreasing on $(0,\pi)$". -/
theorem lemma_Bplus {p lam : ℝ} (hp1 : 3 - Real.sqrt 3 ≤ p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) := by
  apply GKSharp.lemma_Bplus_proved @GKSharp.lemma_onevar_proved <;> assumption

/-- short_v3.70/sec5d_monotone.tex:90–92, Lemma 5.11 (label U). "$\Psi_m$ is strictly increasing on $(0, \pi/2)$"; "$K_f$ is either strictly decreasing" or has the stated single turning point. -/
theorem lemma_U {p : ℝ} (hp1 : 1 < p) (hp2 : p < 4 / 3) :
    StrictMonoOn (monoPsi (p / (2 - p))) (Set.Ioo 0 (Real.pi / 2)) ∧
    ∀ lam ∈ Set.Ioo (0 : ℝ) 1, StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) ∨
      ∃ θl ∈ Set.Ioo 0 Real.pi, StrictMonoOn (curveKf p lam) (Set.Ioc 0 θl) ∧
        StrictAntiOn (curveKf p lam) (Set.Ico θl Real.pi) := by
  apply GKSharp.lemma_U_proved @GKSharp.lemma_onevar_proved <;> assumption

/-- short_v3.70/sec5d_monotone.tex:111. "By Lemma~\ref{lem:onevar}, the set on which $K_f$ increases is an initial interval." -/
theorem sec5d_U_initial_interval {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 4 / 3)
    (hl : 0 < lam) (hl1 : lam < 1) :
    ∀ x ∈ Set.Ioo 0 Real.pi, ∀ y ∈ Set.Ioo 0 Real.pi, x < y →
      0 < deriv (curveKf p lam) y → 0 < deriv (curveKf p lam) x := by
  apply GKSharp.sec5d_U_initial_interval_proved @GKSharp.lemma_onevar_proved <;> assumption

/-- short_v3.70/sec5d_monotone.tex:116. "Thus $K_f$ decreases near $\theta=\pi$". -/
theorem sec5d_U_terminal_decrease {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 4 / 3)
    (hl : 0 < lam) (hl1 : lam < 1) :
    ∃ a ∈ Set.Ioo 0 Real.pi, StrictAntiOn (curveKf p lam) (Set.Ioo a Real.pi) := by
  apply GKSharp.sec5d_U_terminal_decrease_proved @GKSharp.lemma_onevar_proved <;> assumption

end CompleteOneVariableAndMonotonicity

section SharpCurveReductionAndC1
open ComplexConjugate Filter Topology Set

/-- short_v3.70; Consequence (E2), sec5_sharp_inequality.tex l.88-94: "ρ(θ) is continuous, injective by (E1), and ρ → ∞
as θ → π (z_θ → −1); so ρ increases strictly from ρ₀ := ρ(0⁺) = (1 + λr₀)/(1 + r₀) ∈ [0, 1) to ∞, and ρ′ > 0"; "If λ > 0,
r₀ ≤ 1 gives ρ₀ ≥ (1+λ)/2 > √λ". -/
theorem sec5_A2 {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    let r0 := curveRoot lam (1 - p / 2) (p / 2)
    let ρ0 := (1 + lam * r0) / (1 + r0)
    ContinuousOn ((fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖)) (Set.Ioo 0 Real.pi) ∧ StrictMonoOn ((fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖)) (Set.Ioo 0 Real.pi) ∧
    Tendsto ((fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖)) (𝓝[<] Real.pi) atTop ∧ Tendsto ((fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖)) (𝓝[>] 0) (𝓝 ρ0) ∧
    0 ≤ ρ0 ∧ ρ0 < 1 ∧
    (∀ θ ∈ Set.Ioo 0 Real.pi, 0 < deriv ((fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖)) θ) ∧
    (0 < lam → (1 + lam) / 2 ≤ ρ0 ∧ Real.sqrt lam < (1 + lam) / 2) := by
  apply GKSharp.sec5_A2_proved <;> assumption

/-- short_v3.70; (E2), the text's own step, sec5_sharp_inequality.tex l.89-90: "ρ(θ) is continuous, injective by
(E1)" (two angles with the same `ρ(θ)` give two critical points of `f_ρ` in `(0, π)`). -/
theorem sec5_A2_injective {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) :
    Set.InjOn ((fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖)) (Set.Ioo 0 Real.pi) := by
  apply GKSharp.A2Injective.sec5_A2_injective_given @GKSharp.Paper.sec5_critical_points <;> assumption

/-- short_v3.70; Consequence (E3), sec5_sharp_inequality.tex l.93-96: "If ρ > ρ₀, f_ρ has exactly one critical point
φ_c ∈ (0, π), at w(θ) with ρ(θ) = ρ; f_ρ′ > 0 on (0, φ_c), f_ρ′ < 0 on (φ_c, π), and max_{[0,π]} f_ρ is attained only
at φ_c. If ρ ≤ ρ₀ (and ρ ≥ √λ when λ > 0), f_ρ is monotone on [0, π] (...), and Q(ρ) − Q(−ρ) = 2(1+λ)ρ ≥ 0
(both real) gives max f_ρ = f_ρ(0), at w = ρ". -/
theorem sec5_A3 {p lam ρ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1) (hρ : 0 < ρ) :
    let r0 := curveRoot lam (1 - p / 2) (p / 2)
    let ρ0 := (1 + lam * r0) / (1 + r0)
    (ρ0 < ρ → ∃ φc ∈ Set.Ioo 0 Real.pi, ∃ θ ∈ Set.Ioo 0 Real.pi,
      (fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖) θ = ρ ∧ (ρ : ℂ) * Complex.exp ((φc : ℂ) * Complex.I) = mobW lam (curveZ p lam θ) ∧
      (∀ φ ∈ Set.Ioo 0 φc, 0 < deriv (fun x => fRho p lam ρ x) φ) ∧
      (∀ φ ∈ Set.Ioo φc Real.pi, deriv (fun x => fRho p lam ρ x) φ < 0) ∧
      ∀ φ ∈ Set.Icc 0 Real.pi, φ ≠ φc → fRho p lam ρ φ < fRho p lam ρ φc) ∧
    (ρ ≤ ρ0 → (0 < lam → Real.sqrt lam ≤ ρ) →
      (MonotoneOn (fun x => fRho p lam ρ x) (Set.Icc 0 Real.pi) ∨
        AntitoneOn (fun x => fRho p lam ρ x) (Set.Icc 0 Real.pi)) ∧
      ∀ φ ∈ Set.Icc 0 Real.pi, fRho p lam ρ φ ≤ fRho p lam ρ 0) := by
  apply GKSharp.sec5_A3_proved <;> assumption

/-- short_v3.70; sec5_sharp_inequality.tex l.102-103: "On the critical curve w = τv, so ∇Φ(w(θ)) = q|Q|^{q−1}(2τ cos ω − 1)
(K − K_f(θ)) v" (real gradient on `ℂ`, `τ = ρ/|v|`, any `C` and `K`). -/
theorem sec5_grad_Phi {p C K lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    let w := mobW lam (curveZ p lam θ)
    let τ := ‖w‖ / ‖curveV p lam θ‖
    HasFDerivAt (mobPhi p C K lam)
      (innerSL ℝ ((((p / 2) * ‖mobQ lam w‖ ^ (p / 2 - 1) * (2 * τ * Real.cos ((1 - p / 2) * θ) - 1) *
        (K - curveKf p lam θ) : ℝ) : ℂ) * curveV p lam θ) : ℂ →L[ℝ] ℝ) w := by
  apply GKSharp.Sec5GradPhi.sec5_grad_Phi_proved <;> assumption

/-- short_v3.70; sec5_sharp_inequality.tex l.106: "Re(v̄ w′) = (ρ²)′/(2τ)" on the critical curve (`w = w(θ)`,
`ρ = ρ(θ)`, `τ = ρ/|v|`). -/
theorem sec5_re_vbar_wprime {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    let τ := (fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖) θ / ‖curveV p lam θ‖
    DifferentiableAt ℝ (fun x => mobW lam (curveZ p lam x)) θ ∧
    (conj (curveV p lam θ) * deriv (fun x => mobW lam (curveZ p lam x)) θ).re =
      deriv (fun x => (fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖) x ^ 2) θ / (2 * τ) := by
  apply GKSharp.Sec5ReVbar.sec5_re_vbar_wprime_proved <;> assumption

/-- short_v3.70; sec5_sharp_inequality.tex l.106-109 (any `C`, `K`: `C^p` is constant): "d/dθ Φ(w(θ)) =
Re(conj(∇Φ) w′) = q|Q|^{q−1}(2τ cos ω − 1)(ρρ′/τ)(K − K_f(θ))", and "by (5.5) and (E2), Λ′(θ) =
c(θ)(K − K_f(θ)) with c(θ) > 0" (`Λ = Φ(w(θ))/(1−λ)^p`; the positive factor is `F/(1−λ)^p`, `F` the factor of (5.8)). -/
theorem eq_5_8 {p C K lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    let w := mobW lam (curveZ p lam θ)
    let τ := ‖w‖ / ‖curveV p lam θ‖
    let F := p / 2 * ‖mobQ lam w‖ ^ (p / 2 - 1) * (2 * τ * Real.cos ((1 - p / 2) * θ) - 1) *
      (‖w‖ * deriv (fun x => ‖mobW lam (curveZ p lam x)‖) θ / τ)
    HasDerivAt (fun x => mobPhi p C K lam (mobW lam (curveZ p lam x))) (F * (K - curveKf p lam θ)) θ ∧ 0 < F ∧
    HasDerivAt (fun x => mobPhi p C K lam (mobW lam (curveZ p lam x)) / (1 - lam) ^ p)
      (F / (1 - lam) ^ p * (K - curveKf p lam θ)) θ ∧ 0 < F / (1 - lam) ^ p := by
  exact GKSharp.Sec5Eq58.eq_5_8_of_rho_deriv_pos hp1 hp2 hl hl1 hθ0 hθ ((GKSharp.sec5_A2_proved hp1 hp2 hl hl1).2.2.2.2.2.2.1 θ ⟨hθ0, hθ⟩)

/-- short_v3.70; Proposition (Reduction), sec5d_monotone.tex l.122-124: "Let 1 < p < 2 and λ ∈ [−1, 1). If K_f is
strictly decreasing on (0, π), then 𝒟_C ≥ 0 on ℂ, with equality only at z_* and z̄_*". -/
theorem prop_reduction {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hdec : StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi)) :
    (∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) ∧
    ∀ z : ℂ, critD p (gk p lam) (kConst p lam) lam z = 0 →
      z = curveZ p lam (Real.pi / p) ∨ z = conj (curveZ p lam (Real.pi / p)) := by
  apply GKSharp.Proofs.Reduction.prop_reduction_proved <;> assumption

/-- short_v3.70; sec5d_monotone.tex l.151-156 with Theorem 5.1 (label C1), P019_paper.tex l.151-153: for `1 < p < ∞` and
`λ ∈ [−1, 0]`, "‖P₊ + λP₋‖_p = GK_p(λ)". -/
theorem thm_C1 {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) {lam : ℝ}
    (hl : -1 ≤ lam) (hl0 : lam ≤ 0) : pencilNorm P lam = gk p lam := by
  apply GKSharp.Proofs.TheoremC1.thm_C1_proved <;> assumption

/-- short_v3.70; Theorem 5.1 (label C1), equality case, sec5d_monotone.tex l.154 (`1 < p < 2`, `λ ∈ [−1, 0]`):
"with equality in (*) only at z_* and z̄_*". -/
theorem thm_C1_equality {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl0 : lam ≤ 0) :
    (∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) ∧
    ∀ z : ℂ, critD p (gk p lam) (kConst p lam) lam z = 0 →
      z = curveZ p lam (Real.pi / p) ∨ z = conj (curveZ p lam (Real.pi / p)) := by
  apply GKSharp.Proofs.TheoremC1.thm_C1_equality_proved <;> assumption

end SharpCurveReductionAndC1

section LocalOperatorConsequences
open Set GKSharp.Threshold

/-- short_v3.70/sec4b_failure.tex:17–21, Theorem 4.4 (label L). Under (4.2), "then $\|\Pp + \lambda \Pm\|_p > \GK_p(\lambda)$". -/
theorem sec4_thm_L (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) :
    1 < p → p < 2 → ∀ lam ∈ Ioo (0 : ℝ) 1,
      1 < localTest p lam → gk p lam < pencilNorm P lam := by
  apply GKSharp.sec4_thm_L_proved <;> assumption

/-- short_v3.70/sec4b_failure.tex:15. "for $p>2$ the statements below hold with $p'$ in place of $p$, by duality (Section~1)". -/
theorem sec4_thm_L_dual (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (P : RieszProjection p) (hp : 2 < p) :
    ∀ lam ∈ Ioo (0 : ℝ) 1, 1 < localTest p lam → gk p lam < pencilNorm P lam := by
  apply GKSharp.sec4_thm_L_dual_proved <;> assumption

/-- short_v3.70/sec4b_failure.tex:110. "$h(\lambda, p) < 0$ implies $\|\Pp + \lambda\Pm\|_p > \GK_p(\lambda)$." -/
theorem sec4_axis_negative_fails (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (P : RieszProjection p) (hp : 1 < p) (hp2 : p < 2) (lam : ℝ)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) (hh : h p lam < 0) : gk p lam < pencilNorm P lam := by
  apply GKSharp.sec4_axis_negative_fails_proved <;> assumption

/-- short_v3.70; sec4a_criterion.tex:79. "If $\Omega(p) < 0$, then $\|\Pp + \lambda\Pm\|_p > \GK_p(\lambda)$ for all $\lambda < 1$ close enough to $1$." -/
theorem sec4_prop_F (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) :
    1 < p → p < 2 → omega p < 0 →
      ∃ eps > 0, ∀ lam : ℝ, 1 - eps < lam → lam < 1 → gk p lam < pencilNorm P lam := by
  apply GKSharp.sec4_prop_F_proved <;> assumption
end LocalOperatorConsequences

section CstarReadyLeavesAndHeadlineB
open Set Filter Topology GKSharp.Threshold GKSharp.ComputerChecked
open scoped ContDiff

/-- short_v3.70; sec5e_cstar.tex l.22-24: "Λ(0⁺) = Φ(ρ₀)/(1−λ)^p with ρ₀ real, i.e. a value of 𝒟_C/|1+z|^p on the
positive axis, which is ≥ 0 because h ≥ 0" (`ρ₀ = (1 + λr₀)/(1 + r₀)` as in `sec5_A2`). -/
theorem sec5e_Lambda_zero {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1) :
    let r0 := curveRoot lam (1 - p / 2) (p / 2)
    let ρ0 := (1 + lam * r0) / (1 + r0)
    Tendsto ((fun θ : ℝ => mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam θ)) / (1 - lam) ^ p)) (𝓝[>] 0)
      (𝓝 (mobPhi p (gk p lam) (kConst p lam) lam (ρ0 : ℂ) / (1 - lam) ^ p)) ∧
    (kConst p lam ≤ obstacle p (gk p lam) lam 0 → 0 ≤ mobPhi p (gk p lam) (kConst p lam) lam (ρ0 : ℂ)) := by
  apply GKSharp.CstarCurve.sec5e_Lambda_zero_proved <;> assumption

/-- short_v3.70; sec4a_criterion.tex l.71-73 (proof of Proposition 4.2 (label Q), "Only if", after `A_φ = K`): "A q-subtrigonometric
function lies, on any interval of length at most π/q, above the sinusoid with its value and right derivative at the left end [HKV, Lemma 3.2]; at
θ₀ this sinusoid is K cos(qt), since φ(θ₀)=0 and φ′(θ₀⁺)=−Kq, and [θ₀, π] has length π − π/p < π/q. So m_GK ≥ φ ≥ K cos(qt) on [θ₀, π]". Here φ is the
q-subtrigonometric minorant of Theorem 2.2 (label R), equal to A_φ cos(qt) on the arch [−θ₀, θ₀] (l.68) with
A_φ = K (l.71). -/
theorem sec4_cosine_exterior_support (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Set.Ico (-1 : ℝ) 1) (ff : ℝ → ℝ) (hf : QSubtrig (Threshold.q p) ff)
    (hminor : ∀ t, ff t ≤ Threshold.obstacle p lam t)
    (harch : ∀ t ∈ Set.Icc (-Threshold.theta p) (Threshold.theta p),
      ff t = kConst p lam * Real.cos (Threshold.q p * t)) :
    ∀ t ∈ Set.Icc (Threshold.theta p) Real.pi,
      kConst p lam * Real.cos (Threshold.q p * t) ≤ ff t ∧ ff t ≤ Threshold.obstacle p lam t := by
  apply GKSharp.sec4_cosine_exterior_support_proved <;> assumption

/-- short_v3.70; Theorem 5.2 (label B) (b), P019_paper.tex l.158: "If p < p₀ or p > p₀′, then ‖P₊ + λP₋‖_p > GK_p(λ) for every
λ < 1 close enough to 1". Its hypotheses are the computer checks of its proof (Proposition 4.3 (label F) and duality,
sec5d_monotone.tex l.162): `Ω < 0` on `(1, p₀)` is `p0_spec` (`CheckOmegaNeg`, `CheckOmegaRoot`). -/
theorem thm_B_b (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p)
    (hout : p < Threshold.p0 ∨ Threshold.p0 / (Threshold.p0 - 1) < p) :
    ∃ ε > 0, ∀ lam : ℝ, 1 - ε < lam → lam < 1 → gk p lam < pencilNorm P lam := by
  apply GKSharp.ThmBb.thm_B_b_proved <;> assumption

/-- short_v3.70/sec4b_failure.tex:108–110. "We have $h(0, p) > 0$" from C1's equality classification and an attained actual axis minimum. -/
theorem axis_zero_positive (p : ℝ) (hp : 1 < p) (hp2 : p < 2) : 0 < h p 0 := by
  apply GKSharp.axis_zero_positive_proved <;> assumption

/-- short_v3.70; sec5e_cstar.tex l.18-20 ("If" part): "Since 3 − √3 < 4/3, Lemma 5.11 (for p < 4/3) and Lemma 5.10
(for p ≥ 3 − √3) together cover 1 < p < 2. They show that K_f is either decreasing, or increasing on (0, θ_λ] and
decreasing afterwards; in the second case θ_λ < θ₀, because K_f′(θ₀) < 0 whereas K_f′ ≥ 0 on (0, θ_λ]. Hence
{K_f < K} = (0, θ_a) ∪ (θ₀, π) for some θ_a ∈ [0, θ₀)". -/
theorem sec5e_Kf_below {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hh : kConst p lam ≤ obstacle p (gk p lam) lam 0) (hloc : lam < Threshold.lambdaLoc p) :
    (StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) ∨
      ∃ θl ∈ Set.Ioo 0 (Real.pi / p), StrictMonoOn (curveKf p lam) (Set.Ioc 0 θl) ∧
        StrictAntiOn (curveKf p lam) (Set.Ico θl Real.pi)) ∧
    ∃ θa ∈ Set.Ico 0 (Real.pi / p),
      {θ ∈ Set.Ioo 0 Real.pi | curveKf p lam θ < kConst p lam} =
        Set.Ioo 0 θa ∪ Set.Ioo (Real.pi / p) Real.pi := by
  exact GKSharp.sec5e_Kf_below_proved GKSharp.Proofs.TheoremCstar.kf_slope hp1 hp2 hl0 hl1 hh hloc

/-- short_v3.70; sec5e_cstar.tex l.21-22 ("If" part: `h(λ, p) ≥ 0`, `λ < λ_loc(p)`): "Thus Λ ≥ min(Λ(0⁺), 0) and Λ > 0
away from θ₀ unless Λ(0⁺) < 0" (here `Λ(0⁺) ≥ 0`, l.22-24). -/
theorem sec5e_Lambda_pos {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hh : kConst p lam ≤ obstacle p (gk p lam) lam 0) (hloc : lam < Threshold.lambdaLoc p) :
    ∀ θ ∈ Set.Ioo 0 Real.pi, θ ≠ Real.pi / p → 0 < (fun θ : ℝ => mobPhi p (gk p lam) (kConst p lam) lam (mobW lam (curveZ p lam θ)) / (1 - lam) ^ p) θ := by
  obtain ⟨hshape, hset⟩ := sec5e_Kf_below hp1 hp2 hl0 hl1 hh hloc
  exact GKSharp.CstarLambdaPos.lambda_pos_of_shape hp1 hp2 hl0 hl1 hshape hset
    (GKSharp.CstarCurve.mobPhi_rho0_nonneg hp1 hp2 (by linarith) hl1 hh)

end CstarReadyLeavesAndHeadlineB

/-! ## NOT stated
-/

section EndpointEdgeStripAndCstar
open Real Set Filter Topology GKSharp.Threshold GKSharp.ComputerChecked

/-- Lemma A.1 (label endpoint), short_v3.70/endpoint_estimate.tex:7–9. "For $1<p\le1+10^{-6}$,
$h(\lambda_{\mathrm{loc}}(p),p)<-1.88$." (`h = axisGap`; this is case (b) of the proof of Proposition 4.7,
sec4b_failure.tex l.131-132.) -/
theorem slice_E01 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    axisGap p (Threshold.lambdaLoc p) < -(1.88 : ℝ) ∧ axisGap p (Threshold.lambdaLoc p) < 0 := by
  exact GKSharp.endpoint_estimate_proved hp hp1

/-- short_v3.70/endpoint_estimate.tex:12–17. "$s_0=\sin a=\sin(\pi/p)$ and $c_0=\cos a=-\cos(\pi/p)$. Put d^2=\frac{s_0^2}{c_0^4}\left(\frac{p\pi}{4a}-1-c_0^2\right),\qquad \lambda=\frac{1-d}{1+d},\qquad \delta=1-\lambda=\frac{2d}{1+d},\qquad Q_A=\frac{\delta}{s_0}." -/
theorem slice_E03 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let d := endpointD p
    0 < d ∧ d < 1 ∧ d ^ 2 = sin a ^ 2 / cos a ^ 4 * (p * Real.pi / (4 * a) - 1 - cos a ^ 2) ∧
    1 - endpointLambda p = 2 * d / (1 + d) ∧
    (∀ lam : ℝ, 0 < lam → lam < 1 →
      (p * (p / (p - 1)) / 4 * sin (Real.pi / p) ^ 2 +
        4 * lam * cos (Real.pi / p) ^ 4 / (1 + lam) ^ 2 = 1 ↔ lam = endpointLambda p)) := by
  dsimp only
  obtain ⟨hd0, hd1, hd2, he, _⟩ := GKSharp.endpoint_d_basic hp hp1
  exact ⟨hd0, hd1, hd2, he, fun lam h0 h1 => GKSharp.endpoint_threshold_equation hp hp1 lam h0 h1⟩

/-- short_v3.70/endpoint_estimate.tex:19–21. "p-1\le a/3,\quad a-a^3/6\le s_0\le a,\quad 1-a^2/2\le c_0\le1, \quad \frac{\pi a}{4}(1-3a)\le d^2\le\frac{\pi a}{4}(1+a)." -/
theorem slice_E04 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    p - 1 ≤ a / 3 ∧ a - a ^ 3 / 6 ≤ sin a ∧ sin a ≤ a ∧
    1 - a ^ 2 / 2 ≤ cos a ∧ cos a ≤ 1 ∧
    Real.pi * a / 4 * (1 - 3 * a) ≤ endpointD p ^ 2 ∧
    endpointD p ^ 2 ≤ Real.pi * a / 4 * (1 + a) := by
  dsimp only
  obtain ⟨hslo, hshi, hclo, hchi⟩ := GKSharp.endpoint_trig_bounds hp
  obtain ⟨hdlo, hdhi⟩ := GKSharp.endpoint_d_squared_bounds hp hp1
  exact ⟨GKSharp.endpoint_p_sub_one hp hp1, hslo, hshi, hclo, hchi, hdlo, hdhi⟩

/-- short_v3.70/endpoint_estimate.tex:26–28. "\sqrt a\le \delta\le1.8\sqrt a,\qquad a^{-1/2}\le Q_A\le2a^{-1/2},\qquad 2d\le1.8\sqrt a." -/
theorem slice_E06 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let ε := 1 - endpointLambda p
    let Q := ε / sin a
    sqrt a ≤ ε ∧ ε ≤ 1.8 * sqrt a ∧
    a ^ (-(1 / 2 : ℝ)) ≤ Q ∧ Q ≤ 2 * a ^ (-(1 / 2 : ℝ)) ∧
    2 * endpointD p ≤ 1.8 * sqrt a := by
  exact GKSharp.endpoint_scale_bounds hp hp1

/-- short_v3.70/endpoint_estimate.tex:30–31. "$C=(Q_A+\sqrt{Q_A^2+4\lambda})/2$, hence $C^2\le Q_A^2+2$ and $C\le Q_A+Q_A^{-1}\le2Q_A$." -/
theorem slice_E07 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let lam := endpointLambda p
    let Q := (1 - lam) / sin (endpointA p)
    let C := gk p (lam : ℂ)
    C = (Q + sqrt (Q ^ 2 + 4 * lam)) / 2 ∧ C ^ 2 ≤ Q ^ 2 + 2 ∧
      C ≤ Q + Q⁻¹ ∧ Q + Q⁻¹ ≤ 2 * Q := by
  exact GKSharp.endpoint_gk_bounds hp hp1

/-- short_v3.70/endpoint_estimate.tex:32–35. "Inequality~(4.6) with $\vartheta=1/2$, that is, $\rho=(1+\lambda)/2$, gives h(\lambda,p)\le U_1-U_2-K,\qquad U_1=(2C)^p,\qquad U_2=(2\rho)^p." -/
theorem slice_E08 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let lam := endpointLambda p
    let C := gk p (lam : ℂ)
    let w := (1 + lam) / 2
    axisGap p lam ≤ (2 * C) ^ p - (2 * w) ^ p - kConst p lam := by
  exact GKSharp.endpoint_midpoint_bound hp hp1

/-- short_v3.70/endpoint_estimate.tex:36–37. "With $x=(p-1)\log(2C)$, we have $0\le x\le(a/3)\log(8/\sqrt a)<1$. The estimate $e^x\le1+2x$ therefore yields" -/
theorem slice_E09 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let C := gk p (endpointLambda p : ℂ)
    let x := (p - 1) * log (2 * C)
    0 ≤ x ∧ x ≤ a / 3 * log (8 / sqrt a) ∧ a / 3 * log (8 / sqrt a) < 1 ∧
      exp x ≤ 1 + 2 * x := by
  exact GKSharp.endpoint_log_bound hp hp1

/-- short_v3.70/endpoint_estimate.tex:38–41. "U_1\le2Q_A+\frac2{Q_A}+\frac83Q_Aa\log\frac8{\sqrt a},\qquad U_2\ge2\rho=\frac2{1+d}\ge2-2d." -/
theorem slice_E10 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let d := endpointD p
    let lam := endpointLambda p
    let Q := (1 - lam) / sin a
    let C := gk p (lam : ℂ)
    let w := (1 + lam) / 2
    (2 * C) ^ p ≤ 2 * Q + 2 / Q + 8 / 3 * Q * a * log (8 / sqrt a) ∧
      2 * w ≤ (2 * w) ^ p ∧ 2 * w = 2 / (1 + d) ∧ 2 - 2 * d ≤ 2 / (1 + d) := by
  exact GKSharp.endpoint_term_bounds hp hp1

/-- short_v3.70/endpoint_estimate.tex:42–48. "$v=r-\lambda/r=\sqrt{\delta^2+4\lambda s_0^2}/c_0$. The contact equation $r+\lambda/r=(1+\lambda)/c_0$ implies \frac1{c_0}\le r\le\frac{1+s_0^2/\delta}{c_0},\qquad v\le\frac{\delta(1+2s_0^2/\delta^2)}{c_0},\qquad |re^{i\pi/p}+\lambda|\ge r-\lambda\ge \delta." -/
theorem slice_E11 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let lam := endpointLambda p
    let ε := 1 - lam
    let r := contactRadius p lam
    let v := r - lam / r
    v = sqrt (ε ^ 2 + 4 * lam * sin a ^ 2) / cos a ∧
    r + lam / r = (1 + lam) / cos a ∧
    1 / cos a ≤ r ∧ r ≤ (1 + sin a ^ 2 / ε) / cos a ∧
    v ≤ ε * (1 + 2 * sin a ^ 2 / ε ^ 2) / cos a ∧
    ε ≤ r - lam ∧ r - lam ≤ ‖(r : ℂ) * unitPoint (Real.pi / p) + (lam : ℂ)‖ := by
  exact GKSharp.endpoint_contact_bounds hp hp1

/-- short_v3.70/endpoint_estimate.tex:49–53. "K=2Q_A\,r^{-q}\frac{|re^{i\pi/p}+\lambda|^p}{v} \ge2Q_A\frac{c_0^2\delta^{p-1}}{(1+s_0^2/\delta)(1+2s_0^2/\delta^2)} \ge2Q_A(1-E_K)," -/
theorem slice_E12 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let lam := endpointLambda p
    let ε := 1 - lam
    let Q := ε / sin a
    let r := contactRadius p lam
    let v := r - lam / r
    let E := (p - 1) * log (1 / ε) + a ^ 2 + sin a ^ 2 / ε + 2 * sin a ^ 2 / ε ^ 2
    kConst p lam = 2 * Q * r ^ (-(p / 2)) *
      ‖(r : ℂ) * unitPoint (Real.pi / p) + (lam : ℂ)‖ ^ p / v ∧
    2 * Q * (cos a ^ 2 * ε ^ (p - 1) /
      ((1 + sin a ^ 2 / ε) * (1 + 2 * sin a ^ 2 / ε ^ 2))) ≤ kConst p lam ∧
    2 * Q * (1 - E) ≤ kConst p lam := by
  dsimp only
  exact ⟨GKSharp.endpoint_contact_k_identity hp hp1, (GKSharp.endpoint_k_lower_bounds hp hp1).1,
    (GKSharp.endpoint_k_lower_bounds hp hp1).2⟩

/-- short_v3.70/endpoint_estimate.tex:55–61. "E_K=(p-1)\log(1/\delta)+a^2+\frac{s_0^2}{\delta}+\frac{2s_0^2}{\delta^2} \le\frac a6\log\frac1a+a^2+a^{3/2}+2a." -/
theorem slice_E13 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    let a := endpointA p
    let ε := 1 - endpointLambda p
    let E := (p - 1) * log (1 / ε) + a ^ 2 + sin a ^ 2 / ε + 2 * sin a ^ 2 / ε ^ 2
    E ≤ a / 6 * log (1 / a) + a ^ 2 + a ^ (3 / 2 : ℝ) + 2 * a ∧
    1 - (p - 1) * log (1 / ε) ≤ ε ^ (p - 1) ∧
    1 - a ^ 2 ≤ cos a ^ 2 ∧ E < 1 ∧
    (∀ u : ℝ, 0 ≤ u → 1 - u ≤ (1 + u)⁻¹) := by
  exact GKSharp.endpoint_k_error_bounds hp hp1

/-- short_v3.70/endpoint_estimate.tex:62–66. "h(\lambda_{\mathrm{loc}}(p),p)\le-2+R(a),\qquad R(a)=\sqrt a\left[2+\frac{16}3\log\frac8{\sqrt a}+1.8+\frac23\log\frac1a+8+4\sqrt a+4a\right]." -/
theorem slice_E14 {p : ℝ} (hp : 1 < p) (hp1 : p ≤ 1 + 10 ^ (-6 : ℤ)) :
    axisGap p (endpointLambda p) ≤ -2 + endpointError (endpointA p) := by
  exact GKSharp.endpoint_remainder_bound hp hp1

/-- short_v3.70/endpoint_estimate.tex:67–67. "Every term in $R$ is increasing on $(0,\bar a]$: in particular $\sqrt a\log(1/a)$ increases for $a<e^{-2}$." -/
theorem slice_E15 :
    MonotoneOn endpointError (Set.Ioc 0 (3.2 * 10 ^ (-6 : ℤ))) ∧
    StrictMonoOn (fun a : ℝ => sqrt a * log (1 / a)) (Set.Ioo 0 (exp (-2))) := by
  exact ⟨GKSharp.endpoint_error_monotone, GKSharp.sqrt_mul_log_strictMono⟩

/-- short_v3.70/endpoint_estimate.tex:68–68. "Finally $\sqrt{\bar a}<0.001789$, $\log(8/\sqrt{\bar a})<8.5$, and $\log(1/\bar a)<12.66$ give $R(\bar a)<0.12$." -/
theorem slice_E16 :
    let a₁ : ℝ := 3.2 * 10 ^ (-6 : ℤ)
    sqrt a₁ < 0.001789 ∧ log (8 / sqrt a₁) < 8.5 ∧ log (1 / a₁) < 12.66 ∧
      endpointError a₁ < 0.12 := by
  exact GKSharp.endpoint_error_numeric

/-- short_v3.70/sec4b_failure.tex:118–121. "For every $1 < p < p_c$, $h(\lambda_{\mathrm{loc}}(p), p) < 0$." The actual first positive axis zero and strict norm failure at the local threshold are included. The three named checks stay explicit. -/
theorem sec4_prop_edge (hc : CheckLocalF) (hb : CheckBoundaryBulk)
    (hs : CheckBoundarySliver) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (P : RieszProjection p) : 1 < p → p < pc → h p (lambdaLoc p) < 0 ∧
    IsLeast (axisZeros p) (lambda0 p) ∧ 0 < lambda0 p ∧ lambda0 p < lambdaLoc p ∧
    gk p (lambdaLoc p) < pencilNorm P (lambdaLoc p) := by
  exact GKSharp.sec4_prop_edge_proved hc hb hs p P

/-- short_v3.70/sec5f_strip.tex:43–45. "Let $p_0 \le p \le 1.268$ and $0 < \lambda < 1$. Then $h(\lambda, p) > 0$." The operator conclusion for every real ratio on the stated exponent strip is included, with its seven named checks: sec5f_strip.tex:74–75 "For $p_0\le p<3-\sqrt3$ we have $p>p_c$, so $\lambda_{\mathrm{loc}}=1$ and Theorem~5.3 turns $h>0$ into equality for $0<\lambda<1$." and "So the bound is sharp for every real ratio when $p_0\le p<3-\sqrt3$." -/
theorem sec5_prop_S (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hcd : CheckCornerDerivatives) (hct : CheckCornerTails)
    (hbm : CheckStripBulkMiddle) (hbt : CheckStripBulkTails) (hc : CheckLocalF)
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) : (p ∈ Icc p0 (317 / 250 : ℝ) → ∀ lam ∈ Ioo (0 : ℝ) 1, 0 < h p lam) ∧
  (p ∈ Ico p0 (3 - Real.sqrt 3) → ∀ lam : ℝ, pencilNorm P lam = gk p lam) := by
  exact GKSharp.sec5_prop_S_proved hn hr hcd hct hbm hbt hc p P

/-- short_v3.70; Theorem 5.3 (label Cstar), P019_paper.tex l.161-163 (proof sec5e_cstar.tex l.12-30): "Let 1 < p < 2 and
0 < λ < 1. Then ‖P₊ + λP₋‖_p = GK_p(λ) if and only if m_GK(0) ≥ K (the first condition in (1.1)) and
λ < λ_loc(p), where λ_loc is the threshold defined in Section 1 (see Theorem 4.4 and Lemma 4.6; so
λ_loc = 1 for p ≥ p_c)". (`m_GK(0) ≥ K` is `0 ≤ axisGap p lam`, i.e. h(λ, p) ≥ 0; `λ_loc` is the shared
`Threshold.lambdaLoc`, whose clamp to 1 is `lambdaLoc_spec`.) Its hypotheses are the computer checks of its proof: the
case `λ = λ_loc(p)` uses Proposition 4.7 (label edge) (`CheckLocalF`, `CheckBoundaryBulk`, `CheckBoundarySliver`), and the
description of `λ_loc` uses `CheckLocalF`. -/
theorem thm_Cstar (hc : CheckLocalF) (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp1 : 1 < p) (hp2 : p < 2) (P : RieszProjection p)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    pencilNorm P lam = gk p lam ↔
      kConst p lam ≤ obstacle p (gk p lam) lam 0 ∧ lam < Threshold.lambdaLoc p := by
  exact GKSharp.Proofs.TheoremCstar.thm_Cstar_of GKSharp.Proofs.TheoremCstar.kf_slope hc hp1 hp2 P
    (fun hpc => GKSharp.boundary_edge_proved hc hb hs p hp1 hpc) hl0 hl1

end EndpointEdgeStripAndCstar

section HeadlineClosureAndScalarLeaves
open Set Filter Topology GKSharp.Threshold GKSharp.ComputerChecked
open scoped ContDiff

/-- Theorem 5.2 (label B) (a), P019_paper.tex l.156-157: "Let p₀ and p₀′ be as in Theorem 1.1 (p₀ ≈ 1.2336026,
p₀′ ≈ 5.2807742). (a) If p₀ ≤ p ≤ p₀′, then ‖P₊ + λP₋‖_p = GK_p(λ) for every λ ∈ ℝ". Its hypotheses are the
computer checks of its proof (sec5d_monotone.tex l.157-162, sec5f_strip.tex l.43-45 and l.74-75): the six
checks of Proposition 5.14 (label strip), and `CheckLocalF` for `p_c < p₀` (`pc_lt_p0`), which gives `λ_loc = 1` in
Theorem 5.3. -/
theorem thm_B_a (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hcd : CheckCornerDerivatives) (hct : CheckCornerTails)
    (hbm : CheckStripBulkMiddle) (hbt : CheckStripBulkTails) (hc : CheckLocalF)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p)
    (hlo : Threshold.p0 ≤ p) (hhi : p ≤ Threshold.p0 / (Threshold.p0 - 1)) :
    ∀ lam : ℝ, pencilNorm P lam = gk p lam := by
  exact GKSharp.ThmBa.thm_B_a_of hn hr (fun q _ Q hq => (GKSharp.sec5_prop_S_proved hn hr hcd hct hbm hbt hc q Q).2 hq) hp P hlo hhi

/-- Theorem 5.2 (label B) (c), P019_paper.tex l.159: "If p₀ ≤ p ≤ p₀′, p ≠ 2 and α ≠ 0, then
‖αP₊ + βP₋‖_p = GK_p(α, β) if and only if β/α ∈ ℝ. If α = 0, the bound is always sharp" ("always": every
`p > 1`, so the `α = 0` clause is outside the range hypotheses). Its hypotheses are the computer checks of
Theorem 5.2 (a) (`thm_B_a`), used for the "if" direction; the "only if" direction (Theorem 3.2) and the `α = 0` clause
use no computer check. -/
theorem thm_B_pair (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hcd : CheckCornerDerivatives) (hct : CheckCornerTails)
    (hbm : CheckStripBulkMiddle) (hbt : CheckStripBulkTails) (hc : CheckLocalF)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) :
    (Threshold.p0 ≤ p → p ≤ Threshold.p0 / (Threshold.p0 - 1) → p ≠ 2 →
      ∀ α β : ℂ, α ≠ 0 → (‖pencil P α β‖ = gkPair p α β ↔ (β / α).im = 0)) ∧
    ∀ β : ℂ, ‖pencil P 0 β‖ = gkPair p 0 β := by
  exact GKSharp.ThmBa.thm_B_pair_of hn hr (fun q _ Q hq => (GKSharp.sec5_prop_S_proved hn hr hcd hct hbm hbt hc q Q).2 hq) hp P

/-- Theorem 1.1 (label classification), P019_paper.tex l.97-103: "Let 1 < p < ∞ and p₀′ = p₀/(p₀ − 1).
(a) If p ≠ 2 and ρ ∉ ℝ, then N_p(ρ) > GK_p(ρ). (b) If λ ≤ 0 is real, then N_p(λ) = GK_p(λ). (c) The equality
N_p(λ) = GK_p(λ) holds for every real λ if and only if p₀ ≤ p ≤ p₀′. If p < p₀ or p > p₀′, then N_p(λ) > GK_p(λ)
for every λ < 1 sufficiently close to 1. (d) If 1 < p < 2 and 0 < λ < 1, then N_p(λ) = GK_p(λ) if and only if both
conditions in (1.1) hold."; after it, l.104: "part (d) as Theorem 5.3; for p > 2 part (d) applies with p′ in place
of p, since N_p(λ) = N_{p′}(λ) and GK_p = GK_{p′}. Ratios λ > 1 reduce to 1/λ by the reciprocal symmetries above,
and the bound is sharp for λ = 1, for p = 2 and for α = 0." Each clause is its own conjunct, with five clauses
carried by companion rows and links: (b) "If λ ≤ 0 is real" is stated here for `−1 ≤ λ ≤ 0` (Theorem 5.1) and for every `λ ≤ 0` by
`thm_classification_nonpositive`; the criterion is stated here with Theorem 5.3's axis condition `m_GK(0) ≥ K` and
in the form (1.1) by `thm_classification_tests`; the reduction of `λ > 1` is `thm_classification_reciprocal`;
`λ = 1` is `sec5_lambda_one`; `α = 0` is the link `cover_final_alpha_zero_sharp` (from the `α = 0` conjunct
of `thm_B_pair`, with no computer check). The criterion clause is stated for `1 < p < 2` and for `p > 2` (at
`p′ = p/(p−1)`). Its hypotheses are the union of the computer
checks of Theorems 5.2 and 5.3 (`thm_B_a`, `thm_B_b`, `thm_Cstar`); the clauses for `ρ ∉ ℝ`, `λ ∈ [−1, 0]` and
`p = 2` use none (they are also the rows `thm_A`, `thm_C1`). Caption of Figure 1, P019_paper.tex:113: "and for every
$\lambda$ when $p_0\le p<2$" (clause (c), first sentence, for `p < 2`; the literal form is the link
`cover_q17_intro_regime_sharp`) and "In the hatched band the criterion of Theorem~\ref{thm:classification}(d) still
applies to each $\lambda$, but its outcome is known only in part; for example, when $p_c\le p<p_0$ the bound is not
sharp for every $\lambda<1$ close enough to $1$ (Theorem~\ref{thm:classification}(c))" (clause (d); clause (c), second
sentence, for `p < p₀`; the words on what is known are not a claim). -/
theorem thm_classification (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hcd : CheckCornerDerivatives) (hct : CheckCornerTails)
    (hbm : CheckStripBulkMiddle) (hbt : CheckStripBulkTails)
    (hc : CheckLocalF) (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) :
    (p ≠ 2 → ∀ ρ : ℂ, ρ.im ≠ 0 → gk p ρ < pencilNorm P ρ) ∧
    (∀ lam : ℝ, -1 ≤ lam → lam ≤ 0 → pencilNorm P lam = gk p lam) ∧
    ((∀ lam : ℝ, pencilNorm P lam = gk p lam) ↔
      Threshold.p0 ≤ p ∧ p ≤ Threshold.p0 / (Threshold.p0 - 1)) ∧
    ((p < Threshold.p0 ∨ Threshold.p0 / (Threshold.p0 - 1) < p) →
      ∃ ε > 0, ∀ lam : ℝ, 1 - ε < lam → lam < 1 → gk p lam < pencilNorm P lam) ∧
    (p < 2 → ∀ lam : ℝ, 0 < lam → lam < 1 →
      (pencilNorm P lam = gk p lam ↔
        kConst p lam ≤ obstacle p (gk p lam) lam 0 ∧ lam < Threshold.lambdaLoc p)) ∧
    (2 < p → ∀ lam : ℝ, 0 < lam → lam < 1 →
      (pencilNorm P lam = gk p lam ↔
        kConst (p / (p - 1)) lam ≤ obstacle (p / (p - 1)) (gk (p / (p - 1)) lam) lam 0 ∧
          lam < Threshold.lambdaLoc (p / (p - 1)))) ∧
    (p = 2 → ∀ ρ : ℂ, pencilNorm P ρ = gk p ρ) := by
  exact GKSharp.ThmClass.thm_classification_of hn hr (fun q _ Q hq => (GKSharp.sec5_prop_S_proved hn hr hcd hct hbm hbt hc q Q).2 hq) (fun _ _ Q hq1 hq2 _ hl0 hl1 => GKSharp.Proofs.TheoremCstarFinal.thm_Cstar_proved hc hb hs hq1 hq2 Q hl0 hl1) hp P

/-- short_v3.70/sec5_sharp_inequality.tex:88–94. "θ is a smooth function of ρ"; local inverse conclusion (route R8(ii)). -/
theorem sec5_A2_ift {p lam θ₀ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 ≤ lam) (hl1 : lam < 1)
    (hθ0 : 0 < θ₀) (hθ : θ₀ < Real.pi) :
    DifferentiableAt ℝ ((fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖)) θ₀ ∧
    ∃ g : ℝ → ℝ, (∀ᶠ θ in 𝓝 θ₀, g ((fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖) θ) = θ) ∧ ContDiffAt ℝ ∞ g ((fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖) θ₀) ∧
      deriv ((fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖)) θ₀ * deriv g ((fun θ : ℝ => ‖mobW lam (curveZ p lam θ)‖) θ₀) = 1 := by
  exact GKSharp.A2Ift.sec5_A2_ift_proved hp1 hp2 hl hl1 hθ0 hθ

/-- short_v3.70/sec2_obstacle.tex:22–30. "They determine its singular values and are unchanged" by the listed symmetries, including conjugate exponents. -/
theorem sec2_gk_from_invariants (p : ℝ) (α β α' β' : ℂ)
    (hF : ∑ i, ∑ j, ‖gkMatrix p α β i j‖ ^ 2 = ∑ i, ∑ j, ‖gkMatrix p α' β' i j‖ ^ 2)
    (hD : ‖(gkMatrix p α β).det‖ = ‖(gkMatrix p α' β').det‖) : gkPair p α β = gkPair p α' β' := by
  exact GKSharp.GKSingular.sec2_gk_from_invariants_proved p α β α' β' hF hD

/-- short_v3.70/sec2_obstacle.tex:22–30. "They determine its singular values and are unchanged" by the listed symmetries, including conjugate exponents. -/
theorem sec2_gkPair_dual {p : ℝ} (hp : 1 < p) (α β : ℂ) : gkPair (p / (p - 1)) α β = gkPair p α β := by
  exact GKSharp.GKSingular.sec2_gkPair_dual_proved hp α β

/-- short_v3.70/sec4a_criterion.tex:67–74. "hence A_φ = K" and "So m_GK ≥ φ ≥ K cos(qt)"; the full interval follows by evenness. -/
theorem angular_contact_determines_cos (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hlam : lam ∈ Ico (-1 : ℝ) 1) (f : ℝ → ℝ)
    (hf : Continuous f) (hq : QTrigConvex (q p) f)
    (hminor : ∀ t : ℝ, f t ≤ Threshold.obstacle p lam t) :
    ∀ t ∈ Icc (-Real.pi) Real.pi, kConst p lam * Real.cos (q p * |t|) ≤ Threshold.obstacle p lam t := by
  exact GKSharp.angular_contact_determines_cos_proved p lam hp hp2 hlam f hf hq hminor

/-- short_v3.70/sec2_obstacle.tex:57–60 "m_C is finite and continuous";
sec4b_failure.tex:114 "Joint continuity of Γ_C(y,0)"; joint parameter version used by the axis restriction. -/
theorem obstacle_joint_continuous (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ContinuousOn (fun x : ℝ × ℝ => Threshold.obstacle p x.1 x.2) (Ioo (-1 : ℝ) 1 ×ˢ univ) := by
  exact GKSharp.obstacle_joint_continuous_proved p hp hp2

/-- short_v3.70/sec5f_strip.tex:16–17. "the bound is sharp at λ ∈ (0,1) exactly when h(λ, p) ≥ 0". -/
theorem sec5_strip_criterion (hc : CheckLocalF) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p)
    (hp : pc ≤ p) (hp2 : p < 2) (lam : ℝ) (hlam : lam ∈ Ioo (0 : ℝ) 1) :
    pencilNorm P lam = gk p lam ↔ 0 ≤ h p lam := by
  exact GKSharp.Proofs.StripCriterion.sec5_strip_criterion_proved hc p P hp hp2 lam hlam

end HeadlineClosureAndScalarLeaves

section Rows160
open Set Filter GKSharp.Threshold GKSharp.ComputerChecked

/-- Theorem 1.1 (label classification), P019_paper.tex l.100: "(b) If λ ≤ 0 is real, then N_p(λ) = GK_p(λ)" (all
`1 < p < ∞`). For `λ ∈ [−1, 0]` this is Theorem 5.1 (`thm_C1`); for `λ < −1` the reciprocal symmetries of
P019_paper.tex l.60 (`intro_norm_inv`) and sec5d_monotone.tex l.159-160 (`sec5_gk_inv`) move `λ` to
`1/λ ∈ (−1, 0)`. No computer check is used. -/
theorem thm_classification_nonpositive {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)
    (P : RieszProjection p) : ∀ lam : ℝ, lam ≤ 0 → pencilNorm P lam = gk p lam := by
  intro lam hl0
  rcases le_or_gt (-1) lam with h1 | h1
  · exact thm_C1 hp P h1 hl0
  · have hneg : lam < 0 := by linarith
    have hne : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hneg.ne
    have hinv1 : -1 ≤ 1 / lam := by
      rw [le_div_iff_of_neg hneg]
      linarith
    have hinv0 : 1 / lam ≤ 0 := one_div_nonpos.mpr hneg.le
    have hcast : 1 / (lam : ℂ) = ((1 / lam : ℝ) : ℂ) := by push_cast; ring
    rw [intro_norm_inv P hne, sec5_gk_inv p hne, hcast, thm_C1 hp P hinv1 hinv0]

/-- Theorem 1.1 (label classification), P019_paper.tex l.104: "Ratios λ > 1 reduce to 1/λ by the reciprocal
symmetries above": for `λ > 1`, `N_p(λ) = GK_p(λ)` if and only if `N_p(1/λ) = GK_p(1/λ)` (all `1 < p < ∞`; from
`intro_norm_inv` and `sec5_gk_inv`). -/
theorem thm_classification_reciprocal {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (P : RieszProjection p) :
    ∀ lam : ℝ, 1 < lam →
      (pencilNorm P lam = gk p lam ↔ pencilNorm P (1 / lam : ℝ) = gk p (1 / lam : ℝ)) := by
  intro lam hl
  have hne : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hcast : 1 / (lam : ℂ) = ((1 / lam : ℝ) : ℂ) := by push_cast; ring
  have hpos : 0 < ‖(lam : ℂ)‖ := norm_pos_iff.mpr hne
  rw [intro_norm_inv P hne, sec5_gk_inv p hne, hcast]
  exact ⟨fun h => mul_left_cancel₀ hpos.ne' h, fun h => by rw [h]⟩

/-- P019_paper.tex l.54-55: "Gohberg and Krupnik proved the lower bound ‖αP₊ + βP₋‖_p ≥ GK_p(α, β)" (every `α, β ∈ ℂ`, `1 < p`): the
normalized bound `slice_O04` with the homogeneity rows `sec2_gk_homogeneous`, `intro_pencil_homogeneous`, and for
`α = 0` the equal values `sec2_gk_pure_minus`, `intro_pencil_zero_left`. -/
theorem intro_gk_lower_pair {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p)
    (α β : ℂ) : gkPair p α β ≤ ‖pencil P α β‖ := by
  rcases eq_or_ne α 0 with h0 | h0
  · subst h0
    rw [sec2_gk_pure_minus p hp β, intro_pencil_zero_left hp P β]
  · rw [sec2_gk_homogeneous p h0 β, intro_pencil_homogeneous P h0 β]
    exact mul_le_mul_of_nonneg_left (slice_O04 hp P (β / α)) (norm_nonneg α)

/-- P019_paper.tex l.85-87 (definitions before Theorem 1.1, `q = p/2`, `s₀ = sin(π/p)`, `c₀ = −cos(π/p)`): "A = (1 − s₀)/(2s₀)";
"put Ω(p) = p(A + s_*)/(s_*(1 − s_*))^q − 2^q s₀^{p−2} c₀^{1−q}"; "K = 2(1 − λ)C s₀^{p−2}
c₀^{1−q}(C² + λ)^{q−1}" with `C = GK_p(λ)`. (That `s_*` is "the unique root in (0, 1)" of
`(2q − 1)s² + (1 − q + 2qA)s − qA = 0` is the row `sStar_spec`.) -/
theorem intro_constants (p : ℝ) :
    aConst p = (1 - sn p) / (2 * sn p) ∧
    omega p = p * (aConst p + sStar p) / (sStar p * (1 - sStar p)) ^ (p / 2) -
      2 ^ (p / 2) * sn p ^ (p - 2) * cs p ^ (1 - p / 2) ∧
    ∀ lam : ℝ, kConst p lam = 2 * (1 - lam) * gk p lam * sn p ^ (p - 2) * cs p ^ (1 - p / 2) *
      (gk p lam ^ 2 + lam) ^ (p / 2 - 1) :=
  ⟨rfl, rfl, fun _ => rfl⟩

/-- P019_paper.tex l.87-88: "Put T(p) = s₀²(pp′/4 − 1 − c₀²)/c₀⁴ and λ_loc(p) = (1 − √T(p))/(1 + √T(p)) if
T(p) > 0, and λ_loc(p) = 1 if T(p) ≤ 0" (`1 < p < 2`, `p′ = p/(p − 1)`): this is Lean's `lambdaLoc`, whose case
split is on the sign of `localF p = pp′ − 4(1 + cos²(π/p))`; `T(p) = s₀² localF(p)/(4c₀⁴)` has the same sign. -/
theorem intro_lambdaLoc_clamp {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    lambdaLoc p =
      if 0 < sn p ^ 2 * (p * (p / (p - 1)) / 4 - 1 - cs p ^ 2) / cs p ^ 4 then
        (1 - Real.sqrt (sn p ^ 2 * (p * (p / (p - 1)) / 4 - 1 - cs p ^ 2) / cs p ^ 4)) /
          (1 + Real.sqrt (sn p ^ 2 * (p * (p / (p - 1)) / 4 - 1 - cs p ^ 2) / cs p ^ 4))
      else 1 := by
  have hp0 : 0 < p := by linarith
  have hs : 0 < sn p :=
    Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hp0) (div_lt_self Real.pi_pos hp)
  have hc : 0 < cs p := neg_pos.mpr (GKSharp.cos_theta_negative hp hp2)
  have hT : sn p ^ 2 * (p * (p / (p - 1)) / 4 - 1 - cs p ^ 2) / cs p ^ 4 =
      sn p ^ 2 / (4 * cs p ^ 4) * localF p := by
    unfold localF dual cs
    ring
  have hk : 0 < sn p ^ 2 / (4 * cs p ^ 4) := by positivity
  have hiff : 0 < localF p ↔ 0 < sn p ^ 2 * (p * (p / (p - 1)) / 4 - 1 - cs p ^ 2) / cs p ^ 4 := by
    rw [hT]
    exact (mul_pos_iff_of_pos_left hk).symm
  unfold lambdaLoc
  exact if_congr hiff rfl rfl

/-- P019_paper.tex l.90 (`1 < p < 2`, `0 < λ < 1`, `C = GK_p(λ)`): the positive-axis test "C^p(1 + x)^p − (1 + λx)^p ≥
K x^q for every x > 0" is `m_GK(0) ≥ K`, the axis condition of Theorem 5.3 (P019_paper.tex l.162). -/
theorem intro_axis_test_iff {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1) :
    kConst p lam ≤ obstacle p (gk p lam) lam 0 ↔
      ∀ x : ℝ, 0 < x → kConst p lam * x ^ (p / 2) ≤ gk p lam ^ p * (1 + x) ^ p - (1 + lam * x) ^ p := by
  have hC := GKSharp.CstarCurve.gk_gt_max_real hp1 hp2 hl1
  have hreal : ∀ x : ℝ, 0 < x → critD p (gk p lam) (kConst p lam) lam (x : ℂ) =
      gk p lam ^ p * (1 + x) ^ p - (1 + lam * x) ^ p - kConst p lam * x ^ (p / 2) := by
    intro x hx
    unfold critD
    have e1 : ‖1 + (x : ℂ)‖ = 1 + x := by
      rw [show (1 : ℂ) + x = ((1 + x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    have e2 : ‖1 + (lam : ℂ) * x‖ = 1 + lam * x := by
      rw [show (1 : ℂ) + lam * x = ((1 + lam * x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    have e5 : reQPow (x : ℂ) (p / 2) = x ^ (p / 2) := by
      rw [reQPow, Complex.norm_real, Real.norm_of_nonneg hx.le, Complex.arg_ofReal_of_nonneg hx.le, mul_zero,
        Real.cos_zero, mul_one]
    rw [e1, e2, e5]
  constructor
  · intro hh x hx
    have hD := GKSharp.CstarCurve.critD_pos_axis_nonneg (KK := kConst p lam) (by linarith) hC hh hx
    rw [hreal x hx] at hD
    linarith
  · intro hall
    rw [(slice_O14 p (gk p lam) lam 0 0).2]
    refine le_csInf ?_ ?_
    · exact ⟨_, 1, one_pos, rfl⟩
    rintro v ⟨r, hr, rfl⟩
    have hx : 0 < r⁻¹ := inv_pos.mpr hr
    have hDc : 0 ≤ critD p (gk p lam) (kConst p lam) lam ((r⁻¹ : ℝ) : ℂ) := by
      rw [hreal r⁻¹ hx]
      linarith [hall r⁻¹ hx]
    rw [GKSharp.CstarCurve.critD_pos_axis_eq hx, inv_inv] at hDc
    have hG : kConst p lam * r ^ (p / 2) ≤ obstacleG p (gk p lam) (lam : ℂ) (r : ℂ) := by
      have := (mul_nonneg_iff_of_pos_left (Real.rpow_pos_of_pos hx p)).mp hDc
      linarith
    have hu : unitPoint 0 = 1 := by simp [unitPoint]
    have hrq : 0 < r ^ (p / 2) := Real.rpow_pos_of_pos hr _
    rw [hu, mul_one, Real.rpow_neg hr.le, le_inv_mul_iff₀ hrq]
    linarith

/-- (1.1) (label introcrit), P019_paper.tex l.89-90 (`1 < p < 2`, `0 < λ < 1`, `C = GK_p(λ)`): "The two conditions
of the criterion are C^p(1 + x)^p − (1 + λx)^p ≥ K x^q for every x > 0, λ < λ_loc(p)", with Theorem 1.1, l.102:
"(d) If 1 < p < 2 and 0 < λ < 1, then N_p(λ) = GK_p(λ) if and only if both conditions in (1.1) hold" (Theorem 5.3 with the axis test of `intro_axis_test_iff`). Its hypotheses are the computer checks of Theorem 5.3
(`thm_Cstar`). -/
theorem intro_tests_criterion (hc : CheckLocalF) (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp1 : 1 < p) (hp2 : p < 2) (P : RieszProjection p)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    pencilNorm P lam = gk p lam ↔
      (∀ x : ℝ, 0 < x → kConst p lam * x ^ (p / 2) ≤ gk p lam ^ p * (1 + x) ^ p - (1 + lam * x) ^ p) ∧
        lam < lambdaLoc p := by
  rw [thm_Cstar hc hb hs hp1 hp2 P hl0 hl1, intro_axis_test_iff hp1 hp2 hl0 hl1]

/-- Theorem 1.1 (label classification), P019_paper.tex l.102 and l.104 with (1.1) (label introcrit), l.90: "(d) If
1 < p < 2 and 0 < λ < 1, then N_p(λ) = GK_p(λ) if and only if both conditions in (1.1) hold"; "for p > 2 part (d)
applies with p′ in place of p", (1.1) being "C^p(1 + x)^p − (1 + λx)^p ≥ K x^q for every x > 0, λ < λ_loc(p)". The two criterion clauses of
`thm_classification` with the axis test of `intro_axis_test_iff`; the hypotheses are those of
`thm_classification`. -/
theorem thm_classification_tests (hn : CheckOmegaNeg) (hr : CheckOmegaRoot)
    (hcd : CheckCornerDerivatives) (hct : CheckCornerTails)
    (hbm : CheckStripBulkMiddle) (hbt : CheckStripBulkTails)
    (hc : CheckLocalF) (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p) :
    (p < 2 → ∀ lam : ℝ, 0 < lam → lam < 1 →
      (pencilNorm P lam = gk p lam ↔
        (∀ x : ℝ, 0 < x → kConst p lam * x ^ (p / 2) ≤ gk p lam ^ p * (1 + x) ^ p - (1 + lam * x) ^ p) ∧
          lam < lambdaLoc p)) ∧
    (2 < p → ∀ lam : ℝ, 0 < lam → lam < 1 →
      (pencilNorm P lam = gk p lam ↔
        (∀ x : ℝ, 0 < x → kConst (p / (p - 1)) lam * x ^ (p / (p - 1) / 2) ≤
            gk (p / (p - 1)) lam ^ (p / (p - 1)) * (1 + x) ^ (p / (p - 1)) - (1 + lam * x) ^ (p / (p - 1))) ∧
          lam < lambdaLoc (p / (p - 1)))) := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := thm_classification hn hr hcd hct hbm hbt hc hb hs hp P
  refine ⟨fun hp2 lam hl0 hl1 => ?_, fun hp2 lam hl0 hl1 => ?_⟩
  · rw [h5 hp2 lam hl0 hl1, intro_axis_test_iff hp hp2 hl0 hl1]
  · have hp1 : 0 < p - 1 := by linarith
    have hq1 : 1 < p / (p - 1) := by
      rw [lt_div_iff₀ hp1]
      linarith
    have hq2 : p / (p - 1) < 2 := by
      rw [div_lt_iff₀ hp1]
      linarith
    rw [h6 hp2 lam hl0 hl1, intro_axis_test_iff hq1 hq2 hl0 hl1]

/-- sec5d_monotone.tex l.34 (`ε = p − 1`, `q = p/2`, `b = εa`; `monoLogL` and `monoLogM` are L of l.21 and M of
l.33, at points where the sines are nonzero): "With p fixed and b = εa, differentiation gives
L_a = ε[q cot(γ+b) − (1−q) cot(γ−b) − cot(γ+a) + 2 cot 2a − 2 cot 2b], L_γ = (1−q) cot(γ−b) + q cot(γ+b) − ε cot(γ+a),
M_a = −cot(γ−a) − cot(γ+a) + ε[cot(γ+b) + cot(γ−b)], M_γ = cot(γ−a) + cot(γ+b) − cot(γ+a) − cot(γ−b)". -/
theorem sec5d_log_partials (p a g : ℝ)
    (hma : Real.sin (g - a) ≠ 0) (hpa : Real.sin (g + a) ≠ 0)
    (hmb : Real.sin (g - (p - 1) * a) ≠ 0) (hpb : Real.sin (g + (p - 1) * a) ≠ 0)
    (h2a : Real.sin (2 * a) ≠ 0) (h2b : Real.sin (2 * ((p - 1) * a)) ≠ 0) :
    HasDerivAt (fun x => monoLogL p x g)
      ((p - 1) * (p / 2 * Real.cot (g + (p - 1) * a) - (1 - p / 2) * Real.cot (g - (p - 1) * a) -
        Real.cot (g + a) + 2 * Real.cot (2 * a) - 2 * Real.cot (2 * ((p - 1) * a)))) a ∧
    HasDerivAt (monoLogL p a)
      ((1 - p / 2) * Real.cot (g - (p - 1) * a) + p / 2 * Real.cot (g + (p - 1) * a) -
        (p - 1) * Real.cot (g + a)) g ∧
    HasDerivAt (fun x => monoLogM p x g)
      (-Real.cot (g - a) - Real.cot (g + a) +
        (p - 1) * (Real.cot (g + (p - 1) * a) + Real.cot (g - (p - 1) * a))) a ∧
    HasDerivAt (monoLogM p a)
      (Real.cot (g - a) + Real.cot (g + (p - 1) * a) - Real.cot (g + a) - Real.cot (g - (p - 1) * a)) g := by
  obtain ⟨h1, h2, h3, h4⟩ := GKSharp.mono_log_partials p a g hma hpa hmb hpb h2a h2b
  exact ⟨h1.congr_deriv (by ring), h2.congr_deriv (by ring), h3.congr_deriv (by ring), h4⟩

end Rows160

section Q15Rows
open Set Filter GKSharp.Threshold
open scoped Topology

/-- short_v3.70/sec4b_failure.tex:128 "$d=\sqrt{T(p)}$, written as $d^2 = \sin^2 a\,(pp'/4 - 1 - \cos^2 a)/\cos^4 a$" (`a = π/p′`,
so `sin a = sin(π/p)`, `cos a = −cos(π/p)`) and :99 "Here $T(p)=s_0^2\mathcal F(p)/(4c_0^4)$, so the two functions have the same sign" (on `1 < p < 2`;
`localD2` is `d²`, `localF` is `F`, `s₀ = sin(π/p)`, `c₀ = −cos(π/p)`). -/
theorem q15_sec4b_T_sign (p : ℝ) :
    localD2 p = Real.sin (Real.pi / p) ^ 2 * (p * (p / (p - 1)) / 4 - 1 - Real.cos (Real.pi / p) ^ 2) /
        Real.cos (Real.pi / p) ^ 4 ∧
    Real.sin (Real.pi / p) ^ 2 * (p * (p / (p - 1)) / 4 - 1 - Real.cos (Real.pi / p) ^ 2) /
        Real.cos (Real.pi / p) ^ 4 = sn p ^ 2 * localF p / (4 * cs p ^ 4) ∧
    (1 < p → p < 2 → SignType.sign (localD2 p) = SignType.sign (localF p)) :=
  GKSharp.Proofs.Q15Contact.q15_sec4b_T_sign_proved p

/-- short_v3.70/sec4b_failure.tex:30 "The sign of $\partial_y\log|w|$ is the sign of $1+\lambda-c_0(r+\lambda/r)$: it is
negative, positive, negative across the two positive roots. Thus the smaller root is a minimum and the larger a maximum.
Since $1+\lambda-\sigma<0$, the quadratic $r^2-\sigma r+\lambda$ is negative at $r=1$, placing $1$ between the roots"
(`0 < λ < 1`; on the ray `t = θ₀`, `ζ = e^{y+iθ₀}`, `r = e^y`; the roots are `λ/r_*` and `r_*`). -/
theorem q15_sec4b_ray_signs (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ioo (0 : ℝ) 1) :
    let f := fun y : ℝ => Real.log ‖mobContact lam (zeta y (theta p))‖
    let r₁ := lam / rContact p lam
    let r₂ := rContact p lam
    (∀ y : ℝ, SignType.sign (deriv f y) =
      SignType.sign (1 + lam - cs p * (Real.exp y + lam / Real.exp y))) ∧
    0 < r₁ ∧ r₁ < 1 ∧ 1 < r₂ ∧
    r₁ + lam / r₁ = sigmaContact p lam ∧ r₂ + lam / r₂ = sigmaContact p lam ∧
    (∀ r : ℝ, 0 < r → r < r₁ → 1 + lam - cs p * (r + lam / r) < 0) ∧
    (∀ r : ℝ, r₁ < r → r < r₂ → 0 < 1 + lam - cs p * (r + lam / r)) ∧
    (∀ r : ℝ, r₂ < r → 1 + lam - cs p * (r + lam / r) < 0) ∧
    IsLocalMin f (Real.log r₁) ∧ IsLocalMax f (Real.log r₂) ∧
    1 + lam - sigmaContact p lam < 0 ∧ (1 : ℝ) ^ 2 - sigmaContact p lam * 1 + lam < 0 :=
  GKSharp.Proofs.Q15Contact.q15_sec4b_ray_signs_proved p lam hp hp2 hlam

/-- short_v3.70/sec4b_failure.tex:68 "Write $X=r^2$ and $\delta=1-\lambda$. The contact identities give
$\chi_y=X/(X-\lambda)$, $\sigma/v-p\chi_y+p/2=(1-p/2)\sigma/v$, $s_0^2v/(rD_1)=(X-1)/(X+\lambda)$. Hence
$2\lambda s_0^2v/(rD_1)+\delta=(1+\lambda)(X-\lambda)/(X+\lambda)=c_0v$, $c_0^2v^2=(1+\lambda)^2-4\lambda c_0^2$. The first
identity combines the two positive terms above into $p\delta c_0/(s_0^2v)$" (`−1 < λ < 1`; the terms are positive for
`λ > 0`). -/
theorem q15_sec4b_step6_identities (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let r := rContact p lam
    let X := r ^ 2
    let δ := 1 - lam
    let v := vContact p lam
    let D := dOne p lam
    let σ := sigmaContact p lam
    let χy := dy (chi lam) (yContact p lam) (theta p)
    χy = X / (X - lam) ∧
    σ / v - p * χy + p / 2 = (1 - p / 2) * (σ / v) ∧
    sn p ^ 2 * v / (r * D) = (X - 1) / (X + lam) ∧
    2 * lam * (sn p ^ 2 * v / (r * D)) + δ = (1 + lam) * (X - lam) / (X + lam) ∧
    (1 + lam) * (X - lam) / (X + lam) = cs p * v ∧
    cs p ^ 2 * v ^ 2 = (1 + lam) ^ 2 - 4 * lam * cs p ^ 2 ∧
    2 * p * lam * δ / (r * v * D) + p * δ ^ 2 / (sn p ^ 2 * v ^ 2) = p * δ * cs p / (sn p ^ 2 * v) ∧
    (0 < lam → 0 < 2 * p * lam * δ / (r * v * D) ∧ 0 < p * δ ^ 2 / (sn p ^ 2 * v ^ 2)) :=
  GKSharp.Proofs.Q15Contact.q15_sec4b_step6_identities_proved p lam hp hp2 hlam

/-- short_v3.70/sec4b_failure.tex:68 "Put $B_0=\delta(1+\lambda)^2/(c_0^3s_0^2v^3)>0$. Dividing
by $B_0$ then gives $e^{qy_*}\mu_*''(\theta_0)/(p\mathcal{P} B_0)=(p-1)c_0^4v^2/(1+\lambda)^2-s_0^2(1-p/2)^2$. The second identity and
$c_0^2+s_0^2=1$ now yield" the bracket of :70-72 "$(p-1)(1-4\lambda c_0^4/(1+\lambda)^2)-p^2s_0^2/4$". -/
theorem q15_sec4b_step6_normalized (p lam : ℝ) (hp : 1 < p) (hp2 : p < 2) (hlam : lam ∈ Ioo (-1 : ℝ) 1) :
    let y := yContact p lam
    let v := vContact p lam
    bZero p lam = (1 - lam) * (1 + lam) ^ 2 / (cs p ^ 3 * sn p ^ 2 * v ^ 3) ∧ 0 < bZero p lam ∧
    Real.exp (q p * y) * muSecond p lam / (p * weightP p lam y (theta p) * bZero p lam) =
      (p - 1) * cs p ^ 4 * v ^ 2 / (1 + lam) ^ 2 - sn p ^ 2 * (1 - p / 2) ^ 2 ∧
    (p - 1) * cs p ^ 4 * v ^ 2 / (1 + lam) ^ 2 - sn p ^ 2 * (1 - p / 2) ^ 2 =
      (p - 1) * (1 - 4 * lam * cs p ^ 4 / (1 + lam) ^ 2) - p ^ 2 * sn p ^ 2 / 4 :=
  GKSharp.Proofs.Q15Contact.q15_sec4b_step6_normalized_proved p lam hp hp2 hlam

/-- short_v3.70/sec4b_failure.tex:138 "Here $(C-1)/\delta=(C-s_0)/(s_0(C+1))$, by $s_0(C^2-1)=\delta(C-s_0)$; the right
side is regular at $\delta=0$" (`C = C(δ)`, the root near 1 of `s₀C² − δC − s₀(1 − δ) = 0`, any `δ < 1`). -/
theorem q15_sec4b_cDelta_quotient (p δ : ℝ) (hp : 1 < p) (hd : δ < 1) :
    sn p * (cDelta p δ ^ 2 - 1) = δ * (cDelta p δ - sn p) ∧
    0 < sn p * (cDelta p δ + 1) ∧
    (δ ≠ 0 → (cDelta p δ - 1) / δ = (cDelta p δ - sn p) / (sn p * (cDelta p δ + 1))) ∧
    ContinuousAt (fun d => (cDelta p d - sn p) / (sn p * (cDelta p d + 1))) 0 :=
  GKSharp.Proofs.Q15Contact.q15_sec4b_cDelta_quotient_proved p δ hp hd

/-- short_v3.70/sec5d_monotone.tex:20 "The identities $\lambda r=-\sin(\gamma-a)/\sin(\gamma+a)$,
$s_2-rs_1=\sin(\gamma+a)\sin2b/\sin(\gamma+b)$, $|1+\lambda z_\theta|=\sin2a/\sin(\gamma+a)$ follow from (5.9), the
formula for $r$, and the sine addition formulas; the last identity follows by squaring, since both sides are positive"
(`a = θ/2`, `b = εa`, `ε = p − 1`, `s₁ = sin((1−q)θ)`, `s₂ = sin(qθ)`, `q = p/2`, `r = R(θ)`). -/
theorem q15_sec5d_substitutions {p lam θ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hl : -1 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    let a := θ / 2
    let b := (p - 1) * (θ / 2)
    let γ := curveGamma p lam θ
    let r := curveR p lam θ
    lam * r = -(Real.sin (γ - a) / Real.sin (γ + a)) ∧
    Real.sin (p / 2 * θ) - r * Real.sin ((1 - p / 2) * θ) =
      Real.sin (γ + a) * Real.sin (2 * b) / Real.sin (γ + b) ∧
    ‖1 + (lam : ℂ) * curveZ p lam θ‖ = Real.sin (2 * a) / Real.sin (γ + a) ∧
    0 < Real.sin (2 * a) / Real.sin (γ + a) :=
  GKSharp.Proofs.Q15Monotone.q15_sec5d_substitutions_proved hp1 hp2 hl hl1 hθ0 hθ

/-- short_v3.70/sec5d_monotone.tex:34 "To clear the cotangents, put $U=\sin(\gamma-a)\sin(\gamma+a)=(\cos2a-X)/2$,
$V=\sin(\gamma-b)\sin(\gamma+b)=(\cos2b-X)/2$, $N=\sin2a\,V-\sin2b\,U$, $S=UV$. Cotangent sums and differences give
$SM_\gamma=N$, $SM_a=(\varepsilon U-V)\sin2\gamma$, $SL_\gamma=\tfrac12[(U-\varepsilon V)\sin2\gamma+\varepsilon N]$,
$SL_a=\tfrac\varepsilon2[(\varepsilon U-V)\sin2\gamma+N]+2\varepsilon UV(\cot2a-\cot2b)$. In $S^2\mathcal E=(SL_a)(SM_\gamma)-(SL_\gamma)(SM_a)$
the mixed terms cancel. Since $\sin^22\gamma=1-X^2$,
$\mathcal ES=[\varepsilon N^2-(U-\varepsilon V)(\varepsilon U-V)(1-X^2)]/(2UV)+2\varepsilon(\cot2a-\cot2b)N$" (any `γ ∈ (b, π/2)`,
`γ ≠ a`, i.e. `λ ≠ 0`; `X = cos 2γ`; `L_a, L_γ, M_a, M_γ` the actual partial derivatives). -/
theorem q15_sec5d_cleared {p a g : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ha0 : 0 < a) (ha : a < Real.pi / 2)
    (hg : (p - 1) * a < g ∧ g < Real.pi / 2) (hga : g ≠ a) :
    let ε := p - 1
    let b := (p - 1) * a
    let X := Real.cos (2 * g)
    let U := Real.sin (g - a) * Real.sin (g + a)
    let V := Real.sin (g - b) * Real.sin (g + b)
    let N := Real.sin (2 * a) * V - Real.sin (2 * b) * U
    let S := U * V
    U = (Real.cos (2 * a) - X) / 2 ∧ V = (Real.cos (2 * b) - X) / 2 ∧ S = monoS p a g ∧
    S * deriv (monoLogM p a) g = N ∧
    S * deriv (fun x => monoLogM p x g) a = (ε * U - V) * Real.sin (2 * g) ∧
    S * deriv (monoLogL p a) g = ((U - ε * V) * Real.sin (2 * g) + ε * N) / 2 ∧
    S * deriv (fun x => monoLogL p x g) a =
      ε / 2 * ((ε * U - V) * Real.sin (2 * g) + N) + 2 * ε * U * V * (Real.cot (2 * a) - Real.cot (2 * b)) ∧
    S ^ 2 * monoE p a g = (S * deriv (fun x => monoLogL p x g) a) * (S * deriv (monoLogM p a) g) -
      (S * deriv (monoLogL p a) g) * (S * deriv (fun x => monoLogM p x g) a) ∧
    monoE p a g * S = (ε * N ^ 2 - (U - ε * V) * (ε * U - V) * (1 - X ^ 2)) / (2 * U * V) +
      2 * ε * (Real.cot (2 * a) - Real.cot (2 * b)) * N :=
  GKSharp.Proofs.Q15Monotone.q15_sec5d_cleared_proved hp1 hp2 ha0 ha hg hga

/-- short_v3.70/sec5d_monotone.tex:35 "Since $\sin2a\sin2b(\cot2a-\cot2b)=-\sin u_3$ and $2N=\sin u_3-(\sin u_1-\sin u_2)X$,
this gives $2\sin u_1\sin u_2\,\mathcal ES=\Pi(X)$" (Lean route: the coefficients of X², X, 1 are compared directly,
not through the quadratic Π_1; as an identity in `X`, wherever `UV ≠ 0`; `ε = p − 1`, `b = εa`,
`θ = 2a`). -/
theorem q15_sec5d_Pi_coefficients {p a : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ha0 : 0 < a) (ha : a < Real.pi / 2) :
    let ε := p - 1
    let b := (p - 1) * a
    Real.sin (2 * a) * Real.sin (2 * b) * (Real.cot (2 * a) - Real.cot (2 * b)) = -Real.sin (2 * (a - b)) ∧
    ∀ X : ℝ, Real.cos (2 * a) - X ≠ 0 → Real.cos (2 * b) - X ≠ 0 →
      let U := (Real.cos (2 * a) - X) / 2
      let V := (Real.cos (2 * b) - X) / 2
      let N := Real.sin (2 * a) * V - Real.sin (2 * b) * U
      2 * Real.sin (2 * a) * Real.sin (2 * b) *
          ((ε * N ^ 2 - (U - ε * V) * (ε * U - V) * (1 - X ^ 2)) / (2 * U * V) +
            2 * ε * (Real.cot (2 * a) - Real.cot (2 * b)) * N) =
        monoPi ε (2 * a) X :=
  GKSharp.Proofs.Q15Monotone.q15_sec5d_Pi_coefficients_proved hp1 hp2 ha0 ha

/-- short_v3.70/P019_paper.tex:80 "These include the ratios of all real pairs $a,b$ with $ab\ne0$ ($|\rho|=1$, $\rho\ne\pm1$)"
(`ρ = (a + ib)/(a − ib)`); the sharp real cases ρ = ±1 are λ = 1 and λ = −1 of Theorem 1.1 (l.104: "the bound is sharp for $\lambda=1$, for $p=2$ and for $\alpha=0$"; l.100: "If $\lambda\le0$ is real"). -/
theorem q15_normcorr_real_ratio {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (P : RieszProjection p)
    (a b : ℝ) (hab : (a : ℂ) - Complex.I * b ≠ 0) :
    let ρ := ((a : ℂ) + Complex.I * b) / ((a : ℂ) - Complex.I * b)
    (ρ.im = 0 ↔ ρ = 1 ∨ ρ = -1) ∧ (ρ = 1 ↔ b = 0) ∧ (ρ = -1 ↔ a = 0) ∧
    (ρ.im = 0 → pencilNorm P ρ = gk p ρ) ∧ (gk p ρ < pencilNorm P ρ → ρ.im ≠ 0) :=
  GKSharp.Proofs.Q15Misc.q15_normcorr_real_ratio_proved hp P a b hab

/-- short_v3.70/sec4a_criterion.tex:38 "Uniqueness of the minimizing $y_*$ (Lemma 4.1) and locally uniform coercivity
(Section 2.2) imply that any nearby minimizers $y_t$ tend to $y_*$ as $t\to\theta_0$. Minimality gives
$\Gamma_C(y_t,t)-\Gamma_C(y_t,\theta_0)\le m_C(t)-m_C(\theta_0)\le\Gamma_C(y_*,t)-\Gamma_C(y_*,\theta_0)$. Dividing by
$t-\theta_0$ ... gives $m_C'(\theta_0)=\partial_t\Gamma_C(y_*,\theta_0)$"; with :37
"$K=-q^{-1}\partial_t\Gamma_C(y_*,\theta_0)=-m_C'(\theta_0)/q$" (`C = GK_p(λ)`, `θ₀ = π/p`, `y_* = log r_*`, `−1 ≤ λ < 1`). -/
theorem q15_sec2_envelope_route {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (lam : ℝ) (hlam : -1 ≤ lam ∧ lam < 1) :
    let C := gk p (lam : ℂ)
    let θ₀ := Real.pi / p
    let ystar := Real.log (contactRadius p lam)
    (∀ y : ℝ, GKSharp.gamma p C lam y θ₀ = GKSharp.obstacle p C lam θ₀ → y = ystar) ∧
    (∀ t yt : ℝ, GKSharp.gamma p C lam yt t = GKSharp.obstacle p C lam t →
      GKSharp.gamma p C lam yt t - GKSharp.gamma p C lam yt θ₀ ≤
          GKSharp.obstacle p C lam t - GKSharp.obstacle p C lam θ₀ ∧
        GKSharp.obstacle p C lam t - GKSharp.obstacle p C lam θ₀ ≤
          GKSharp.gamma p C lam ystar t - GKSharp.gamma p C lam ystar θ₀) ∧
    (∀ sel : ℝ → ℝ, (∀ᶠ t in 𝓝 θ₀, GKSharp.gamma p C lam (sel t) t = GKSharp.obstacle p C lam t) →
      Tendsto sel (𝓝 θ₀) (𝓝 ystar)) ∧
    DifferentiableAt ℝ (GKSharp.obstacle p C lam) θ₀ ∧
    deriv (GKSharp.obstacle p C lam) θ₀ = deriv (fun t => GKSharp.gamma p C lam ystar t) θ₀ ∧
    kConst p lam = -deriv (GKSharp.obstacle p C lam) θ₀ / (p / 2) :=
  GKSharp.Proofs.Q15Misc.q15_sec2_envelope_route_proved hp hp2 lam hlam

/-- short_v3.70/sec5e_cstar.tex:26 "So $(*)$ holds (at $z=-1$ by continuity)" ("If" part of Theorem 5.3, :15-25:
`1 < p < 2`, `0 < λ < 1`, `h(λ, p) ≥ 0`, `λ < λ_loc(p)`; `(*)` is `𝒟_C ≥ 0` on `ℂ`). -/
theorem q15_sec5e_star_holds {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (hh : kConst p lam ≤ GKSharp.obstacle p (gk p lam) lam 0) (hloc : lam < lambdaLoc p) :
    (∀ z : ℂ, 0 ≤ critD p (gk p lam) (kConst p lam) lam z) ∧
      0 ≤ critD p (gk p lam) (kConst p lam) lam (-1) :=
  GKSharp.Proofs.Q15Misc.q15_sec5e_star_holds_proved hp1 hp2 hl0 hl1 hh hloc

end Q15Rows

section Q19Rows
open GKSharp.Proofs.Q19Rows

/-- short_v3.70/P019_paper.tex:121 "On this subspace the constant in the displayed inequality becomes, after division by
$1+t$, $(1+t^2\tan^2(\pi/(2p)))^{1/2}/(1+t)$ ... For example, at $t=1$, that is, $\lambda=0$, the normalized constant is
$1/(2\cos(\pi/(2p)))=\sin(\pi/(2p))\,\GK_p(0)$, strictly smaller than $\GK_p(0)=1/\sin(\pi/p)$" (every `p > 1`). -/
theorem q19_intro_hkv_example {p : ℝ} (hp : 1 < p) :
    Real.sqrt (1 + 1 ^ 2 * Real.tan (Real.pi / (2 * p)) ^ 2) / (1 + 1) = 1 / (2 * Real.cos (Real.pi / (2 * p))) ∧
    1 / (2 * Real.cos (Real.pi / (2 * p))) = Real.sin (Real.pi / (2 * p)) * gk p 0 ∧
    Real.sin (Real.pi / (2 * p)) * gk p 0 < gk p 0 ∧
    gk p 0 = 1 / Real.sin (Real.pi / p) :=
  q19_intro_hkv_example_proved hp

/-- short_v3.70/sec2_obstacle.tex:42 "namely $C=\bigl((1-\lambda)+\sqrt{(1-\lambda)^2+4\lambda s_0^2}\bigr)/(2s_0)$"
(`C = GK_p(λ)` the larger root of (2.2), `s₀ = sin(π/p)`; here for every `p > 1` and every `λ < 1`, with the
radicand nonnegative). -/
theorem q19_sec2_gk_explicit {p : ℝ} (hp : 1 < p) {lam : ℝ} (hlam : lam < 1) :
    0 ≤ (1 - lam) ^ 2 + 4 * lam * Real.sin (Real.pi / p) ^ 2 ∧
    gk p lam = ((1 - lam) + Real.sqrt ((1 - lam) ^ 2 + 4 * lam * Real.sin (Real.pi / p) ^ 2)) /
      (2 * Real.sin (Real.pi / p)) :=
  q19_sec2_gk_explicit_proved hp hlam

/-- short_v3.70/sec2_obstacle.tex:69 "indeed $f(x)=\varphi(x/q)$ satisfies $f''+f=q^{-2}(\varphi''+q^2\varphi)(x/q)$"
(here for twice-differentiable `φ` and every `q ≠ 0`; the comparison with [HKV, (3.1)] in the same sentence is context). -/
theorem q19_sec2_rescale {q : ℝ} (hq : q ≠ 0) {φ : ℝ → ℝ} (hφ1 : Differentiable ℝ φ)
    (hφ2 : Differentiable ℝ (deriv φ)) (x : ℝ) :
    deriv (deriv (fun y => φ (y / q))) x + φ (x / q) =
      (q ^ 2)⁻¹ * (deriv (deriv φ) (x / q) + q ^ 2 * φ (x / q)) :=
  q19_sec2_rescale_proved hq hφ1 hφ2 x

/-- short_v3.70/sec5d_monotone.tex:35 (proof of Lemma 5.7 (label signformula), `ε = p − 1`, `b = εa`, `θ = 2a`,
`u₁ = 2a`, `u₂ = 2b`, `u₃ = 2(a − b)`, `X = cos 2γ`, `U, V` the affine forms, `N = sin2a V − sin2b U`):
"Write the first term as $\Pi_1(X)/2$, where $\Pi_1:=[\varepsilon N^2-(U-\varepsilon V)(\varepsilon U-V)(1-X^2)]/(UV)$.
Its numerator vanishes where $U=0$ and where $V=0$: there $1-X^2$ equals $\sin^22a$, respectively $\sin^22b$, and $N$
equals $V\sin2a$, respectively $-U\sin2b$. So $\Pi_1$ is a quadratic polynomial in $X$. Its leading coefficient is
$-(1-\varepsilon)^2$, and at $X=\pm1$ one finds $\Pi_1(\pm1)=4\varepsilon\sin^2(a-b)=2\varepsilon(1-\cos u_3)$. Hence
$\Pi_1(X)=-(1-\varepsilon)^2X^2+1+\varepsilon^2-2\varepsilon\cos u_3$"; "$2N=\sin u_3-(\sin u_1-\sin u_2)X$". -/
theorem q19_sec5d_q_closed {p a : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ha0 : 0 < a) (ha : a < Real.pi / 2) :
    let ε := p - 1
    let b := (p - 1) * a
    let U := fun X : ℝ => (Real.cos (2 * a) - X) / 2
    let V := fun X : ℝ => (Real.cos (2 * b) - X) / 2
    let N := fun X : ℝ => Real.sin (2 * a) * V X - Real.sin (2 * b) * U X
    let num := fun X : ℝ => ε * N X ^ 2 - (U X - ε * V X) * (ε * U X - V X) * (1 - X ^ 2)
    let q := fun X : ℝ => num X / (U X * V X)
    (num (Real.cos (2 * a)) = 0 ∧ 1 - Real.cos (2 * a) ^ 2 = Real.sin (2 * a) ^ 2 ∧
      N (Real.cos (2 * a)) = V (Real.cos (2 * a)) * Real.sin (2 * a)) ∧
    (num (Real.cos (2 * b)) = 0 ∧ 1 - Real.cos (2 * b) ^ 2 = Real.sin (2 * b) ^ 2 ∧
      N (Real.cos (2 * b)) = -(U (Real.cos (2 * b)) * Real.sin (2 * b))) ∧
    (∀ X : ℝ, U X ≠ 0 → V X ≠ 0 →
      q X = -(1 - ε) ^ 2 * X ^ 2 + 1 + ε ^ 2 - 2 * ε * Real.cos (2 * (a - b))) ∧
    q 1 = 4 * ε * Real.sin (a - b) ^ 2 ∧ q (-1) = 4 * ε * Real.sin (a - b) ^ 2 ∧
    4 * ε * Real.sin (a - b) ^ 2 = 2 * ε * (1 - Real.cos (2 * (a - b))) ∧
    ∀ X : ℝ, 2 * N X = Real.sin (2 * (a - b)) - (Real.sin (2 * a) - Real.sin (2 * b)) * X :=
  q19_sec5d_q_closed_proved hp1 hp2 ha0 ha

/-- short_v3.70/sec5d_monotone.tex:55 (proof of Lemma 5.8 (label onevar), before (5.10)): "for the constant term,
$\sin^2u_3=\sin^2u_1+\sin^2u_2-2\sin u_1\sin u_2\cos u_3$" (`u₃ = u₁ − u₂`; for all real `u₁, u₂`). -/
theorem q19_sec5d_constant_term (u₁ u₂ : ℝ) :
    Real.sin (u₁ - u₂) ^ 2 =
      Real.sin u₁ ^ 2 + Real.sin u₂ ^ 2 - 2 * Real.sin u₁ * Real.sin u₂ * Real.cos (u₁ - u₂) :=
  q19_sec5d_constant_term_proved u₁ u₂

/-- short_v3.70/sec5d_monotone.tex:18 "Write $D=(rs_2-s_1)+\lambda r(s_2-rs_1)$. With $r=\sin(\gamma-b)/\sin(\gamma+b)$,
product-to-sum gives $s_1-rs_2=\sin2b\,\sin(a-\gamma)/\sin(\gamma+b)$ and $s_2-rs_1=\sin2b\,\sin(\gamma+a)/\sin(\gamma+b)$"
(`a = θ/2`, `b = (p − 1)a`, `s₁ = sin(a − b)`, `s₂ = sin(a + b)`, `D = D(θ, r)` of (5.3); wherever `sin(γ + b) ≠ 0`). -/
theorem q20_sec5d_D_split (p lam θ γ : ℝ) (hplus : Real.sin (γ + (p - 1) * (θ / 2)) ≠ 0) :
    let a := θ / 2
    let b := (p - 1) * (θ / 2)
    let r := Real.sin (γ - b) / Real.sin (γ + b)
    curveD p lam θ r = (r * Real.sin (a + b) - Real.sin (a - b)) +
        lam * r * (Real.sin (a + b) - r * Real.sin (a - b)) ∧
    Real.sin (a - b) - r * Real.sin (a + b) = Real.sin (2 * b) * Real.sin (a - γ) / Real.sin (γ + b) ∧
    Real.sin (a + b) - r * Real.sin (a - b) = Real.sin (2 * b) * Real.sin (γ + a) / Real.sin (γ + b) :=
  q20_sec5d_D_split_proved p lam θ γ hplus

end Q19Rows

section FinalRows
open Set GKSharp.Threshold GKSharp.ComputerChecked

/-- short_v3.70/sec4b_failure.tex:115 "For $1<p<p_0$ let $(0,\lambda_1(p)]$ be the largest interval of the form
$(0,\lambda]$ on which $h(\cdot,p)\ge0$. It exists, and $\lambda_1(p)<1$"; P019_paper.tex:106 "with $\lambda_1(p)<1$, and
$\lambda_1(p)<\lambda_{\mathrm{loc}}(p)$ when $p<p_c$ (Propositions~\ref{prop:F} and~\ref{prop:edge}). So the bound is
sharp for $0<\lambda\le\lambda_1(p)$" (the largest interval: `λ₁` is the greatest `λ ∈ (0, 1)` with `h(·, p) ≥ 0` on
`(0, λ]`; given the computer checks of Propositions 4.3, 4.7, 5.14 and Lemma 4.6); caption of Figure 1,
P019_paper.tex:113 "The bound is sharp on and below the lower curve $\lambda=\lambda_1(p)$, defined for $p<p_0$
(Section~\ref{subsec:second})" (for `0 < λ ≤ λ₁(p)`; the clause "for every $\lambda$ when $p_0\le p<2$" is the link
`cover_q17_intro_regime_sharp`). -/
theorem sec4_lambda1_interval (hn : CheckOmegaNeg) (hr : CheckOmegaRoot) (hc : CheckLocalF)
    (hb : CheckBoundaryBulk) (hs : CheckBoundarySliver) {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (P : RieszProjection p) (hp1 : 1 < p) (hpp0 : p < p0) :
    ∃ lam1 : ℝ, IsGreatest {lam : ℝ | 0 < lam ∧ lam < 1 ∧ ∀ mu ∈ Ioc 0 lam, 0 ≤ h p mu} lam1 ∧
      (p < pc → lam1 < lambdaLoc p) ∧ ∀ lam ∈ Ioc 0 lam1, pencilNorm P lam = gk p lam :=
  GKSharp.Proofs.FinalRows.sec4_lambda1_interval_proved hn hr hc hb hs P hp1 hpp0

/-- Lemma 4.6(b) (label Pc), short_v3.70/sec4b_failure.tex:95 "For $0<\lambda<1$ the left side of \eqref{eq:localfail}
is less than $1$, equal to $1$ or greater than $1$ according as $\lambda<\lambda_{\mathrm{loc}}(p)$,
$\lambda=\lambda_{\mathrm{loc}}(p)$ or $\lambda>\lambda_{\mathrm{loc}}(p)$. Moreover $0<\lambda_{\mathrm{loc}}(p)\le1$"
(`1 < p < 2`; the left side of (4.2) is `localTest p λ`). -/
theorem sec4_lemma_Pc_b (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    (∀ lam ∈ Ioo (0 : ℝ) 1, (localTest p lam < 1 ↔ lam < lambdaLoc p) ∧
      (localTest p lam = 1 ↔ lam = lambdaLoc p) ∧ (1 < localTest p lam ↔ lambdaLoc p < lam)) ∧
    0 < lambdaLoc p ∧ lambdaLoc p ≤ 1 :=
  GKSharp.Proofs.FinalRows.sec4_lemma_Pc_b_proved p hp hp2

/-- Proof of Theorem 5.3 (label Cstar), "If", short_v3.70/sec5e_cstar.tex:15-17: "At $\theta=\theta_0$ we have
$m\omega=q\theta_0=\pi/2$ and $\sin\omega=c_0$, so $\Psi_m(\omega)=(m^2c_0^2-1)/c_0^4$. Since $m^2/(m^2-1)=pp'/4$ and
$1/(m^2-1)=pp'/4-1$, \[ \frac{\Psi_m(\omega)}{m^2-1}=\frac{1-(pp'/4)s_0^2}{c_0^4} , \] so
$\Psi_m(\omega)>4(m^2-1)\lambda/(1+\lambda)^2$ is equivalent to $(pp'/4)s_0^2+4\lambda c_0^4/(1+\lambda)^2<1$"
(`1 < p < 2`, `λ > −1`, `m = p/(2 − p)`, `q = p/2`, `ω = (1 − q)θ₀`, `θ₀ = π/p`, `s₀ = sn p`, `c₀ = cs p`). -/
theorem sec5e_routeB_identities {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl : -1 < lam) :
    p / (2 - p) * ((1 - p / 2) * (Real.pi / p)) = Real.pi / 2 ∧ p / 2 * (Real.pi / p) = Real.pi / 2 ∧
    Real.sin ((1 - p / 2) * (Real.pi / p)) = cs p ∧
    monoPsi (p / (2 - p)) ((1 - p / 2) * (Real.pi / p)) = ((p / (2 - p)) ^ 2 * cs p ^ 2 - 1) / cs p ^ 4 ∧
    (p / (2 - p)) ^ 2 / ((p / (2 - p)) ^ 2 - 1) = p * dual p / 4 ∧
    1 / ((p / (2 - p)) ^ 2 - 1) = p * dual p / 4 - 1 ∧
    monoPsi (p / (2 - p)) ((1 - p / 2) * (Real.pi / p)) / ((p / (2 - p)) ^ 2 - 1) =
      (1 - p * dual p / 4 * sn p ^ 2) / cs p ^ 4 ∧
    (4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 < monoPsi (p / (2 - p)) ((1 - p / 2) * (Real.pi / p)) ↔
      localTest p lam < 1) :=
  GKSharp.Proofs.FinalRows.sec5e_routeB_identities_proved hp1 hp2 hl

/-- Proof of Theorem 5.3 (label Cstar), "If", short_v3.70/sec5e_cstar.tex:15: "Assume $h(\lambda, p) \ge 0$ and
$\lambda < \lambda_{\mathrm{loc}}(p)$. By Lemma~\ref{lem:Pc}(b), the left side of \eqref{eq:localfail} is less than $1$.
We first show that $K_f'(\theta_0)<0$." and l.17 "Lemma~\ref{lem:onevar} therefore gives $K_f'(\theta_0)<0$"
(`1 < p < 2`, `0 < λ < 1`, `θ₀ = π/p`; the row does not need `h(λ, p) ≥ 0`). -/
theorem sec5e_Kf_slope_routeB {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hloc : lam < lambdaLoc p) : deriv (curveKf p lam) (Real.pi / p) < 0 :=
  GKSharp.Proofs.FinalRows.sec5e_Kf_slope_routeB_proved hp1 hp2 hl0 hl1 hloc

/-- Proposition 4.3 (label F), proof, short_v3.70/sec4a_criterion.tex:94: "By Jordan's inequality $s_0 \ge 2(p-1)/p$, so
$s_0^{p-1}\ge(p-1)^{p-1}\ge0.001^{0.001}>0.9931$, since $x^x$ decreases on $(0,1/e)$" (the range `1 < p ≤ 1.001`, that
is `0 < p − 1 ≤ 0.001`; `s₀ = sn p`; the row states that `x^x` decreases on `(0, 1/e]`). -/
theorem sec4_omega_endpoint_chain {p : ℝ} (hp : 1 < p) (hhi : p - 1 ≤ 1 / 1000) :
    2 * (p - 1) / p ≤ sn p ∧ (p - 1) ^ (p - 1) ≤ sn p ^ (p - 1) ∧
    (1 / 1000 : ℝ) ^ (1 / 1000 : ℝ) ≤ (p - 1) ^ (p - 1) ∧
    (9931 / 10000 : ℝ) < (1 / 1000 : ℝ) ^ (1 / 1000 : ℝ) ∧
    AntitoneOn (fun x : ℝ => x ^ x) (Ioc 0 (Real.exp (-1))) :=
  GKSharp.Proofs.FinalRows.sec4_omega_endpoint_chain_proved hp hhi

end FinalRows

end GKSharp.Paper
