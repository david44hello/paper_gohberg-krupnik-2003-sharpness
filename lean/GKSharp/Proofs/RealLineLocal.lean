/- RealLineLocal.lean - N family: localization identities N04 and N04_minus
   (norm_correspondence.tex l.22-29, l.37).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.RealLineUnique
import GKSharp.Proofs.SchwartzPeriodization

open MeasureTheory Real Filter Topology
open scoped FourierTransform

namespace GKSharp.Proofs.RealLineLocal

open GKSharp.RealLineFourier GKSharp.Proofs.RealLineUnique GKSharp.Proofs.SchwartzPeriodization

/-- The n-th derivative of x ↦ e^{cx} on the real line is c^n e^{cx}. -/
theorem iteratedDeriv_cexp_real (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => Complex.exp (c * x)) = fun x : ℝ => c ^ n * Complex.exp (c * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h1 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul c
    rw [((h1.cexp).const_mul (c ^ n)).deriv]
    ring

/-- x ↦ e^{ibx} has temperate growth (all derivatives bounded by |b|^n). -/
theorem hasTemperateGrowth_cexp (b : ℝ) :
    (fun x : ℝ => Complex.exp (Complex.I * b * x)).HasTemperateGrowth := by
  refine ⟨(contDiff_const.mul Complex.ofRealCLM.contDiff).cexp, fun n => ⟨0, |b| ^ n, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_real]
  have h1 : ‖Complex.exp (Complex.I * b * x)‖ = 1 := by
    rw [show Complex.I * b * x = ((b * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  simp [norm_mul, norm_pow, h1]

/-- Modulation by e^{ibx}, as a Schwartz map. -/
noncomputable def modulate (b : ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => Complex.exp (Complex.I * b * x)) f

theorem modulate_apply (b : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    modulate b f x = Complex.exp (Complex.I * b * x) * f x := by
  rw [modulate, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_cexp b), smul_eq_mul]

/-- The localized piece x ↦ η(hx) e^{iax} (h > 0). -/
noncomputable def piece (η : SchwartzMap ℝ ℂ) {h : ℝ} (hh : 0 < h) (a : ℝ) : SchwartzMap ℝ ℂ :=
  dilate h hh.ne' (modulate (a / h) η)

theorem piece_apply (η : SchwartzMap ℝ ℂ) {h : ℝ} (hh : 0 < h) (a x : ℝ) :
    piece η hh a x = η (h * x) * Complex.exp (Complex.I * a * x) := by
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  rw [piece, dilate_apply, modulate_apply, mul_comm]
  congr 2
  push_cast
  field_simp

/-- The paper transform turns a modulation into a shift. -/
theorem paperFourier_modulate (b : ℝ) (f : SchwartzMap ℝ ℂ) (ζ : ℝ) :
    paperFourier (modulate b f) ζ = paperFourier f (ζ - b) := by
  unfold paperFourier
  apply integral_congr_ae
  filter_upwards [] with x
  rw [modulate_apply, mul_comm (Complex.exp _) (f x), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Mathlib Fourier transform of a piece: h⁻¹ η̂(2πξ/h - a/h) in the paper normalization. -/
theorem fourier_piece (η : SchwartzMap ℝ ℂ) {h : ℝ} (hh : 0 < h) (a ξ : ℝ) :
    𝓕 (piece η hh a) ξ = ((h⁻¹ : ℝ) : ℂ) * paperFourier η (2 * Real.pi * ξ / h - a / h) := by
  have hcoe : 𝓕 (piece η hh a) ξ = 𝓕 (fun x : ℝ => (modulate (a / h) η) (h * x)) ξ := rfl
  rw [hcoe, fourier_dilate _ hh, paperFourier_modulate]

/-- A compactly supported paper transform vanishes outside some interval [-R, R], R > 0. -/
theorem exists_paper_bound (η : SchwartzMap ℝ ℂ) (hη : HasCompactSupport (paperFourier η)) :
    ∃ R : ℝ, 0 < R ∧ ∀ ζ, R < |ζ| → paperFourier η ζ = 0 := by
  obtain ⟨R, hR⟩ := hη.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, by positivity, fun ζ hζ => ?_⟩
  by_contra hne
  have hmem := hR (subset_tsupport _ (Function.mem_support.mpr hne))
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
  linarith [le_max_left R 1]

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {α β : ℂ}

/-- A piece with frequency a > R h lies in positive frequencies: T multiplies it by α. -/
theorem map_piece_pos (hp : 1 < p) (hN10 : N10Prop) (T : RealLinePencil p α β) (η : SchwartzMap ℝ ℂ)
    {R : ℝ} (hR : ∀ ζ, R < |ζ| → paperFourier η ζ = 0) {h : ℝ} (hh : 0 < h) {a : ℝ} (ha : R * h < a) :
    T.map ((piece η hh a).toLp (ENNReal.ofReal p) volume) =
      α • (piece η hh a).toLp (ENNReal.ofReal p) volume := by
  apply map_toLp_of_fourier_pos hp hN10 T
  intro ξ hξ
  rw [fourier_piece, hR, mul_zero]
  have h1 : 2 * Real.pi * ξ / h ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.pi_pos]) hh.le
  have h2 : R < a / h := by rw [lt_div_iff₀ hh]; linarith
  exact lt_abs.mpr (Or.inr (by linarith))

/-- A piece with frequency a < -R h lies in negative frequencies: T multiplies it by β. -/
theorem map_piece_neg (hp : 1 < p) (hN10 : N10Prop) (T : RealLinePencil p α β) (η : SchwartzMap ℝ ℂ)
    {R : ℝ} (hR : ∀ ζ, R < |ζ| → paperFourier η ζ = 0) {h : ℝ} (hh : 0 < h) {a : ℝ} (ha : a < -(R * h)) :
    T.map ((piece η hh a).toLp (ENNReal.ofReal p) volume) =
      β • (piece η hh a).toLp (ENNReal.ofReal p) volume := by
  apply map_toLp_of_fourier_neg hp hN10 T
  intro ξ hξ
  rw [fourier_piece, hR, mul_zero]
  have h1 : 0 ≤ 2 * Real.pi * ξ / h := div_nonneg (by positivity) hh.le
  have h2 : R < -a / h := by rw [lt_div_iff₀ hh]; linarith
  have h3 : -a / h = -(a / h) := neg_div h a
  exact lt_abs.mpr (Or.inl (by linarith))

/-- Shared assembly: T sends Σ w_n piece(n + shift) to Σ s_n w_n piece(n + shift) when every frequency is
    separated from 0 by R h, with s_n = α on positive and β on negative frequencies. -/
theorem map_sum_pieces (hp : 1 < p) (hN10 : N10Prop) (T : RealLinePencil p α β) (η : SchwartzMap ℝ ℂ)
    {R : ℝ} (hR : ∀ ζ, R < |ζ| → paperFourier η ζ = 0) {h : ℝ} (hh : 0 < h) (S : Finset ℤ) (w s : ℤ → ℂ)
    (shift : ℝ) (hs : ∀ n ∈ S, (R * h < n + shift ∧ s n = α) ∨ ((n : ℝ) + shift < -(R * h) ∧ s n = β)) :
    T.map ((∑ n ∈ S, w n • piece η hh (n + shift)).toLp (ENNReal.ofReal p) volume) =
      (∑ n ∈ S, (s n * w n) • piece η hh (n + shift)).toLp (ENNReal.ofReal p) volume := by
  have hlin : ∀ u : SchwartzMap ℝ ℂ, u.toLp (ENNReal.ofReal p) volume =
      SchwartzMap.toLpCLM ℂ ℂ (ENNReal.ofReal p) volume u := fun u => rfl
  rw [hlin, hlin, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hY : T.map ((piece η hh (n + shift)).toLp (ENNReal.ofReal p) volume) =
      s n • (piece η hh (n + shift)).toLp (ENNReal.ofReal p) volume := by
    rcases hs n hn with ⟨hpos, hsn⟩ | ⟨hneg, hsn⟩
    · rw [hsn, map_piece_pos hp hN10 T η hR hh hpos]
    · rw [hsn, map_piece_neg hp hN10 T η hR hh hneg]
  simp only [map_smul]
  rw [← hlin, hY, smul_smul, mul_comm (s n) (w n)]

theorem schwartz_sum_apply {ι : Type*} (S : Finset ι) (f : ι → SchwartzMap ℝ ℂ) (x : ℝ) :
    (∑ i ∈ S, f i) x = ∑ i ∈ S, f i x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => simp [Finset.sum_insert hi, ih]

theorem sum_pieces_apply (η : SchwartzMap ℝ ℂ) {h : ℝ} (hh : 0 < h) (S : Finset ℤ) (w : ℤ → ℂ)
    (shift x : ℝ) :
    (∑ n ∈ S, w n • piece η hh (n + shift)) x = η (h * x) * Complex.exp (Complex.I * shift * x) *
      ∑ n ∈ S, w n * Complex.exp (((n * x : ℝ) : ℂ) * Complex.I) := by
  rw [schwartz_sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [SchwartzMap.smul_apply, piece_apply, smul_eq_mul,
    show Complex.exp (Complex.I * (((n : ℝ) + shift : ℝ) : ℂ) * (x : ℂ)) =
      Complex.exp (Complex.I * shift * x) * Complex.exp (((n * x : ℝ) : ℂ) * Complex.I) from by
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
  ring

theorem trig_eq_sum (c : ℤ →₀ ℂ) (x : ℝ) :
    trig c x = ∑ n ∈ c.support, c n * Complex.exp (((n * x : ℝ) : ℂ) * Complex.I) := by
  simp only [trig, mode, Finsupp.sum]

/-- α P₊ + β P₋ assigns α to the frequencies n ≥ 0 and β to n < 0. -/
theorem pencil_sum_eq (c : ℤ →₀ ℂ) (x : ℝ) (α β : ℂ) :
    α * Pplus c x + β * Pminus c x =
      ∑ n ∈ c.support, ((if 0 ≤ n then α else β) * c n) * Complex.exp (((n * x : ℝ) : ℂ) * Complex.I) := by
  simp only [Pminus, Pplus, trig, mode, Finsupp.sum, mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> ring

/-- With the constant-mode correction, frequency 0 moves to β: α to n > 0 and β to n ≤ 0. -/
theorem pencil_sum_eq_minus (c : ℤ →₀ ℂ) (x : ℝ) (α β : ℂ) :
    α * Pplus c x + β * Pminus c x + (β - α) * c 0 =
      ∑ n ∈ c.support, ((if 0 < n then α else β) * c n) * Complex.exp (((n * x : ℝ) : ℂ) * Complex.I) := by
  rw [pencil_sum_eq]
  have h0 : (β - α) * c 0 = ∑ n ∈ c.support,
      (if n = 0 then (β - α) * c n * Complex.exp (((n * x : ℝ) : ℂ) * Complex.I) else 0) := by
    rw [Finset.sum_ite_eq' c.support 0]
    split_ifs with hc
    · simp
    · rw [Finsupp.notMem_support_iff.mp hc, mul_zero]
  rw [h0, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · simp [hn.ne, not_le.mpr hn, not_lt.mpr hn.le]
  · simp
    ring
  · simp [hn.ne', hn.le, hn]

/-- N04 (norm_correspondence.tex l.22-29), with N10 as the explicit density input. -/
theorem slice_N04_of_N10 (hN10 : N10Prop) (hp : 1 < p) (_P : RieszProjection p) (α β : ℂ)
    (T : RealLinePencil p α β) (d : ℝ) (hd : 0 < d ∧ d < 1) (η : SchwartzMap ℝ ℂ)
    (hη : HasCompactSupport (paperFourier η)) (c : ℤ →₀ ℂ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∃ Z W : SchwartzMap ℝ ℂ,
        (∀ x, Z x = η (h * x) * Complex.exp (Complex.I * (d : ℂ) * x) * trig c x) ∧
        (∀ x, W x = η (h * x) * Complex.exp (Complex.I * (d : ℂ) * x) *
          (α * Pplus c x + β * Pminus c x)) ∧
        T.map (Z.toLp (ENNReal.ofReal p) volume) = W.toLp (ENNReal.ofReal p) volume := by
  obtain ⟨R, hR0, hR⟩ := exists_paper_bound η hη
  refine ⟨min d (1 - d) / R, div_pos (lt_min hd.1 (by linarith [hd.2])) hR0, fun h hh hlt => ?_⟩
  have hRh : R * h < min d (1 - d) := by rwa [lt_div_iff₀ hR0, mul_comm] at hlt
  refine ⟨∑ n ∈ c.support, c n • piece η hh (n + d),
    ∑ n ∈ c.support, ((if 0 ≤ n then α else β) * c n) • piece η hh (n + d),
    fun x => ?_, fun x => ?_, ?_⟩
  · rw [sum_pieces_apply, trig_eq_sum]
  · rw [sum_pieces_apply, pencil_sum_eq]
  · apply map_sum_pieces hp hN10 T η hR hh
    intro n _
    by_cases hn : 0 ≤ n
    · refine Or.inl ⟨?_, if_pos hn⟩
      have : (0 : ℝ) ≤ n := by exact_mod_cast hn
      linarith [min_le_left d (1 - d)]
    · refine Or.inr ⟨?_, if_neg hn⟩
      have : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      linarith [min_le_right d (1 - d)]

/-- N04_minus (norm_correspondence.tex l.37), with N10 as the explicit density input. -/
theorem slice_N04_minus_of_N10 (hN10 : N10Prop) (hp : 1 < p) (α β : ℂ) (T : RealLinePencil p α β)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (η : SchwartzMap ℝ ℂ)
    (hη : HasCompactSupport (paperFourier η)) (c : ℤ →₀ ℂ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∃ Z W : SchwartzMap ℝ ℂ,
        (∀ x, Z x = η (h * x) * Complex.exp (-(Complex.I * (d : ℂ) * x)) * trig c x) ∧
        (∀ x, W x = η (h * x) * Complex.exp (-(Complex.I * (d : ℂ) * x)) *
          (α * Pplus c x + β * Pminus c x + (β - α) * c 0)) ∧
        T.map (Z.toLp (ENNReal.ofReal p) volume) = W.toLp (ENNReal.ofReal p) volume := by
  obtain ⟨R, hR0, hR⟩ := exists_paper_bound η hη
  refine ⟨min d (1 - d) / R, div_pos (lt_min hd.1 (by linarith [hd.2])) hR0, fun h hh hlt => ?_⟩
  have hRh : R * h < min d (1 - d) := by rwa [lt_div_iff₀ hR0, mul_comm] at hlt
  have hexp : ∀ x : ℝ, Complex.I * ((-d : ℝ) : ℂ) * (x : ℂ) = -(Complex.I * (d : ℂ) * x) := fun x => by
    push_cast
    ring
  refine ⟨∑ n ∈ c.support, c n • piece η hh (n + -d),
    ∑ n ∈ c.support, ((if 0 < n then α else β) * c n) • piece η hh (n + -d),
    fun x => ?_, fun x => ?_, ?_⟩
  · rw [sum_pieces_apply, trig_eq_sum, hexp]
  · rw [sum_pieces_apply, pencil_sum_eq_minus, hexp]
  · apply map_sum_pieces hp hN10 T η hR hh
    intro n _
    by_cases hn : 0 < n
    · refine Or.inl ⟨?_, if_pos hn⟩
      have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith [min_le_right d (1 - d)]
    · refine Or.inr ⟨?_, if_neg hn⟩
      have : (n : ℝ) ≤ 0 := by exact_mod_cast (show n ≤ 0 by omega)
      linarith [min_le_left d (1 - d)]

end GKSharp.Proofs.RealLineLocal
