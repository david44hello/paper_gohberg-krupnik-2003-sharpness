/- generic largest homogeneous subharmonic minorant.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.Envelope
open Real Metric Set Filter Topology MeasureTheory
namespace GKSharp.ColeHom

/-! ### Dilations and circle averages -/

theorem circleMap_mul (r : ℝ) (a : ℂ) (ρ θ : ℝ) :
    (r : ℂ) * circleMap a ρ θ = circleMap ((r : ℂ) * a) (r * ρ) θ := by
  simp only [circleMap, Complex.ofReal_mul]; ring

theorem circleAverage_dilate (f : ℂ → ℝ) (r : ℝ) (a : ℂ) (ρ : ℝ) :
    circleAverage (fun z => f ((r : ℂ) * z)) a ρ = circleAverage f ((r : ℂ) * a) (r * ρ) := by
  simp only [circleAverage_def, circleMap_mul]

theorem circleIntegrable_dilate {f : ℂ → ℝ} {r : ℝ} {a : ℂ} {ρ : ℝ}
    (h : CircleIntegrable f ((r : ℂ) * a) (r * ρ)) : CircleIntegrable (fun z => f ((r : ℂ) * z)) a ρ := by
  unfold CircleIntegrable at h ⊢
  simpa only [circleMap_mul] using h

theorem circleIntegrable_max_const {f : ℂ → ℝ} {a : ℂ} {ρ : ℝ} (h : CircleIntegrable f a ρ) (t : ℝ) :
    CircleIntegrable (fun z => max (f z) t) a ρ := by
  unfold CircleIntegrable at h ⊢
  have hc : IntervalIntegrable (fun _ : ℝ => t) volume 0 (2 * π) := intervalIntegrable_const
  exact ⟨Integrable.sup h.1 hc.1, Integrable.sup h.2 hc.2⟩

/-- A real-level truncation `max(w, -t)` of a sub-mean function is sub-mean. -/
theorem max_const_submean {w : ℂ → ℝ} {b : ℂ} {R t : ℝ} (hint : CircleIntegrable w b R)
    (hsub : w b ≤ circleAverage w b R) : max (w b) (-t) ≤ circleAverage (fun z => max (w z) (-t)) b R := by
  have hint' := circleIntegrable_max_const hint (-t)
  have h1 : circleAverage w b R ≤ circleAverage (fun z => max (w z) (-t)) b R :=
    circleAverage_mono hint hint' (fun z _ => le_max_left _ _)
  have h2 : -t ≤ circleAverage (fun z => max (w z) (-t)) b R := by
    have := circleAverage_mono (circleIntegrable_const (-t) b R) hint' (fun z _ => le_max_right _ _)
    rwa [circleAverage_const] at this
  exact max_le (hsub.trans h1) h2

/-! ### Scaling: `c · V(r ·)` is subharmonic (`c, r > 0`) -/

theorem ereal_cmul_ne_top {c : ℝ} (hc : 0 < c) {x : EReal} (hx : x ≠ ⊤) : (c : EReal) * x ≠ ⊤ := by
  induction x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hc]; exact bot_ne_top
  | coe y => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  | top => exact absurd rfl hx

theorem continuous_cmul {c : ℝ} (hc : 0 < c) : Continuous (fun x : EReal => (c : EReal) * x) := by
  have hc0 : (c : EReal) ≠ 0 := by exact_mod_cast hc.ne'
  rw [continuous_iff_continuousAt]
  intro x
  have h := EReal.continuousAt_mul (p := ((c : EReal), x)) (Or.inl hc0) (Or.inl hc0)
    (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))
  exact h.comp (continuous_const.prodMk continuous_id).continuousAt

theorem monotone_cmul {c : ℝ} (hc : 0 < c) : Monotone (fun x : EReal => (c : EReal) * x) :=
  fun _ _ h => mul_le_mul_of_nonneg_left h (by exact_mod_cast hc.le)

theorem trunc_bot (m : ℕ) : potentialTrunc m (⊥ : EReal) = -(m : ℝ) := by
  unfold potentialTrunc
  rw [max_eq_right bot_le, show (-(m : EReal)) = ((-(m : ℝ) : ℝ) : EReal) by simp, EReal.toReal_coe]

/-- `potentialTrunc n (c x) = c · max(potentialTrunc N x, -n/c)` when `N ≥ n/c`. -/
theorem trunc_cmul {c : ℝ} (hc : 0 < c) {x : EReal} (hx : x ≠ ⊤) (n N : ℕ) (hN : (n : ℝ) / c ≤ N) :
    potentialTrunc n ((c : EReal) * x) = c * max (potentialTrunc N x) (-((n : ℝ) / c)) := by
  induction x using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hc, trunc_bot, trunc_bot, max_eq_right (by linarith)]
    field_simp
  | coe y =>
    rw [← EReal.coe_mul, SubharmonicBasic.trunc_coe, SubharmonicBasic.trunc_coe, max_assoc,
      max_eq_right (show -(N : ℝ) ≤ -((n : ℝ) / c) by linarith), mul_max_of_nonneg _ _ hc.le]
    congr 1
    field_simp
  | top => exact absurd rfl hx

theorem scale_subharmonic {V : ℂ → EReal} (hV : IsSubharmonic V) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    IsSubharmonic (fun ζ => (c : EReal) * V ((r : ℂ) * ζ)) := by
  refine ⟨fun z => ereal_cmul_ne_top hc (hV.1 _), ?_, ?_⟩
  · have hu : UpperSemicontinuous (fun ζ => V ((r : ℂ) * ζ)) := fun ζ =>
      (hV.2.1 ((r : ℂ) * ζ)).comp (continuous_const.mul continuous_id).continuousAt
    exact (continuous_cmul hc).comp_upperSemicontinuous hu (monotone_cmul hc)
  · intro n a ρ hρ
    obtain ⟨N, hN⟩ := exists_nat_ge ((n : ℝ) / c)
    have hrep : ∀ z, potentialTrunc n ((c : EReal) * V ((r : ℂ) * z)) =
        c * max (potentialTrunc N (V ((r : ℂ) * z))) (-((n : ℝ) / c)) :=
      fun z => trunc_cmul hc (hV.1 _) n N hN
    simp only [hrep]
    have hint : CircleIntegrable (fun z => potentialTrunc N (V z)) ((r : ℂ) * a) (r * ρ) := Envelope.trunc_circleIntegrable hV N _ _
    have hsub : potentialTrunc N (V ((r : ℂ) * a)) ≤ circleAverage (fun z => potentialTrunc N (V z)) ((r : ℂ) * a) (r * ρ) :=
      hV.2.2 N _ _ (by positivity)
    have hint2 := circleIntegrable_dilate hint
    have hsub2 : potentialTrunc N (V ((r : ℂ) * a)) ≤ circleAverage (fun z => potentialTrunc N (V ((r : ℂ) * z))) a ρ := by
      rw [circleAverage_dilate (fun z => potentialTrunc N (V z))]; exact hsub
    have hm := max_const_submean (t := (n : ℝ) / c) hint2 hsub2
    have hsm : circleAverage (fun z => c * max (potentialTrunc N (V ((r : ℂ) * z))) (-((n : ℝ) / c))) a ρ =
        c * circleAverage (fun z => max (potentialTrunc N (V ((r : ℂ) * z))) (-((n : ℝ) / c))) a ρ := by
      simp only [← smul_eq_mul]; exact circleAverage_fun_smul
    rw [hsm]
    exact mul_le_mul_of_nonneg_left hm hc.le

/-! ### Upper regularization -/

theorem le_uscRegC (u : ℂ → EReal) (z : ℂ) : u z ≤ uscRegC u z := by
  unfold uscRegC
  exact le_iInf fun ε => le_iSup₂_of_le z (mem_ball_self ε.2) le_rfl

theorem uscRegC_le {u : ℂ → EReal} {F : ℂ → ℝ} (hF : Continuous F) (hle : ∀ z, u z ≤ (F z : EReal)) (z : ℂ) :
    uscRegC u z ≤ (F z : EReal) := by
  rw [← EReal.le_of_forall_lt_iff_le]
  intro b hb
  have hb' : F z < b := EReal.coe_lt_coe_iff.mp hb
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp hF.continuousAt (b - F z) (by linarith)
  unfold uscRegC
  refine (iInf_le _ ⟨ε, hε⟩).trans ?_
  refine iSup₂_le fun y hy => (hle y).trans ?_
  have h := hball (mem_ball.mp hy)
  rw [Real.dist_eq] at h
  exact EReal.coe_le_coe_iff.mpr (by linarith [le_abs_self (F y - F z)])

theorem locUnif_of_le {ι : Type} (u : ι → ℂ → EReal) {F : ℂ → ℝ} (hF : Continuous F)
    (hle : ∀ i z, u i z ≤ (F z : EReal)) : LocUnifBddAboveC u := by
  intro z
  obtain ⟨B, hB⟩ := (isCompact_closedBall z 1).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨1, one_pos, B, fun i y hy => (hle i y).trans (EReal.coe_le_coe_iff.mpr ?_)⟩
  have h := hB y (ball_subset_closedBall hy)
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h


/-- The paper's own envelope and dilation argument. The supplied minorant is
exactly the existence conclusion of the external Cole theorem; this lemma does not assume homogeneity or maximality. -/
theorem largest_homogeneous_minorant {F : ℂ → ℝ} (hFc : Continuous F) {q : ℝ}
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → F ((r : ℂ) * z) = r ^ q * F z)
    (hbase : ∃ v : ℂ → EReal, IsSubharmonic v ∧ (∀ z, v z ≤ (F z : EReal)) ∧ 0 ≤ v 0) :
    ∃ V : ℂ → EReal, IsSubharmonic V ∧ (∀ z, V z ≤ (F z : EReal)) ∧ 0 ≤ V 0 ∧
      (∀ (t : ℝ) (z : ℂ), 0 < t → V ((t : ℂ) * z) = ((t ^ q : ℝ) : EReal) * V z) ∧
      (∀ u : ℂ → EReal, IsSubharmonic u → (∀ z, u z ≤ (F z : EReal)) → ∀ z, u z ≤ V z) := by
  obtain ⟨v0, hv0, hv0F, hv00⟩ := hbase
  set Fe : ℂ → EReal := fun z => (F z : EReal) with hFe
  -- the family of all subharmonic minorants of `F`, its upper envelope and the regularization `V`
  let S := {v : ℂ → EReal // IsSubharmonic v ∧ ∀ z, v z ≤ Fe z}
  set V : ℂ → EReal := uscRegC (fun z => ⨆ v : S, v.1 z) with hV
  have hVsh : IsSubharmonic V := Envelope.demailly_4_24 (fun v : S => v.1) (fun v => v.2.1)
    (locUnif_of_le _ hFc (fun v z => v.2.2 z))
  have hVF : ∀ z, V z ≤ Fe z := uscRegC_le hFc (fun z => iSup_le fun v => v.2.2 z)
  have hge : ∀ v : S, ∀ z, v.1 z ≤ V z := fun v z => (le_iSup (fun v : S => v.1 z) v).trans (le_uscRegC (fun z => ⨆ v : S, v.1 z) z)
  have hV0 : 0 ≤ V 0 := hv00.trans (hge ⟨v0, hv0, hv0F⟩ 0)
  -- `r^{-q} V(r·)` is again a subharmonic minorant, hence `≤ V`
  have hscale : ∀ r : ℝ, 0 < r → ∀ ζ, ((r ^ (-q) : ℝ) : EReal) * V ((r : ℂ) * ζ) ≤ V ζ := by
    intro r hr ζ
    have hW : IsSubharmonic (fun ζ => ((r ^ (-q) : ℝ) : EReal) * V ((r : ℂ) * ζ)) :=
      scale_subharmonic hVsh (by positivity) hr
    have hWF : ∀ z, ((r ^ (-q) : ℝ) : EReal) * V ((r : ℂ) * z) ≤ Fe z := by
      intro z
      have h1 := SubharmonicBasic.ereal_mul_le (by positivity : 0 < r ^ (-q)) (hVF ((r : ℂ) * z))
      refine h1.trans (le_of_eq ?_)
      simp only [hFe]
      rw [hhom r z hr, ← mul_assoc, ← rpow_add hr, neg_add_cancel, rpow_zero, one_mul]
    exact hge ⟨_, hW, hWF⟩ ζ
  refine ⟨V, hVsh, hVF, hV0, ?_, ?_⟩
  · intro t z ht
    have h1 := hscale t ht z
    have h2 := hscale t⁻¹ (inv_pos.mpr ht) ((t : ℂ) * z)
    have e1 : ((t⁻¹ : ℝ) : ℂ) * ((t : ℂ) * z) = z := by
      rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one, one_mul]
    have e2 : (t⁻¹) ^ (-q) = t ^ q := by rw [inv_rpow ht.le, rpow_neg ht.le, inv_inv]
    rw [e1, e2] at h2
    refine le_antisymm ?_ h2
    have h0 : (0 : EReal) ≤ ((t ^ q : ℝ) : EReal) := by exact_mod_cast rpow_nonneg ht.le q
    have h3 := mul_le_mul_of_nonneg_left h1 h0
    rwa [← mul_assoc, ← EReal.coe_mul, ← rpow_add ht, add_neg_cancel, rpow_zero, EReal.coe_one, one_mul] at h3
  
  
  · intro u hu hUF z
    exact hge ⟨u, hu, hUF⟩ z

end GKSharp.ColeHom
