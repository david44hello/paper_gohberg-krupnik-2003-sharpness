/- Lemma U assembly, frozen sec5d_monotone.tex:84-110 (rows lemma_U, sec5d_U_initial_interval,
sec5d_U_terminal_decrease; types verbatim from the proposal v020). CONDITIONAL for the K_f parts: premise-style
on the open row lemma_onevar (premise type OnevarHyp = its exact type).
Route = the text: Ψ_m = Σ β_n tⁿ with β_n > 0 and t = sin²α strictly increasing, so φ(θ) = Ψ_m((1-p/2)θ) is strictly
increasing on (0,π); K_f' has the sign of c - φ (c = 4(m²-1)λ/(1+λ)²). At θ = π, α = π/(m+1) and Ψ_m > m²-1 > c
(endpoint row), so by continuity φ > c near π. The turning point is θ_λ = sup {θ : φ(θ) < c} (the text's "the
increasing region is an initial interval"); K_f increases before it and decreases after it.
Copyright (C) Dave Goel 2026--now. -/
import GKSharp.Proofs.MonotoneUD
import GKSharp.Proofs.MonotoneBplusB

namespace GKSharp

open Filter Topology BplusB

namespace UAssembly

/-- Ψ_m is strictly increasing on (0, π/2) for 1 < m < 2 (sec5d:104-105). -/
theorem psi_strictMono {m : ℝ} (hm : 1 < m) (hm2 : m < 2) :
    StrictMonoOn (monoPsi m) (Set.Ioo 0 (Real.pi / 2)) := by
  intro x hx y hy hxy
  have hfx := sec5d_Psi_beta_series_proved hm hm2 hx.1 hx.2
  have hfy := sec5d_Psi_beta_series_proved hm hm2 hy.1 hy.2
  have ht : Real.sin x ^ 2 < Real.sin y ^ 2 := sec5d_sin_square_strictMono_proved hx hy hxy
  have ht0 : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
  refine hasSum_lt (i := 1) (fun n => ?_) ?_ hfx hfy
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht.le n) (sec5d_beta_positive_proved hm hm2 n).le
  · simp only [pow_one]
    exact mul_lt_mul_of_pos_left ht (sec5d_beta_positive_proved hm hm2 1)

theorem m_range {p : ℝ} (hp1 : 1 < p) (hp2 : p < 4 / 3) : 1 < p / (2 - p) ∧ p / (2 - p) < 2 := by
  have h2p : 0 < 2 - p := by linarith
  constructor
  · rw [lt_div_iff₀ h2p]
    linarith
  · rw [div_lt_iff₀ h2p]
    linarith

/-- The angle (1-p/2)θ lies in (0, π/2) for θ ∈ (0, π]. -/
theorem alpha_mem {p θ : ℝ} (hp1 : 1 < p) (hp2 : p < 4 / 3) (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi) :
    (1 - p / 2) * θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hpi := Real.pi_pos
  refine ⟨mul_pos (by linarith) hθ0, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hθ (show (0 : ℝ) ≤ 1 - p / 2 by linarith), mul_pos (sub_pos.mpr hp1) hpi]

/-- At θ = π the angle is π/(m+1). -/
theorem alpha_end {p : ℝ} (hp1 : 1 < p) (hp2 : p < 4 / 3) :
    (1 - p / 2) * Real.pi = Real.pi / (p / (2 - p) + 1) := by
  have h2p : 0 < 2 - p := by linarith
  have hm1 : 0 < p / (2 - p) + 1 := by linarith [(m_range hp1 hp2).1]
  have hhalf : (1 - p / 2) * (p / (2 - p)) = p / 2 := by
    rw [show 1 - p / 2 = (2 - p) / 2 by ring, div_mul_div_comm, mul_comm (2 - p) p,
      mul_div_mul_right _ _ h2p.ne']
  rw [eq_div_iff hm1.ne']
  calc (1 - p / 2) * Real.pi * (p / (2 - p) + 1) = Real.pi * ((1 - p / 2) * (p / (2 - p)) + (1 - p / 2)) := by
        ring
    _ = Real.pi := by rw [hhalf]; ring

/-- φ(θ) = Ψ_m((1-p/2)θ) is strictly increasing on (0, π). -/
theorem phi_strictMono {p : ℝ} (hp1 : 1 < p) (hp2 : p < 4 / 3) :
    StrictMonoOn (fun θ => monoPsi (p / (2 - p)) ((1 - p / 2) * θ)) (Set.Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  exact psi_strictMono (m_range hp1 hp2).1 (m_range hp1 hp2).2 (alpha_mem hp1 hp2 hx.1 hx.2.le)
    (alpha_mem hp1 hp2 hy.1 hy.2.le) (mul_lt_mul_of_pos_left hxy (by linarith))

/-- The sign of K_f' (from the premise): positive iff φ < c, negative iff φ > c. -/
theorem deriv_sign {p lam θ : ℝ} (onevar : OnevarHyp) (hp1 : 1 < p) (hp2 : p < 4 / 3)
    (hl : 0 < lam) (hl1 : lam < 1) (hθ0 : 0 < θ) (hθ : θ < Real.pi) :
    (0 < deriv (curveKf p lam) θ ↔
      monoPsi (p / (2 - p)) ((1 - p / 2) * θ) < 4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2) ∧
    (deriv (curveKf p lam) θ < 0 ↔
      4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 < monoPsi (p / (2 - p)) ((1 - p / 2) * θ)) := by
  have hsign := (onevar hp1 (by linarith) (by linarith) hl1 hθ0 hθ).2
  constructor
  · constructor
    · intro h
      exact sub_pos.mp (sign_eq_one_iff.mp (hsign.symm.trans (sign_eq_one_iff.mpr h)))
    · intro h
      exact sign_eq_one_iff.mp (hsign.trans (sign_eq_one_iff.mpr (sub_pos.mpr h)))
  · constructor
    · intro h
      exact sub_neg.mp (sign_eq_neg_one_iff.mp (hsign.symm.trans (sign_eq_neg_one_iff.mpr h)))
    · intro h
      exact sign_eq_neg_one_iff.mp (hsign.trans (sign_eq_neg_one_iff.mpr (sub_neg.mpr h)))

/-- Near θ = π, φ exceeds c (endpoint row + continuity of Ψ_m at π/(m+1)). -/
theorem exists_phi_gt {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 4 / 3) (hl : 0 < lam) (hl1 : lam < 1) :
    ∃ θs ∈ Set.Ioo 0 Real.pi, 4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 <
      monoPsi (p / (2 - p)) ((1 - p / 2) * θs) := by
  have hpi := Real.pi_pos
  obtain ⟨hm, hm2⟩ := m_range hp1 hp2
  obtain ⟨-, -, hgap, hthr⟩ := sec5d_U_endpoint_proved hm hm2 hl hl1
  have hgt : 4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 <
      monoPsi (p / (2 - p)) ((1 - p / 2) * Real.pi) := by
    rw [alpha_end hp1 hp2]
    linarith
  have hs : Real.sin ((1 - p / 2) * Real.pi) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (alpha_mem hp1 hp2 hpi le_rfl).1
      (by linarith [(alpha_mem hp1 hp2 hpi le_rfl).2])).ne'
  have hcont : ContinuousAt (fun θ => monoPsi (p / (2 - p)) ((1 - p / 2) * θ)) Real.pi := by
    unfold monoPsi
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 4 hs)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually (lt_mem_nhds hgt))
  refine ⟨max (Real.pi - ε / 2) (Real.pi / 2),
    ⟨lt_max_of_lt_right (by positivity), max_lt (by linarith) (by linarith)⟩, ?_⟩
  apply hball
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [le_max_left (Real.pi - ε / 2) (Real.pi / 2)]
  · linarith [max_lt (show Real.pi - ε / 2 < Real.pi by linarith) (show Real.pi / 2 < Real.pi by linarith)]

/-- K_f is continuous on any subset of (0, π) (from the premise's differentiability). -/
theorem kf_continuousOn {p lam : ℝ} (onevar : OnevarHyp) (hp1 : 1 < p) (hp2 : p < 4 / 3)
    (hl : 0 < lam) (hl1 : lam < 1) {s : Set ℝ} (hs : s ⊆ Set.Ioo 0 Real.pi) :
    ContinuousOn (curveKf p lam) s := fun θ hθ =>
  (onevar hp1 (by linarith) (by linarith) hl1 (hs hθ).1 (hs hθ).2).1.continuousAt.continuousWithinAt

end UAssembly

open UAssembly

/-- Row `sec5d_U_initial_interval`, premise-style on the open row `lemma_onevar`. -/
theorem sec5d_U_initial_interval_proved (onevar : OnevarHyp) {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 4 / 3)
    (hl : 0 < lam) (hl1 : lam < 1) :
    ∀ x ∈ Set.Ioo 0 Real.pi, ∀ y ∈ Set.Ioo 0 Real.pi, x < y →
      0 < deriv (curveKf p lam) y → 0 < deriv (curveKf p lam) x := by
  intro x hx y hy hxy hdy
  have hφ := phi_strictMono hp1 hp2 hx hy hxy
  have hy' := (deriv_sign onevar hp1 hp2 hl hl1 hy.1 hy.2).1.mp hdy
  exact (deriv_sign onevar hp1 hp2 hl hl1 hx.1 hx.2).1.mpr (lt_trans hφ hy')

/-- Row `sec5d_U_terminal_decrease`, premise-style on the open row `lemma_onevar`. -/
theorem sec5d_U_terminal_decrease_proved (onevar : OnevarHyp) {p lam : ℝ} (hp1 : 1 < p) (hp2 : p < 4 / 3)
    (hl : 0 < lam) (hl1 : lam < 1) :
    ∃ a ∈ Set.Ioo 0 Real.pi, StrictAntiOn (curveKf p lam) (Set.Ioo a Real.pi) := by
  obtain ⟨θs, hθs, hgt⟩ := exists_phi_gt hp1 hp2 hl hl1
  refine ⟨θs, hθs, strictAntiOn_of_deriv_neg (convex_Ioo θs Real.pi)
    (kf_continuousOn onevar hp1 hp2 hl hl1 fun θ hθ => ⟨hθs.1.trans hθ.1, hθ.2⟩) ?_⟩
  rw [interior_Ioo]
  intro θ hθ
  have hθ' : θ ∈ Set.Ioo 0 Real.pi := ⟨hθs.1.trans hθ.1, hθ.2⟩
  exact (deriv_sign onevar hp1 hp2 hl hl1 hθ'.1 hθ'.2).2.mpr
    (hgt.trans (phi_strictMono hp1 hp2 hθs hθ' hθ.1))

/-- Row `lemma_U`; its K_f part is premise-style on the open row `lemma_onevar`. -/
theorem lemma_U_proved (onevar : OnevarHyp) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 4 / 3) :
    StrictMonoOn (monoPsi (p / (2 - p))) (Set.Ioo 0 (Real.pi / 2)) ∧
    ∀ lam ∈ Set.Ioo (0 : ℝ) 1, StrictAntiOn (curveKf p lam) (Set.Ioo 0 Real.pi) ∨
      ∃ θl ∈ Set.Ioo 0 Real.pi, StrictMonoOn (curveKf p lam) (Set.Ioc 0 θl) ∧
        StrictAntiOn (curveKf p lam) (Set.Ico θl Real.pi) := by
  refine ⟨psi_strictMono (m_range hp1 hp2).1 (m_range hp1 hp2).2, fun lam hlam => ?_⟩
  obtain ⟨hl, hl1⟩ := hlam
  have hpi := Real.pi_pos
  set c := 4 * ((p / (2 - p)) ^ 2 - 1) * lam / (1 + lam) ^ 2 with hc
  set φ := fun θ => monoPsi (p / (2 - p)) ((1 - p / 2) * θ) with hφ
  have hmono : StrictMonoOn φ (Set.Ioo 0 Real.pi) := phi_strictMono hp1 hp2
  have hsgn := fun θ (hθ : θ ∈ Set.Ioo 0 Real.pi) => deriv_sign onevar hp1 hp2 hl hl1 hθ.1 hθ.2
  by_cases hT : ∃ θ ∈ Set.Ioo 0 Real.pi, φ θ < c
  · -- the increasing region {φ < c} is an initial interval (0, θl)
    right
    obtain ⟨θs, hθs, hgt⟩ := exists_phi_gt hp1 hp2 hl hl1
    obtain ⟨θ1, hθ1, hθ1c⟩ := hT
    set T := {θ | θ ∈ Set.Ioo 0 Real.pi ∧ φ θ < c} with hTdef
    have hTne : T.Nonempty := ⟨θ1, hθ1, hθ1c⟩
    have hTbdd : ∀ θ ∈ T, θ < θs := fun θ hθ => by
      by_contra hle
      rcases (not_lt.mp hle).eq_or_lt with h | h
      · subst h
        exact absurd hθ.2 (not_lt.mpr hgt.le)
      · exact absurd hθ.2 (not_lt.mpr (hgt.trans (hmono hθs hθ.1 h)).le)
    have hbdd : BddAbove T := ⟨θs, fun θ hθ => (hTbdd θ hθ).le⟩
    set θl := sSup T with hθl
    have hθ1le : θ1 ≤ θl := le_csSup hbdd ⟨hθ1, hθ1c⟩
    have hθlle : θl ≤ θs := csSup_le hTne fun θ hθ => (hTbdd θ hθ).le
    have hθlpos : 0 < θl := hθ1.1.trans_le hθ1le
    have hθllt : θl < Real.pi := hθlle.trans_lt hθs.2
    -- before θl: φ < c; after θl: φ > c
    have hbefore : ∀ θ ∈ Set.Ioo 0 θl, 0 < deriv (curveKf p lam) θ := fun θ hθ => by
      obtain ⟨θ', hθ'T, hθθ'⟩ := exists_lt_of_lt_csSup hTne hθ.2
      have hθI : θ ∈ Set.Ioo 0 Real.pi := ⟨hθ.1, hθ.2.trans hθllt⟩
      exact (hsgn θ hθI).1.mpr ((hmono hθI hθ'T.1 hθθ').trans hθ'T.2)
    have hnotT : ∀ θ ∈ Set.Ioo θl Real.pi, c ≤ φ θ := fun θ hθ => by
      by_contra hlt
      exact absurd (le_csSup hbdd ⟨⟨hθlpos.trans hθ.1, hθ.2⟩, not_le.mp hlt⟩) (not_le.mpr hθ.1)
    have hafter : ∀ θ ∈ Set.Ioo θl Real.pi, deriv (curveKf p lam) θ < 0 := fun θ hθ => by
      have hmid : (θl + θ) / 2 ∈ Set.Ioo θl Real.pi := ⟨by linarith [hθ.1], by linarith [hθ.1, hθ.2]⟩
      have hθI : θ ∈ Set.Ioo 0 Real.pi := ⟨hθlpos.trans hθ.1, hθ.2⟩
      have hmidI : (θl + θ) / 2 ∈ Set.Ioo 0 Real.pi := ⟨hθlpos.trans hmid.1, hmid.2⟩
      exact (hsgn θ hθI).2.mpr ((hnotT _ hmid).trans_lt (hmono hmidI hθI (by linarith [hθ.1])))
    refine ⟨θl, ⟨hθlpos, hθllt⟩, ?_, ?_⟩
    · exact strictMonoOn_of_deriv_pos (convex_Ioc 0 θl)
        (kf_continuousOn onevar hp1 hp2 hl hl1 fun θ hθ => ⟨hθ.1, hθ.2.trans_lt hθllt⟩)
        (by rw [interior_Ioc]; exact hbefore)
    · exact strictAntiOn_of_deriv_neg (convex_Ico θl Real.pi)
        (kf_continuousOn onevar hp1 hp2 hl hl1 fun θ hθ => ⟨hθlpos.trans_le hθ.1, hθ.2⟩)
        (by rw [interior_Ico]; exact hafter)
  · -- φ ≥ c everywhere, hence φ > c everywhere (strict increase), so K_f' < 0
    left
    have hT' : ∀ θ ∈ Set.Ioo 0 Real.pi, c ≤ φ θ := fun θ hθ => not_lt.mp fun h => hT ⟨θ, hθ, h⟩
    refine strictAntiOn_of_deriv_neg (convex_Ioo 0 Real.pi)
      (kf_continuousOn onevar hp1 hp2 hl hl1 subset_rfl) ?_
    rw [interior_Ioo]
    intro θ hθ
    have hhalf : θ / 2 ∈ Set.Ioo 0 Real.pi := ⟨by linarith [hθ.1], by linarith [hθ.1, hθ.2]⟩
    exact (hsgn θ hθ).2.mpr ((hT' _ hhalf).trans_lt (hmono hhalf hθ (by linarith [hθ.1])))

end GKSharp

