/-
GKSharp/Proofs/StripLeaves.lean — proofs of slice (b) strip rows of paper 019 (sec5f_strip.tex, calculation_certificates.tex), with the
exact types of the statement draft PROPOSAL_CHECKS_THRESHOLDS.lean (v0.80): phi_ge_one, strip_cover,
exprel_coordinate_identities, g_zero, cDelta_eq_gk, g_tail_bounds, bulk_positive (PROVED-GIVEN the two strip-bulk
Check Props, as hypotheses), sigma_core_cover.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import GKSharp.Defs.ThresholdAnalysis
import GKSharp.ComputerChecked
import GKSharp.Proofs.GKProps

namespace GKSharp.Strip

open Set GKSharp.Threshold

lemma sn_pos {p : ℝ} (hp : 1 < p) : 0 < sn p :=
  Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by linarith))
    (div_lt_self Real.pi_pos hp)

lemma cDelta_zero (p : ℝ) : cDelta p 0 = 1 := by
  simp [cDelta]

lemma exprel_of_ne {x : ℝ} (hx : x ≠ 0) : exprel x = (1 - Real.exp (-x)) / x := by
  simp [exprel, hx]

lemma one_sub_exp_neg_ne {x : ℝ} (hx : x ≠ 0) : 1 - Real.exp (-x) ≠ 0 := by
  intro h
  have h1 : Real.exp (-x) = 1 := by linarith
  rw [Real.exp_eq_one_iff] at h1
  exact hx (neg_eq_zero.1 h1)

lemma powSlope_nonneg {p c : ℝ} (hp : 0 < p) (hc : 0 < c) : 0 ≤ powSlope p c := by
  unfold powSlope
  split_ifs with h
  · exact hp.le
  · rcases lt_or_gt_of_ne h with h1 | h1
    · exact div_nonneg_of_nonpos (by linarith [Real.rpow_le_one hc.le h1.le hp.le]) (by linarith)
    · exact div_nonneg (by linarith [Real.one_le_rpow h1.le hp.le]) (by linarith)

lemma cDelta_ge_sn {p delta : ℝ} (hp : 1 < p) (hd : delta ∈ Icc (0 : ℝ) 1) : sn p ≤ cDelta p delta := by
  have hsn := sn_pos hp
  have hsn1 : sn p ≤ 1 := Real.sin_le_one _
  have hrad : 0 ≤ delta ^ 2 / (4 * sn p ^ 2) + 1 - delta := by
    have : 0 ≤ delta ^ 2 / (4 * sn p ^ 2) := by positivity
    linarith [hd.2]
  set R := Real.sqrt (delta ^ 2 / (4 * sn p ^ 2) + 1 - delta) with hR
  set b := delta / (2 * sn p) with hb
  have hr2 : R ^ 2 = b ^ 2 + 1 - delta := by
    rw [hR, Real.sq_sqrt hrad, hb]
    field_simp
    ring
  have hr0 : 0 ≤ R := Real.sqrt_nonneg _
  have hbs : b * sn p * 2 = delta := by
    rw [hb]
    field_simp
  show sn p ≤ b + R
  by_contra hlt0
  have hlt : b + R < sn p := lt_of_not_ge hlt0
  have h1 : R < sn p - b := by linarith
  have h2 : R ^ 2 < (sn p - b) ^ 2 := by
    nlinarith [mul_pos (sub_pos.2 h1) (by linarith : 0 < sn p - b + R)]
  nlinarith [h2, hr2, hbs, mul_le_mul hsn1 hsn1 hsn.le zero_le_one]

lemma tOne_nonneg {p delta : ℝ} (hp : 1 < p) (hd : delta ∈ Icc (0 : ℝ) 1) : 0 ≤ tOne p delta := by
  have hsn := sn_pos hp
  have hc := cDelta_ge_sn hp hd
  have hcpos : 0 < cDelta p delta := lt_of_lt_of_le hsn hc
  unfold tOne
  exact div_nonneg (mul_nonneg (powSlope_nonneg (by linarith) hcpos) (by linarith))
    (mul_pos hsn (by linarith)).le

lemma exprel_pos (x : ℝ) : 0 < exprel x := by
  by_cases hx : x = 0
  · simp [exprel, hx]
  rw [exprel_of_ne hx]
  rcases lt_or_gt_of_ne hx with h | h
  · have : 1 < Real.exp (-x) := Real.one_lt_exp_iff.2 (by linarith)
    exact div_pos_of_neg_of_neg (by linarith) h
  · have : Real.exp (-x) < 1 := by simpa using Real.exp_lt_exp.2 (show -x < 0 by linarith)
    exact div_pos (by linarith) h

lemma exprel_le_one {x : ℝ} (hx : 0 ≤ x) : exprel x ≤ 1 := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [exprel, ← h]
  rw [exprel_of_ne h.ne', div_le_one h]
  linarith [Real.add_one_le_exp (-x)]

lemma exprel_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : exprel b ≤ exprel a := by
  rcases eq_or_lt_of_le ha with h0 | h0
  · rw [← h0]
    simpa [exprel] using exprel_le_one (ha.trans hab)
  have hb : 0 < b := lt_of_lt_of_le h0 hab
  have key := convexOn_exp.secant_mono (a := 0) (x := -b) (y := -a) trivial trivial trivial
    (by linarith) (by linarith) (by linarith)
  rw [exprel_of_ne hb.ne', exprel_of_ne h0.ne']
  simp only [Real.exp_zero, sub_zero, div_neg] at key
  have e1 : (1 - Real.exp (-b)) / b = -((Real.exp (-b) - 1) / b) := by ring
  have e2 : (1 - Real.exp (-a)) / a = -((Real.exp (-a) - 1) / a) := by ring
  rw [e1, e2]
  linarith

lemma exprel_eta1 : 9 / 10 ≤ exprel eta1 := by
  have hl : Real.log (19 / 20) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hpos : 0 < eta1 := by unfold eta1; linarith
  have hexp : Real.exp (-eta1) = 19 / 20 := by
    rw [eta1, neg_neg, Real.exp_log (by norm_num)]
  have hle : eta1 ≤ 1 / 19 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 20 / 19 by norm_num)
    have e : eta1 = Real.log (20 / 19) := by
      rw [eta1, ← Real.log_inv]
      norm_num
    rw [e]
    linarith
  rw [exprel_of_ne hpos.ne', hexp, le_div_iff₀ hpos]
  linarith

end GKSharp.Strip

namespace GKSharp

open Set GKSharp.Threshold GKSharp.ComputerChecked GKSharp.Strip

theorem phi_ge_one_proved (p x : ℝ) (hp : 1 ≤ p) (hx : x ∈ Icc (0 : ℝ) 1) : 1 ≤ phi p x := by
  unfold phi powSlope
  split_ifs with h1
  · exact hp
  · have hy1 : 1 - x < 1 := lt_of_le_of_ne (by linarith [hx.1]) h1
    have hpow : (1 - x) ^ p ≤ 1 - x := by
      rcases eq_or_lt_of_le (show 0 ≤ 1 - x by linarith [hx.2]) with h0 | h0
      · rw [← h0, Real.zero_rpow (by linarith)]
      · calc (1 - x) ^ p ≤ (1 - x) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge h0 hy1.le hp
          _ = 1 - x := Real.rpow_one _
    rw [le_div_iff_of_neg (by linarith)]
    linarith

theorem strip_cover_proved (p delta : ℝ) (hp : p ∈ Icc p0 (317 / 250 : ℝ))
    (hp0 : a0 < p0) (hd : delta ∈ Ioo (0 : ℝ) 1) :
    (p ∈ Icc a0 b1 ∧ delta ∈ Ioc (0 : ℝ) (1 / 20)) ∨ bulkDomain p delta := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hd1, hd2⟩ := hd
  by_cases hdl : delta ≤ 1 / 20
  · by_cases hpb : p ≤ b1
    · exact Or.inl ⟨⟨by linarith, hpb⟩, hd1, hdl⟩
    · exact Or.inr (Or.inr ⟨⟨(lt_of_not_ge hpb).le, hp2⟩, hd1.le, hdl⟩)
  · exact Or.inr (Or.inl ⟨⟨by linarith, hp2⟩, (lt_of_not_ge hdl).le, hd2.le⟩)

theorem exprel_coordinate_identities_proved (p eta sigma : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hs : sigma ∈ Ioo (0 : ℝ) 1) :
    deltaEta eta = eta * exprel eta ∧
    1 - sEta eta sigma = Real.exp (-sigma * eta) * (1 - sigma) *
      exprel ((1 - sigma) * eta) / exprel eta ∧
    sEta eta sigma * phi p (sEta eta sigma * deltaEta eta) =
      p * sigma * exprel (p * sigma * eta) / exprel eta := by
  obtain ⟨hs0, hs1⟩ := hs
  by_cases he : eta = 0
  · subst he
    refine ⟨by simp [deltaEta], by simp [sEta, exprel], ?_⟩
    simp [sEta, exprel, phi, powSlope, deltaEta]
    ring
  have hse : sigma * eta ≠ 0 := mul_ne_zero hs0.ne' he
  have hce : (1 - sigma) * eta ≠ 0 := mul_ne_zero (by linarith) he
  have hpe : p * sigma * eta ≠ 0 := mul_ne_zero (mul_ne_zero (by linarith) hs0.ne') he
  have hA := one_sub_exp_neg_ne he
  have hB := one_sub_exp_neg_ne hse
  have hBC : Real.exp (-(sigma * eta)) * Real.exp (-((1 - sigma) * eta)) = Real.exp (-eta) := by
    rw [← Real.exp_add]
    ring_nf
  have hsE : sEta eta sigma = (1 - Real.exp (-(sigma * eta))) / (1 - Real.exp (-eta)) := by
    rw [sEta, exprel_of_ne hse, exprel_of_ne he]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [deltaEta, exprel_of_ne he]
    field_simp
  · rw [hsE, exprel_of_ne hce, exprel_of_ne he, neg_mul, ← hBC]
    have hA' : 1 - Real.exp (-(sigma * eta)) * Real.exp (-((1 - sigma) * eta)) ≠ 0 := by rwa [hBC]
    have h1s : (1 : ℝ) - sigma ≠ 0 := by linarith
    generalize Real.exp (-(sigma * eta)) = X at hA' ⊢
    generalize Real.exp (-((1 - sigma) * eta)) = Y at hA' ⊢
    field_simp
    ring
  · have hx : sEta eta sigma * deltaEta eta = 1 - Real.exp (-(sigma * eta)) := by
      rw [hsE, deltaEta]
      field_simp
    have hB1 : Real.exp (-(sigma * eta)) ≠ 1 := fun h => hB (by rw [h]; ring)
    have hpow : Real.exp (-(sigma * eta)) ^ p = Real.exp (-(p * sigma * eta)) := by
      rw [← Real.exp_mul]
      ring_nf
    have hB1' : Real.exp (-(sigma * eta)) - 1 ≠ 0 := sub_ne_zero.2 hB1
    rw [hx, phi, sub_sub_cancel]
    simp only [powSlope, hB1, ↓reduceIte]
    rw [hpow, hsE, exprel_of_ne hpe, exprel_of_ne he]
    field_simp
    ring

theorem g_zero_proved (p s : ℝ) (hp : 1 < p) (_hp2 : p < 2) :
    g p 0 s = omegaFirst p s - kappaZero p := by
  have hsn := (sn_pos hp).ne'
  have htOne : tOne p 0 = p * aConst p := by
    simp only [tOne, cDelta_zero, powSlope, ↓reduceIte, aConst]
    field_simp
    ring
  have hkap : kap p 0 = kappaZero p := by
    rw [kap, cDelta_zero, kappaZero]
    norm_num
    rw [Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hphi : phi p (s * 0) = p := by
    simp only [mul_zero, phi, sub_zero, powSlope, ↓reduceIte]
  rw [g, htOne, hkap, hphi, omegaFirst]
  ring

theorem cDelta_eq_gk_proved (p delta : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hd : delta ∈ Ico (0 : ℝ) 1) : cDelta p delta = gk p ((1 - delta : ℝ) : ℂ) := by
  have hsn := sn_pos hp
  rcases eq_or_lt_of_le hd.1 with h0 | h0
  · subst h0
    rw [cDelta_zero]
    norm_num
    have hsq := gk_sq_eq p 1
    have hmid : gkMid p 1 = 2 := by simp [gkMid]; norm_num
    rw [gkRootHi, hmid] at hsq
    norm_num at hsq
    have h1 := one_le_gk p 1
    rcases hsq with h | h <;> linarith
  set b := delta / (2 * sn p) with hb
  set r := Real.sqrt (delta ^ 2 / (4 * sn p ^ 2) + 1 - delta) with hr
  have hrad : 0 ≤ delta ^ 2 / (4 * sn p ^ 2) + 1 - delta := by
    have : 0 ≤ delta ^ 2 / (4 * sn p ^ 2) := by positivity
    linarith [hd.2]
  have hr2 : r ^ 2 = b ^ 2 + 1 - delta := by
    rw [hr, Real.sq_sqrt hrad, hb]
    field_simp
    ring
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hc : cDelta p delta = b + r := rfl
  obtain ⟨hgk, hmax⟩ := gk_real_eq hp (lam := 1 - delta) (by linarith)
  set C := gk p ((1 - delta : ℝ) : ℂ) with hC
  have hsnd : Real.sin (Real.pi / p) = sn p := rfl
  rw [hsnd] at hgk hmax
  -- cDelta is a root, so cDelta ≤ C
  have hroot : (1 - (1 - delta)) * (b + r) = sn p * ((b + r) ^ 2 - (1 - delta)) := by
    have e : (b + r) ^ 2 - (1 - delta) = 2 * b * (b + r) := by nlinarith [hr2]
    rw [e, hb]
    field_simp
    ring
  have hle := hmax (b + r) hroot
  -- C is a root, so C ≤ b + r
  have hCq : (C - b) ^ 2 = r ^ 2 := by
    have e : C ^ 2 - (1 - delta) = 2 * b * C := by
      rw [hb]
      field_simp
      linarith [hgk]
    nlinarith [hr2, e]
  have hge : C ≤ b + r := by nlinarith [hCq, hr0]
  rw [hc]
  linarith

theorem g_tail_bounds_proved (p delta s : ℝ) (hp : 1 < p) (_hp2 : p < 2)
    (hd : delta ∈ Icc (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    (s ≤ 1 / 20 → lowTail p delta ≤ g p delta s) ∧
    (19 / 20 ≤ s → highTail p delta ≤ g p delta s) := by
  obtain ⟨hs0, hs1⟩ := hs
  have hq : 0 < q p := by unfold q; linarith
  have hT := tOne_nonneg hp hd
  have hphi : 1 ≤ phi p (s * delta) :=
    phi_ge_one_proved p (s * delta) hp.le ⟨mul_nonneg hs0.le hd.1, by nlinarith [hd.1, hd.2]⟩
  have hss : 0 < s * (1 - s) := mul_pos hs0 (by linarith)
  have hP : 0 < (s * (1 - s)) ^ q p := Real.rpow_pos_of_pos hss _
  constructor
  · intro hsl
    have hle : (s * (1 - s)) ^ q p ≤ (1 / 20 : ℝ) ^ q p :=
      Real.rpow_le_rpow hss.le (by nlinarith) hq.le
    have key : tOne p delta / (1 / 20 : ℝ) ^ q p ≤
        (tOne p delta + s * phi p (s * delta)) / (s * (1 - s)) ^ q p :=
      calc tOne p delta / (1 / 20 : ℝ) ^ q p ≤ tOne p delta / (s * (1 - s)) ^ q p :=
            div_le_div_of_nonneg_left hT hP hle
        _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) hP.le
    unfold lowTail g
    linarith
  · intro hsh
    have hle : (s * (1 - s)) ^ q p ≤ (1 / 20 : ℝ) ^ q p :=
      Real.rpow_le_rpow hss.le (by nlinarith) hq.le
    have key : (tOne p delta + 19 / 20) / (1 / 20 : ℝ) ^ q p ≤
        (tOne p delta + s * phi p (s * delta)) / (s * (1 - s)) ^ q p :=
      calc (tOne p delta + 19 / 20) / (1 / 20 : ℝ) ^ q p
          ≤ (tOne p delta + 19 / 20) / (s * (1 - s)) ^ q p :=
            div_le_div_of_nonneg_left (by linarith) hP hle
        _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) hP.le
    unfold highTail g
    linarith

theorem bulk_positive_proved (hc : CheckStripBulkMiddle) (ht : CheckStripBulkTails)
    (p delta s : ℝ) (hp : bulkDomain p delta) (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < g p delta s := by
  have hpd : (1 < p ∧ p < 2) ∧ delta ∈ Icc (0 : ℝ) 1 := by
    rcases hp with ⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩
    · unfold a0 at h1
      exact ⟨⟨by linarith, by linarith⟩, by linarith, h4⟩
    · unfold b1 at h1
      exact ⟨⟨by linarith, by linarith⟩, h3, by linarith⟩
  obtain ⟨⟨hp1, hp2⟩, hd⟩ := hpd
  obtain ⟨hlow, hhigh⟩ := ht p delta hp
  have htail := g_tail_bounds_proved p delta s hp1 hp2 hd hs
  by_cases h1 : s ≤ 1 / 20
  · linarith [htail.1 h1]
  by_cases h2 : 19 / 20 ≤ s
  · linarith [htail.2 h2]
  exact hc p delta hp s ⟨(lt_of_not_ge h1).le, (lt_of_not_ge h2).le⟩

theorem sigma_core_cover_proved (eta sigma : ℝ) (he : eta ∈ Icc (0 : ℝ) eta1)
    (hs : sEta eta sigma ∈ Icc (1 / 20 : ℝ) (19 / 20)) (hsi : sigma ∈ Ioo (0 : ℝ) 1) :
    sEta eta sigma * exprel eta ≤ sigma ∧ sigma ≤ sEta eta sigma ∧
    sigma ∈ Icc (9 / 200 : ℝ) (19 / 20) := by
  obtain ⟨he0, he1⟩ := he
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨hσ0, hσ1⟩ := hsi
  have hE := exprel_pos eta
  have hmul : sEta eta sigma * exprel eta = sigma * exprel (sigma * eta) := by
    rw [sEta]
    field_simp
  have h1 : sEta eta sigma * exprel eta ≤ sigma := by
    rw [hmul]
    exact mul_le_of_le_one_right hσ0.le (exprel_le_one (mul_nonneg hσ0.le he0))
  have h2 : sigma ≤ sEta eta sigma := by
    rw [sEta, le_div_iff₀ hE]
    exact mul_le_mul_of_nonneg_left
      (exprel_anti (mul_nonneg hσ0.le he0) (mul_le_of_le_one_left he0 hσ1.le)) hσ0.le
  have h3 : exprel eta1 ≤ exprel eta := exprel_anti he0 he1
  have h4 := exprel_eta1
  have h5 : (1 / 20) * exprel eta ≤ sEta eta sigma * exprel eta := mul_le_mul_of_nonneg_right hs1 hE.le
  exact ⟨h1, h2, by linarith, by linarith⟩

end GKSharp
