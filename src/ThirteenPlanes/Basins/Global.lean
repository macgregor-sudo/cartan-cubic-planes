module

public import ThirteenPlanes.Basins.RatioChart
public import ThirteenPlanes.Basins.Fixed

@[expose] public section

/-! Every forward solution away from the origin converges to a nonzero fixed point.

The plane minus the origin is the union of the invariant region `b (lam b + a) > 0` (limit: the
equal-strength point), the third line `a = -lam b` (its own fixed point), and the region of ratio
`-1/lam < b/a ≤ 0` (limit: the decoupled point). -/

open Set Filter Topology

namespace ThirteenPlanes

noncomputable section

variable {lam ε : ℝ} {x : ℝ → ℝ × ℝ}

theorem sectorQ_eq_chart (lam : ℝ) {a b : ℝ} (ha : a ≠ 0) :
    b * (lam * b + a) = a ^ 2 * (b / a * (lam * (b / a) + 1)) := by
  field_simp

/-- The region `b (lam b + a) > 0` in chart terms: `b ≠ 0`, and either `a = 0` or the ratio
`b/a` lies outside `[-1/lam, 0]`. -/
theorem sectorQ_pos_of_chart {lam a b : ℝ} (hlam : 0 < lam) (hb : b ≠ 0)
    (h : a = 0 ∨ b / a ∉ Icc (-1 / lam) 0) : 0 < b * (lam * b + a) := by
  rcases h with rfl | h
  · have := pow_pos (abs_pos.mpr hb) 2
    rw [sq_abs] at this
    nlinarith
  · have ha : a ≠ 0 := by
      rintro rfl; apply h; rw [div_zero]
      exact ⟨div_nonpos_of_nonpos_of_nonneg (by norm_num) hlam.le, le_rfl⟩
    rw [sectorQ_eq_chart lam ha]
    apply mul_pos (by positivity)
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · have : lam * (b / a) + 1 < 0 := by
        rw [lt_div_iff₀ hlam] at h; linarith
      nlinarith
    · have : 0 < lam * (b / a) + 1 := by positivity
      positivity

theorem equalStrength_fixed (hlam : 0 < lam) (hε : 0 < ε) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    familyField lam ε (σ * equalStrengthLevel lam ε, σ * equalStrengthLevel lam ε) = 0 := by
  rw [familyField_eq_zero_iff_explicit hlam]
  refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
  simp only [mul_pow, hσ, one_mul, equalStrengthLevel]
  rw [Real.sq_sqrt (by have := flowScale_pos; positivity)]
  field_simp

theorem decoupled_fixed (hε : 0 < ε) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    familyField lam ε (σ * decoupledLevel ε, 0) = 0 := by
  have h : familyField lam ε (σ * decoupledLevel ε, 0) =
      familyField lam ε (σ * decoupledLevel ε, σ * decoupledLevel ε * 0) := by rw [mul_zero]
  have hne : σ * decoupledLevel ε ≠ 0 := by
    apply mul_ne_zero (by rintro rfl; norm_num at hσ)
    exact (Real.sqrt_pos.mpr (by have := flowScale_pos; positivity)).ne'
  rw [h, familyField_eq_zero_iff_of_mul hne]
  refine ⟨by simp [ratioPolynomial], ?_⟩
  rw [strengthPolynomial_eq, div_mul_eq_mul_div, div_eq_iff flowScale_ne_zero]
  simp only [mul_pow, hσ, one_mul, decoupledLevel]
  rw [Real.sq_sqrt (by have := flowScale_pos; positivity)]
  ring

theorem thirdLine_fixed (hlam : 0 < lam) (hε : 0 < ε) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    familyField lam ε (-lam * (σ * thirdLineLevel lam ε), σ * thirdLineLevel lam ε) = 0 := by
  rw [familyField_eq_zero_iff_explicit hlam]
  refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
  simp only [mul_pow, hσ, one_mul, thirdLineLevel]
  rw [Real.sq_sqrt (by have := flowScale_pos; positivity)]
  field_simp

/-- Every forward solution that starts away from the origin converges to a nonzero zero of the
field (`lam ≥ 1/2`, `ε > 0`). -/
theorem exists_tendsto_fixedPoint (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) (h0 : x 0 ≠ 0) :
    ∃ p : ℝ × ℝ, p ≠ 0 ∧ familyField lam ε p = 0 ∧ Tendsto x atTop (𝓝 p) := by
  have hlam0 : 0 < lam := by linarith
  have hK := flowScale_pos
  have hc1 : 0 < equalStrengthLevel lam ε := Real.sqrt_pos.mpr (by positivity)
  have hc2 : 0 < decoupledLevel ε := Real.sqrt_pos.mpr (by positivity)
  have hc3 : 0 < thirdLineLevel lam ε := Real.sqrt_pos.mpr (by positivity)
  have one_sq : (1 : ℝ) ^ 2 = 1 := by norm_num
  have neg_one_sq : (-1 : ℝ) ^ 2 = 1 := by norm_num
  -- the decoupled region
  have hdec : (x 0).1 ≠ 0 → -1 / lam < (x 0).2 / (x 0).1 → (x 0).2 / (x 0).1 ≤ 0 →
      ∃ p : ℝ × ℝ, p ≠ 0 ∧ familyField lam ε p = 0 ∧ Tendsto x atTop (𝓝 p) := by
    intro ha0 hlo hhi
    obtain ⟨hp, hn⟩ := tendsto_decoupled_point hlam hε hx ha0 hlo hhi
    rcases lt_or_gt_of_ne ha0 with h | h
    · refine ⟨(-1 * decoupledLevel ε, 0), by simp [hc2.ne'], decoupled_fixed hε _ neg_one_sq, ?_⟩
      simpa using hn h
    · refine ⟨(1 * decoupledLevel ε, 0), by simp [hc2.ne'], decoupled_fixed hε _ one_sq, ?_⟩
      simpa using hp h
  by_cases hb0 : (x 0).2 = 0
  · have ha0 : (x 0).1 ≠ 0 := fun ha ↦ h0 (Prod.ext ha hb0)
    exact hdec ha0 (by rw [hb0, zero_div]; exact div_neg_of_neg_of_pos (by norm_num) hlam0)
      (by rw [hb0, zero_div])
  rcases lt_trichotomy ((x 0).2 * (lam * (x 0).2 + (x 0).1)) 0 with hq | hq | hq
  · have ha0 : (x 0).1 ≠ 0 := by
      rintro ha; rw [ha, add_zero] at hq; nlinarith [sq_nonneg (x 0).2]
    rw [sectorQ_eq_chart lam ha0] at hq
    have hpa : 0 < (x 0).1 ^ 2 := by positivity
    have hneg : (x 0).2 / (x 0).1 * (lam * ((x 0).2 / (x 0).1) + 1) < 0 := by
      by_contra h; rw [not_lt] at h; nlinarith
    set t := (x 0).2 / (x 0).1
    rcases lt_or_ge t 0 with ht | ht
    · refine hdec ha0 ?_ ht.le
      have : 0 < lam * t + 1 := by
        by_contra h; rw [not_lt] at h; nlinarith
      rw [div_lt_iff₀ hlam0]; linarith
    · exfalso
      have : 0 < lam * t + 1 := by positivity
      nlinarith
  · have hline : (x 0).1 = -lam * (x 0).2 := by
      have := (mul_eq_zero.mp hq).resolve_left hb0; linarith
    obtain ⟨hp, hn⟩ := tendsto_thirdLine_point hlam hε hx hline
    rcases lt_or_gt_of_ne hb0 with h | h
    · refine ⟨(-lam * (-1 * thirdLineLevel lam ε), -1 * thirdLineLevel lam ε),
        by simp [hc3.ne'], thirdLine_fixed hlam0 hε _ neg_one_sq, ?_⟩
      simpa using hn h
    · refine ⟨(-lam * (1 * thirdLineLevel lam ε), 1 * thirdLineLevel lam ε),
        by simp [hc3.ne'], thirdLine_fixed hlam0 hε _ one_sq, ?_⟩
      simpa using hp h
  · obtain ⟨hp, hn⟩ := tendsto_equalStrength_point hlam hε hx hq
    rcases lt_or_gt_of_ne hb0 with h | h
    · refine ⟨(-1 * equalStrengthLevel lam ε, -1 * equalStrengthLevel lam ε),
        by simp [hc1.ne'], equalStrength_fixed hlam0 hε _ neg_one_sq, ?_⟩
      simpa using hn h
    · refine ⟨(1 * equalStrengthLevel lam ε, 1 * equalStrengthLevel lam ε),
        by simp [hc1.ne'], equalStrength_fixed hlam0 hε _ one_sq, ?_⟩
      simpa using hp h

end

end ThirteenPlanes
