module

public import ThirteenPlanes.FourPlaneFixedData

@[expose] public section

set_option backward.privateInPublic true

/-! Complete classification of the zeros of the homogeneous one-loop field.

The chart statements (`familyField_fixed_iff_of_ne_zero`, `eight_fixed_iff`,
`twentySix_fixed_iff`) and the existence of both signs are in `FourPlaneFixedData`; here they are
turned into a chart-free list of points on the whole plane. -/

namespace ThirteenPlanes

noncomputable section

/-- On the pure-mixing axis the field is never zero away from the origin. -/
theorem familyField_pureMixing_ne_zero {lam ε b : ℝ} (hlam : lam ≠ 0) (hb : b ≠ 0) :
    familyField lam ε (0, b) ≠ 0 := by
  intro h
  have hm := familyField_pureMixing lam ε b
  rw [h] at hm
  change flowScale * 0 = _ at hm
  rw [mul_zero, eq_comm] at hm
  exact mul_ne_zero hlam (pow_ne_zero 3 hb) hm

private theorem strength_eq_iff {lam ε a t : ℝ} :
    a ^ 2 / flowScale * strengthPolynomial lam t = ε ↔
      a ^ 2 * strengthPolynomial lam t = flowScale * ε := by
  rw [div_mul_eq_mul_div, div_eq_iff flowScale_ne_zero, mul_comm ε]

/-- Every zero of the field for positive `lam`: the origin, two antipodal points on the decoupled
axis, on the equal-strength diagonal and on the line `a = -lam b`, with the stated strengths. -/
theorem familyField_eq_zero_iff_explicit {lam ε : ℝ} (hlam : 0 < lam) (u : ℝ × ℝ) :
    familyField lam ε u = 0 ↔
      u = 0 ∨
      (u.2 = 0 ∧ u.1 ^ 2 = flowScale * ε) ∨
      (u.2 = u.1 ∧ (1 + lam) * u.1 ^ 2 = flowScale * ε) ∨
      (u.1 = -lam * u.2 ∧ (lam + 1) * (lam + 2) * u.2 ^ 2 = flowScale * ε) := by
  rcases u with ⟨a, b⟩
  by_cases hu : (a, b) = 0
  · simp [hu]
  have hu' : ¬ (a = 0 ∧ b = 0) := fun h ↦ hu (by simp [h.1, h.2])
  rw [familyField_fixed_iff_of_ne_zero hlam hu, strength_eq_iff]
  simp only [hu, false_or]
  constructor
  · rintro ⟨ha, ht, hs⟩
    rcases ht with ht | ht | ht
    · have hb : b = 0 := by simpa [ha] using ht
      refine Or.inl ⟨hb, ?_⟩
      rw [ht, strengthPolynomial_eq] at hs
      simpa using hs
    · have hb : b = a := by rw [div_eq_one_iff_eq ha] at ht; exact ht
      refine Or.inr (Or.inl ⟨hb, ?_⟩)
      rw [ht, strengthPolynomial_eq] at hs
      linear_combination hs
    · have hb : a = -lam * b := by
        rw [div_eq_div_iff ha hlam.ne'] at ht
        linarith
      refine Or.inr (Or.inr ⟨hb, ?_⟩)
      rw [ht, strengthPolynomial_eq] at hs
      rw [hb] at hs
      have hl := hlam.ne'
      field_simp at hs
      linear_combination hs
  · rintro (⟨hb, hs⟩ | ⟨hb, hs⟩ | ⟨hb, hs⟩)
    · have ha : a ≠ 0 := fun ha ↦ hu' ⟨ha, hb⟩
      refine ⟨ha, Or.inl (by simp [hb]), ?_⟩
      rw [hb, zero_div, strengthPolynomial_eq]
      simpa using hs
    · have ha : a ≠ 0 := fun ha ↦ hu' ⟨ha, hb.trans ha⟩
      have ht : b / a = 1 := by rw [hb, div_self ha]
      refine ⟨ha, Or.inr (Or.inl ht), ?_⟩
      rw [ht, strengthPolynomial_eq]
      linear_combination hs
    · have hb0 : b ≠ 0 := fun hb0 ↦ hu' ⟨by rw [hb, hb0, mul_zero], hb0⟩
      have ha : a ≠ 0 := by rw [hb]; exact mul_ne_zero (neg_ne_zero.mpr hlam.ne') hb0
      have ht : b / a = -1 / lam := by
        rw [div_eq_div_iff ha hlam.ne', hb]
        ring
      refine ⟨ha, Or.inr (Or.inr ht), ?_⟩
      rw [ht, strengthPolynomial_eq, hb]
      have hl := hlam.ne'
      field_simp
      linear_combination hs

/-- The zeros of the thirteen-plane field (`lam = 2`). -/
theorem twentySix_zero_iff {ε : ℝ} (u : ℝ × ℝ) :
    familyField 2 ε u = 0 ↔
      u = 0 ∨
      (u.2 = 0 ∧ u.1 ^ 2 / flowScale = ε) ∨
      (u.2 = u.1 ∧ u.1 ^ 2 / flowScale = ε / 3) ∨
      (u.1 = -2 * u.2 ∧ u.1 ^ 2 / flowScale = ε / 3) := by
  rw [familyField_eq_zero_iff_explicit (by norm_num : (0 : ℝ) < 2)]
  have hK := flowScale_ne_zero
  refine or_congr_right (or_congr ?_ (or_congr ?_ ?_))
  · refine and_congr_right fun _ ↦ ?_
    rw [div_eq_iff hK]; constructor <;> intro h <;> linarith
  · refine and_congr_right fun _ ↦ ?_
    rw [div_eq_iff hK]; constructor <;> intro h <;> linarith
  · refine and_congr_right fun h ↦ ?_
    rw [h, div_eq_iff hK]; constructor <;> intro h <;> nlinarith

/-- The zeros of the four-plane field (`lam = 1/2`). -/
theorem eight_zero_iff {ε : ℝ} (u : ℝ × ℝ) :
    familyField (1 / 2) ε u = 0 ↔
      u = 0 ∨
      (u.2 = 0 ∧ u.1 ^ 2 / flowScale = ε) ∨
      (u.2 = u.1 ∧ u.1 ^ 2 / flowScale = 2 * ε / 3) ∨
      (u.1 = -(1 / 2) * u.2 ∧ u.1 ^ 2 / flowScale = ε / 15) := by
  rw [familyField_eq_zero_iff_explicit (by norm_num : (0 : ℝ) < 1 / 2)]
  have hK := flowScale_ne_zero
  refine or_congr_right (or_congr ?_ (or_congr ?_ ?_))
  · refine and_congr_right fun _ ↦ ?_
    rw [div_eq_iff hK]; constructor <;> intro h <;> linarith
  · refine and_congr_right fun _ ↦ ?_
    rw [div_eq_iff hK]; constructor <;> intro h <;> linarith
  · refine and_congr_right fun h ↦ ?_
    rw [h, div_eq_iff hK]; constructor <;> intro h <;> nlinarith

end

end ThirteenPlanes
