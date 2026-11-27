module

public import ThirteenPlanes.Planar
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

set_option backward.privateInPublic true

/-! Fixed strengths and linearized scaling data for the two scalar models. -/

namespace ThirteenPlanes

noncomputable section

/-- The two chart velocities in physical time. -/
def chartField (lam ε : ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  ((flowScale * ε * u.1 - strengthPolynomial lam u.2 * u.1 ^ 3) / (2 * flowScale),
   u.1 ^ 2 * ratioPolynomial lam u.2 / flowScale)

/-- The ordinary derivative of the shape polynomial. -/
def ratioSlope (lam t : ℝ) : ℝ :=
  2 * t * (1 - t) * (1 + lam * t) - t ^ 2 * (1 + lam * t) + t ^ 2 * (1 - t) * lam

theorem hasDerivAt_ratioPolynomial (lam t : ℝ) :
    HasDerivAt (ratioPolynomial lam) (ratioSlope lam t) t := by
  have ht := hasDerivAt_id t
  have hl : HasDerivAt (fun x : ℝ ↦ 1 - x) (0 - 1) t :=
    HasDerivAt.sub (hasDerivAt_const t 1) ht
  have hr : HasDerivAt (fun x : ℝ ↦ 1 + lam * x) (0 + lam * 1) t :=
    HasDerivAt.add (hasDerivAt_const t 1) (ht.const_mul lam)
  convert ((ht.pow 2).mul hl).mul hr using 1
  · rfl
  · simp only [ratioSlope, Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat]
    ring

theorem hasDerivAt_chartStrength (lam ε a t : ℝ) :
    HasDerivAt (fun x ↦ (chartField lam ε (x, t)).1)
      ((flowScale * ε - 3 * strengthPolynomial lam t * a ^ 2) / (2 * flowScale)) a := by
  have ha := hasDerivAt_id a
  convert (HasDerivAt.sub (ha.const_mul (flowScale * ε))
    ((ha.pow 3).const_mul (strengthPolynomial lam t))).div_const (2 * flowScale) using 1
  · rfl
  · simp only [id_eq, Nat.cast_ofNat]
    ring

theorem hasDerivAt_chartRatio_strength (lam ε a t : ℝ) :
    HasDerivAt (fun x ↦ (chartField lam ε (x, t)).2)
      (2 * a * ratioPolynomial lam t / flowScale) a := by
  convert (((hasDerivAt_id a).pow 2).mul_const (ratioPolynomial lam t)).div_const flowScale
    using 1
  · rfl
  · norm_num

theorem hasDerivAt_chartRatio_ratio (lam ε a t : ℝ) :
    HasDerivAt (fun x ↦ (chartField lam ε (a, x)).2)
      (a ^ 2 * ratioSlope lam t / flowScale) t := by
  exact ((hasDerivAt_ratioPolynomial lam t).const_mul (a ^ 2)).div_const flowScale

/-- The one-loop scalar field dimension, with the pair fixed at its chart coordinates. -/
def scalarDimension (lam ε a t : ℝ) : ℝ :=
  1 - ε / 2 + familyM lam (1, t) * (a ^ 2 / flowScale) / 2

/-- In physical time the exponent is the negative of the linearized diagonal entry. -/
def ratioExponent (lam a t : ℝ) : ℝ := -(a ^ 2 / flowScale * ratioSlope lam t)

theorem chartLinearization_at_fixed {lam ε a t : ℝ} (ha : a ≠ 0)
    (hfixed : familyField lam ε (a, a * t) = 0) :
    HasDerivAt (fun x ↦ (chartField lam ε (x, t)).1) (-ε) a ∧
    HasDerivAt (fun x ↦ (chartField lam ε (x, t)).2) 0 a ∧
    HasDerivAt (fun x ↦ (chartField lam ε (a, x)).2) (-ratioExponent lam a t) t := by
  obtain ⟨ht, hs⟩ := (familyField_eq_zero_iff_of_mul ha).mp hfixed
  refine ⟨?_, ?_, ?_⟩
  · convert hasDerivAt_chartStrength lam ε a t using 1
    rw [eq_div_iff (mul_ne_zero (by norm_num) flowScale_ne_zero)]
    rw [div_mul_eq_mul_div, div_eq_iff flowScale_ne_zero] at hs
    linear_combination 3 * hs
  · simpa [ht] using hasDerivAt_chartRatio_strength lam ε a t
  · convert hasDerivAt_chartRatio_ratio lam ε a t using 1
    simp only [ratioExponent, neg_neg]
    ring

private theorem familyField_fixed_of_lam_pos {lam ε a b : ℝ} (hlam : 0 < lam)
    (hfixed : familyField lam ε (a, b) = 0) (hu : (a, b) ≠ 0) : a ≠ 0 := by
  intro ha
  subst a
  have hm := familyField_pureMixing lam ε b
  rw [hfixed] at hm
  change flowScale * 0 = _ at hm
  rw [mul_zero, eq_comm, mul_eq_zero] at hm
  have hb := (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp (hm.resolve_left hlam.ne')
  exact hu (Prod.ext rfl hb)

/-- Stationarity at nonzero coupling, including exclusion of the pure-mixing axis. -/
theorem familyField_fixed_iff_of_ne_zero {lam ε a b : ℝ} (hlam : 0 < lam)
    (hu : (a, b) ≠ 0) :
    familyField lam ε (a, b) = 0 ↔ a ≠ 0 ∧
      (b / a = 0 ∨ b / a = 1 ∨ b / a = -1 / lam) ∧
      a ^ 2 / flowScale * strengthPolynomial lam (b / a) = ε := by
  have key (ha : a ≠ 0) := by
    have hb : a * (b / a) = b := by rw [mul_comm, div_mul_cancel₀ _ ha]
    simpa only [hb, ratioPolynomial_eq_zero_iff hlam.ne'] using
      (familyField_eq_zero_iff_of_mul (lam := lam) (ε := ε) (t := b / a) ha)
  exact ⟨fun h ↦ ⟨familyField_fixed_of_lam_pos hlam h hu,
    (key (familyField_fixed_of_lam_pos hlam h hu)).mp h⟩, fun ⟨ha, h⟩ ↦ (key ha).mpr h⟩

/-- The strengths in the four-plane fixed-point table, in the chart `b = a * t`. -/
theorem eight_fixed_iff {ε a t : ℝ} (ha : a ≠ 0) :
    familyField (1 / 2) ε (a, a * t) = 0 ↔
      (t = 1 ∧ a ^ 2 / flowScale = 2 * ε / 3) ∨
      (t = -2 ∧ a ^ 2 / flowScale = ε / 15) ∨
      (t = 0 ∧ a ^ 2 / flowScale = ε) := by
  rw [familyField_eq_zero_iff_of_mul ha, ratioPolynomial_eq_zero_iff (by norm_num)]
  norm_num
  constructor
  · rintro ⟨rfl | rfl | rfl, h⟩
    · exact Or.inr (Or.inr ⟨rfl, by simpa [strengthPolynomial_eq] using h⟩)
    · refine Or.inl ⟨rfl, ?_⟩
      norm_num [strengthPolynomial_eq] at h
      linarith
    · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      norm_num [strengthPolynomial_eq] at h
      linarith
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨Or.inr (Or.inl rfl), by norm_num [strengthPolynomial_eq, h]; ring⟩
    · exact ⟨Or.inr (Or.inr rfl), by norm_num [strengthPolynomial_eq, h]⟩
    · exact ⟨Or.inl rfl, by norm_num [strengthPolynomial_eq, h]⟩

/-- The strengths in the thirteen-plane fixed-point table, in the chart `b = a * t`. -/
theorem twentySix_fixed_iff {ε a t : ℝ} (ha : a ≠ 0) :
    familyField 2 ε (a, a * t) = 0 ↔
      (t = 1 ∧ a ^ 2 / flowScale = ε / 3) ∨
      (t = -1 / 2 ∧ a ^ 2 / flowScale = ε / 3) ∨
      (t = 0 ∧ a ^ 2 / flowScale = ε) := by
  rw [familyField_eq_zero_iff_of_mul ha, ratioPolynomial_eq_zero_iff (by norm_num)]
  constructor
  · rintro ⟨rfl | rfl | rfl, h⟩
    · exact Or.inr (Or.inr ⟨rfl, by simpa [strengthPolynomial_eq] using h⟩)
    · refine Or.inl ⟨rfl, ?_⟩
      norm_num [strengthPolynomial_eq] at h
      linarith
    · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      norm_num [strengthPolynomial_eq] at h
      linarith
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨Or.inr (Or.inl rfl), by norm_num [strengthPolynomial_eq, h]⟩
    · exact ⟨Or.inr (Or.inr rfl), by norm_num [strengthPolynomial_eq, h]⟩
    · exact ⟨Or.inl rfl, by norm_num [strengthPolynomial_eq, h]⟩

/-- The ratio exponents and field dimensions in the four-plane table. -/
theorem eight_stationary_scaling {ε a t : ℝ} (ha : a ≠ 0)
    (hfixed : familyField (1 / 2) ε (a, a * t) = 0) :
    (t = 1 ∧ ratioExponent (1 / 2) a t = ε ∧ scalarDimension (1 / 2) ε a t = 1 - 2 * ε / 9) ∨
    (t = -2 ∧ ratioExponent (1 / 2) a t = -2 * ε / 5 ∧
      scalarDimension (1 / 2) ε a t = 1 - 19 * ε / 45) ∨
    (t = 0 ∧ ratioExponent (1 / 2) a t = 0 ∧ scalarDimension (1 / 2) ε a t = 1 - ε / 3) := by
  rcases (eight_fixed_iff ha).mp hfixed with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, by norm_num [ratioExponent, ratioSlope, h]; ring,
      by norm_num [scalarDimension, familyM, h]; ring⟩
  · exact Or.inr (Or.inl ⟨rfl, by norm_num [ratioExponent, ratioSlope, h]; ring,
      by norm_num [scalarDimension, familyM, h]; ring⟩)
  · exact Or.inr (Or.inr ⟨rfl, by norm_num [ratioExponent, ratioSlope],
      by norm_num [scalarDimension, familyM, h]; ring⟩)

/-- The ratio exponents and field dimensions in the thirteen-plane table. -/
theorem twentySix_stationary_scaling {ε a t : ℝ} (ha : a ≠ 0)
    (hfixed : familyField 2 ε (a, a * t) = 0) :
    (t = 1 ∧ ratioExponent 2 a t = ε ∧ scalarDimension 2 ε a t = 1 - ε / 9) ∨
    (t = -1 / 2 ∧ ratioExponent 2 a t = -ε / 4 ∧
      scalarDimension 2 ε a t = 1 - 13 * ε / 36) ∨
    (t = 0 ∧ ratioExponent 2 a t = 0 ∧ scalarDimension 2 ε a t = 1 - ε / 3) := by
  rcases (twentySix_fixed_iff ha).mp hfixed with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, by norm_num [ratioExponent, ratioSlope, h],
      by norm_num [scalarDimension, familyM, h]; ring⟩
  · exact Or.inr (Or.inl ⟨rfl, by norm_num [ratioExponent, ratioSlope, h]; ring,
      by norm_num [scalarDimension, familyM, h]; ring⟩)
  · exact Or.inr (Or.inr ⟨rfl, by norm_num [ratioExponent, ratioSlope],
      by norm_num [scalarDimension, familyM, h]; ring⟩)

/-- For positive `ε`, any positive strength from either table is attained at both signs. -/
theorem exists_signed_strength {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ a ^ 2 / flowScale = c ∧ (-a) ^ 2 / flowScale = c := by
  have hp := mul_pos hc flowScale_pos
  refine ⟨Real.sqrt (c * flowScale), Real.sqrt_pos.2 hp, ?_, ?_⟩
  · exact (div_eq_iff flowScale_ne_zero).2 (Real.sq_sqrt hp.le)
  · rw [neg_sq]
    exact (div_eq_iff flowScale_ne_zero).2 (Real.sq_sqrt hp.le)

/-- Every positive stationary chart strength gives the two fixed couplings of opposite signs. -/
theorem exists_signed_fixed_of_ratioPolynomial_eq_zero {lam ε t : ℝ} (hε : 0 < ε)
    (ht : ratioPolynomial lam t = 0) (hc : 0 < strengthPolynomial lam t) :
    ∃ a : ℝ, 0 < a ∧ familyField lam ε (a, a * t) = 0 ∧
      familyField lam ε (-a, -a * t) = 0 := by
  obtain ⟨a, ha, hp, hn⟩ := exists_signed_strength (div_pos hε hc)
  refine ⟨a, ha, (familyField_eq_zero_iff_of_mul ha.ne').mpr ⟨ht, ?_⟩,
    (familyField_eq_zero_iff_of_mul (neg_ne_zero.mpr ha.ne')).mpr ⟨ht, ?_⟩⟩
  · rw [hp, div_mul_cancel₀ _ hc.ne']
  · rw [hn, div_mul_cancel₀ _ hc.ne']

/-- All three four-plane ratios are attained at positive and negative strength. -/
theorem eight_fixed_exists_at_ratio {ε t : ℝ} (hε : 0 < ε)
    (ht : t = 1 ∨ t = -2 ∨ t = 0) :
    ∃ a : ℝ, 0 < a ∧ familyField (1 / 2) ε (a, a * t) = 0 ∧
      familyField (1 / 2) ε (-a, -a * t) = 0 := by
  apply exists_signed_fixed_of_ratioPolynomial_eq_zero hε
  · rcases ht with rfl | rfl | rfl <;> norm_num [ratioPolynomial]
  · rcases ht with rfl | rfl | rfl <;> norm_num [strengthPolynomial_eq]

/-- All three thirteen-plane ratios are attained at positive and negative strength. -/
theorem twentySix_fixed_exists_at_ratio {ε t : ℝ} (hε : 0 < ε)
    (ht : t = 1 ∨ t = -1 / 2 ∨ t = 0) :
    ∃ a : ℝ, 0 < a ∧ familyField 2 ε (a, a * t) = 0 ∧
      familyField 2 ε (-a, -a * t) = 0 := by
  apply exists_signed_fixed_of_ratioPolynomial_eq_zero hε
  · rcases ht with rfl | rfl | rfl <;> norm_num [ratioPolynomial]
  · rcases ht with rfl | rfl | rfl <;> norm_num [strengthPolynomial_eq]

/-- The four-plane reciprocal-strength forcing is bounded on both basin intervals. -/
theorem eight_strengthPolynomial_bounds {t : ℝ} (ht : t ∈ Set.Icc (-2) 1) :
    1 ≤ strengthPolynomial (1 / 2) t ∧ strengthPolynomial (1 / 2) t ≤ 15 := by
  rw [strengthPolynomial_eq]
  have ht₁ : 0 ≤ 3 - 2 * t := by linarith [ht.2]
  have ht₂ : 0 ≤ t ^ 2 - 7 * t / 2 + 7 := by nlinarith only [sq_nonneg t, ht.2]
  constructor
  · nlinarith only [mul_nonneg (sq_nonneg t) ht₁]
  · have h := mul_nonneg (show 0 ≤ t + 2 by linarith [ht.1]) ht₂
    nlinarith only [h]

/-- In either open four-plane interval the shape increases. -/
theorem eight_ratioPolynomial_pos {t : ℝ} (hlo : -2 < t) (hhi : t < 1) (ht : t ≠ 0) :
    0 < ratioPolynomial (1 / 2) t := by
  unfold ratioPolynomial
  exact mul_pos (mul_pos (sq_pos_of_ne_zero ht) (sub_pos.mpr hhi)) (by linarith)

end

end ThirteenPlanes
