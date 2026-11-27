module

public import ThirteenPlanes.Basins.Bounds

@[expose] public section

/-! Invariant lines and sectors of the homogeneous one-loop flow.

The mixing coordinate `b`, the diagonal gap `b - a` and the gap `lam b + a` each obey a linear
equation with multiplicative rate along any forward solution, so each keeps its sign and its zero
set. The three stationary lines are invariant, and so are the open sectors between them, described
by the signs of `b (b - a)` and `b (lam b + a)`. -/

open Set Filter Topology

namespace ThirteenPlanes

noncomputable section

variable {lam ε : ℝ} {x : ℝ → ℝ × ℝ}

/-- The multiplicative rate of the mixing coordinate. -/
def mixingRate (lam ε : ℝ) (u : ℝ × ℝ) : ℝ :=
  (8 * Real.pi ^ 2 * ε - 3 * familyM lam u / 2 + u.1 * u.2 - (1 - lam) * u.2 ^ 2) / flowScale

/-- The multiplicative rate of the gap to a stationary ray of ratio `r`. -/
def gapRate (lam ε r : ℝ) (u : ℝ × ℝ) : ℝ :=
  (8 * Real.pi ^ 2 * ε - 3 * familyM lam u / 2 - (1 - lam + r * lam) * u.2 ^ 2) / flowScale

theorem continuous_mixingRate (lam ε : ℝ) : Continuous (mixingRate lam ε) := by
  unfold mixingRate familyM
  fun_prop

theorem continuous_gapRate (lam ε r : ℝ) : Continuous (gapRate lam ε r) := by
  unfold gapRate familyM
  fun_prop

/-- Along a forward solution the mixing coordinate is a positive multiple of its initial value. -/
theorem mixing_eq_pos_mul (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) :
    ∀ t, 0 ≤ t → ∃ k > 0, (x t).2 = k * (x 0).2 := by
  apply exists_pos_mul_of_multiplicative (c := fun s ↦ mixingRate lam ε (x s))
    ((continuous_mixingRate lam ε).comp_continuousOn hx.continuousOn)
  intro s hs
  have h := solution_snd hx s hs
  rwa [familyField_mixing_factor] at h

/-- Along a forward solution the gap `b - r a` to a stationary ray is a positive multiple of its
initial value. -/
theorem gap_eq_pos_mul {r : ℝ} (hr : (1 - lam + r * lam) * r = 1)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) :
    ∀ t, 0 ≤ t → ∃ k > 0, (x t).2 - r * (x t).1 = k * ((x 0).2 - r * (x 0).1) := by
  apply exists_pos_mul_of_multiplicative (y := fun s ↦ (x s).2 - r * (x s).1)
    (c := fun s ↦ gapRate lam ε r (x s))
    ((continuous_gapRate lam ε r).comp_continuousOn hx.continuousOn)
  intro s hs
  have h := (solution_snd hx s hs).sub ((solution_fst hx s hs).const_mul r)
  rwa [familyField_ray_gap_factor hr] at h

/-- The diagonal gap `b - a` is a positive multiple of its initial value. -/
theorem diagonalGap_eq_pos_mul (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) :
    ∀ t, 0 ≤ t → ∃ k > 0, (x t).2 - (x t).1 = k * ((x 0).2 - (x 0).1) := by
  intro t ht
  obtain ⟨k, hk, h⟩ := gap_eq_pos_mul (r := 1) (by ring) hx t ht
  exact ⟨k, hk, by simpa using h⟩

/-- The gap `lam b + a` to the third stationary line is a positive multiple of its initial value. -/
theorem thirdGap_eq_pos_mul (hlam : lam ≠ 0)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) :
    ∀ t, 0 ≤ t → ∃ k > 0, lam * (x t).2 + (x t).1 = k * (lam * (x 0).2 + (x 0).1) := by
  intro t ht
  obtain ⟨k, hk, h⟩ := gap_eq_pos_mul (r := -1 / lam) (by field_simp; ring) hx t ht
  refine ⟨k, hk, ?_⟩
  have e : ∀ a b : ℝ, lam * b + a = lam * (b - -1 / lam * a) := fun a b ↦ by
    field_simp; ring
  rw [e, e, h]
  ring

/-- The sector function `b (lam b + a)` is a positive multiple of its initial value. -/
theorem sectorQ_eq_pos_mul (hlam : lam ≠ 0)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) :
    ∀ t, 0 ≤ t → ∃ k > 0, (x t).2 * (lam * (x t).2 + (x t).1) =
      k * ((x 0).2 * (lam * (x 0).2 + (x 0).1)) := by
  intro t ht
  obtain ⟨k₁, hk₁, h₁⟩ := mixing_eq_pos_mul hx t ht
  obtain ⟨k₂, hk₂, h₂⟩ := thirdGap_eq_pos_mul hlam hx t ht
  exact ⟨k₁ * k₂, mul_pos hk₁ hk₂, by rw [h₂, mul_mul_mul_comm, ← h₁]⟩

/-- The sector function `b (b - a)` is a positive multiple of its initial value. -/
theorem sectorP_eq_pos_mul (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) :
    ∀ t, 0 ≤ t → ∃ k > 0, (x t).2 * ((x t).2 - (x t).1) =
      k * ((x 0).2 * ((x 0).2 - (x 0).1)) := by
  intro t ht
  obtain ⟨k₁, hk₁, h₁⟩ := mixing_eq_pos_mul hx t ht
  obtain ⟨k₂, hk₂, h₂⟩ := diagonalGap_eq_pos_mul hx t ht
  exact ⟨k₁ * k₂, mul_pos hk₁ hk₂, by rw [h₂, mul_mul_mul_comm, ← h₁]⟩

section Signs

variable {y : ℝ → ℝ}

theorem pos_of_pos_mul (h : ∀ t, 0 ≤ t → ∃ k > 0, y t = k * y 0) (h0 : 0 < y 0) :
    ∀ t, 0 ≤ t → 0 < y t := fun t ht ↦ by
  obtain ⟨k, hk, e⟩ := h t ht
  rw [e]; positivity

theorem neg_of_pos_mul (h : ∀ t, 0 ≤ t → ∃ k > 0, y t = k * y 0) (h0 : y 0 < 0) :
    ∀ t, 0 ≤ t → y t < 0 := fun t ht ↦ by
  obtain ⟨k, hk, e⟩ := h t ht
  rw [e]; exact mul_neg_of_pos_of_neg hk h0

theorem zero_of_pos_mul (h : ∀ t, 0 ≤ t → ∃ k > 0, y t = k * y 0) (h0 : y 0 = 0) :
    ∀ t, 0 ≤ t → y t = 0 := fun t ht ↦ by
  obtain ⟨k, hk, e⟩ := h t ht
  rw [e, h0, mul_zero]

theorem ne_zero_of_pos_mul (h : ∀ t, 0 ≤ t → ∃ k > 0, y t = k * y 0) (h0 : y 0 ≠ 0) :
    ∀ t, 0 ≤ t → y t ≠ 0 := fun t ht ↦ by
  obtain ⟨k, hk, e⟩ := h t ht
  rw [e]; exact mul_ne_zero hk.ne' h0

end Signs

/-- The decoupled axis `b = 0` is invariant. -/
theorem decoupled_invariant (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (h0 : (x 0).2 = 0) : ∀ t, 0 ≤ t → (x t).2 = 0 :=
  zero_of_pos_mul (mixing_eq_pos_mul hx) h0

/-- The equal-strength diagonal `b = a` is invariant. -/
theorem diagonal_invariant (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (h0 : (x 0).2 = (x 0).1) : ∀ t, 0 ≤ t → (x t).2 = (x t).1 := fun t ht ↦
  sub_eq_zero.mp (zero_of_pos_mul (diagonalGap_eq_pos_mul hx) (sub_eq_zero.mpr h0) t ht)

/-- The third stationary line `a = -lam b` is invariant. -/
theorem thirdLine_invariant (hlam : lam ≠ 0)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (h0 : (x 0).1 = -lam * (x 0).2) : ∀ t, 0 ≤ t → (x t).1 = -lam * (x t).2 := fun t ht ↦ by
  have := zero_of_pos_mul (thirdGap_eq_pos_mul hlam hx) (by rw [h0]; ring) t ht
  linarith

end

end ThirteenPlanes
