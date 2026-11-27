module

public import ThirteenPlanes.Basins.Calculus
public import ThirteenPlanes.Planar
public import Mathlib.Analysis.ODE.Basic

@[expose] public section

/-! A priori bounds for forward solutions of the homogeneous one-loop flow.

A forward solution is `x : ℝ → ℝ × ℝ` with `IsIntegralCurveOn x (fun _ ↦ familyField lam ε)
(Ici 0)`: physical time `ℓ ≥ 0`, one-sided derivative at `ℓ = 0`. The weighted squared strength
`R = a² + 3 lam b²` obeys `K R' = K ε R - D` with `R²/6 ≤ D ≤ 3 R²` (`lam ≥ 1/2`). -/

open Set Filter Topology

namespace ThirteenPlanes

noncomputable section

variable {lam ε : ℝ} {x : ℝ → ℝ × ℝ}

theorem solution_fst
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) :
    ∀ s ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun r ↦ (x r).1) (familyField lam ε ((x s).1, (x s).2)).1 (Ici 0) s :=
  fun s hs ↦ (hx s hs).fst

theorem solution_snd
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) :
    ∀ s ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun r ↦ (x r).2) (familyField lam ε ((x s).1, (x s).2)).2 (Ici 0) s :=
  fun s hs ↦ (hx s hs).snd

/-- The weighted squared strength along a forward solution. -/
theorem hasDerivWithinAt_weightedStrength
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) :
    ∀ s ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun r ↦ weightedStrength lam (x r).1 (x r).2)
        ((flowScale * ε * weightedStrength lam (x s).1 (x s).2 -
          radialDamping lam (x s).1 (x s).2) / flowScale) (Ici 0) s := by
  intro s hs
  have h := ((solution_fst hx s hs).pow 2).add
    (((solution_snd hx s hs).pow 2).const_mul (3 * lam))
  convert h using 1
  · funext r
    simp [weightedStrength]
  · rw [div_eq_iff flowScale_ne_zero, ← familyField_weightedStrength lam ε (x s).1 (x s).2]
    simp only [Nat.cast_ofNat]
    ring

theorem weightedStrength_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (a b : ℝ) :
    0 ≤ weightedStrength lam a b := by
  unfold weightedStrength
  positivity

theorem weightedStrength_pos {lam : ℝ} (hlam : 0 < lam) {a b : ℝ} (h : (a, b) ≠ 0) :
    0 < weightedStrength lam a b := by
  unfold weightedStrength
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b ≠ 0 := fun hb ↦ h (by simp [hb])
    have := pow_pos (abs_pos.mpr hb) 2
    rw [sq_abs] at this
    positivity
  · have := pow_pos (abs_pos.mpr ha) 2
    rw [sq_abs] at this
    positivity

/-- Upper a priori bound: the weighted squared strength never exceeds the larger of its initial
value and `6 K ε`. -/
theorem weightedStrength_le_of_solution (hlam : 0 ≤ lam)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) :
    ∀ t, 0 ≤ t → weightedStrength lam (x t).1 (x t).2 ≤
      max (weightedStrength lam (x 0).1 (x 0).2) (6 * flowScale * ε) := by
  apply le_of_deriv_neg_above one_pos (hasDerivWithinAt_weightedStrength hx) (le_max_left _ _)
  intro s _ hC _
  set R := weightedStrength lam (x s).1 (x s).2
  have hR0 : 0 ≤ weightedStrength lam (x 0).1 (x 0).2 := weightedStrength_nonneg hlam _ _
  have h1 : 6 * flowScale * ε < R := lt_of_le_of_lt (le_max_right _ _) hC
  have h2 : 0 < R := lt_of_le_of_lt (le_trans hR0 (le_max_left _ _)) hC
  have hD := weightedStrength_sq_div_six_le_radialDamping hlam (x s).1 (x s).2
  apply div_neg_of_neg_of_pos _ flowScale_pos
  nlinarith [mul_pos h2 (sub_pos.mpr h1)]

/-- Lower a priori bound (`lam ≥ 1/2`): the weighted squared strength never drops below the
smaller of its initial value and `K ε / 3`. -/
theorem le_weightedStrength_of_solution (hlam : 1 / 2 ≤ lam)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) :
    ∀ t, 0 ≤ t → min (weightedStrength lam (x 0).1 (x 0).2) (flowScale * ε / 3) ≤
      weightedStrength lam (x t).1 (x t).2 := by
  set c := min (weightedStrength lam (x 0).1 (x 0).2) (flowScale * ε / 3)
  have hlam0 : 0 ≤ lam := by linarith
  rcases le_or_gt c 0 with hc | hc
  · exact fun t _ ↦ le_trans hc (weightedStrength_nonneg hlam0 _ _)
  apply ge_of_deriv_pos_below (half_pos hc) (hasDerivWithinAt_weightedStrength hx)
    (min_le_left _ _)
  intro s _ hlt hge
  set R := weightedStrength lam (x s).1 (x s).2
  have h1 : R < flowScale * ε / 3 := lt_of_lt_of_le hlt (min_le_right _ _)
  have h2 : 0 < R := by linarith
  have hD := radialDamping_le_three_weightedStrength_sq hlam (x s).1 (x s).2
  apply div_pos _ flowScale_pos
  nlinarith [mul_pos h2 (show 0 < flowScale * ε - 3 * R by linarith)]

/-- A forward solution that starts away from the origin stays uniformly away from it
(`lam ≥ 1/2`, `ε > 0`). -/
theorem weightedStrength_pos_lower_of_solution (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) (h0 : x 0 ≠ 0) :
    0 < min (weightedStrength lam (x 0).1 (x 0).2) (flowScale * ε / 3) ∧
    ∀ t, 0 ≤ t → min (weightedStrength lam (x 0).1 (x 0).2) (flowScale * ε / 3) ≤
      weightedStrength lam (x t).1 (x t).2 :=
  ⟨lt_min (weightedStrength_pos (by linarith) (by simpa using h0))
      (by have := flowScale_pos; positivity),
    le_weightedStrength_of_solution hlam hx⟩

/-- A forward solution that starts away from the origin never reaches it. -/
theorem ne_zero_of_solution (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) (h0 : x 0 ≠ 0) :
    ∀ t, 0 ≤ t → x t ≠ 0 := by
  intro t ht hxt
  obtain ⟨hpos, hle⟩ := weightedStrength_pos_lower_of_solution hlam hε hx h0
  have h1 := hle t ht
  have h2 : weightedStrength lam (x t).1 (x t).2 = 0 := by rw [hxt]; simp [weightedStrength]
  linarith

end

end ThirteenPlanes
