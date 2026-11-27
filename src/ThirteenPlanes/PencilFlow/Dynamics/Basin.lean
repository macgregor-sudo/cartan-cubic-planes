module

public import ThirteenPlanes.Basins.Endpoints

@[expose] public section

set_option backward.privateInPublic true

/-! The equal-strength basin of the planar field `familyField lam ε` for every `lam > 0`.

The basin estimates assume `1/2 ≤ lam` only through the damping bound `D ≤ 3 R²`. For any
`lam > 0` the bound `D ≤ (3 + 1/lam) R²` holds, which gives the same lower a-priori bound with a
different constant. The proofs below follow `Basins/Bounds.lean` and `Basins/MixingChart.lean`
with that single change. -/

open Set Filter Topology

namespace ThirteenPlanes.PencilFlow.Dynamics

noncomputable section

open ThirteenPlanes

variable {lam ε : ℝ} {x : ℝ → ℝ × ℝ}

/-- An upper bound for radial damping for every positive `lam`. -/
theorem radialDamping_le_weightedStrength_sq (hlam : 0 < lam) (a b : ℝ) :
    radialDamping lam a b ≤ (3 + 1 / lam) * weightedStrength lam a b ^ 2 := by
  have hb4 : 0 ≤ b ^ 4 := by positivity
  have h1 : radialDamping lam a b ≤ a ^ 4 + 12 * lam * a ^ 2 * b ^ 2 +
      (3 * lam ^ 2 + 26 * lam / 3) * b ^ 4 := by
    unfold radialDamping
    nlinarith only [mul_nonneg hlam.le (sq_nonneg (a * b + 2 * b ^ 2 / 3))]
  have hinv : lam * (1 / lam) = 1 := by field_simp
  have hi : 0 < 1 / lam := by positivity
  have e : (3 + 1 / lam) * weightedStrength lam a b ^ 2 =
      (3 + 1 / lam) * a ^ 4 + (18 * lam + 6) * a ^ 2 * b ^ 2 + (27 * lam ^ 2 + 9 * lam) * b ^ 4 := by
    unfold weightedStrength
    have : (3 + 1 / lam) * (6 * lam) = 18 * lam + 6 := by
      linear_combination 6 * hinv
    have h2 : (3 + 1 / lam) * (9 * lam ^ 2) = 27 * lam ^ 2 + 9 * lam := by
      linear_combination 9 * lam * hinv
    linear_combination (a ^ 2 * b ^ 2) * this + b ^ 4 * h2
  rw [e]
  have ha4 : 0 ≤ a ^ 4 := by positivity
  have hab : 0 ≤ a ^ 2 * b ^ 2 := by positivity
  nlinarith [mul_nonneg hi.le ha4, mul_nonneg hlam.le hab, mul_nonneg (sq_nonneg lam) hb4,
    mul_nonneg hlam.le hb4]

/-- Lower a priori bound for every `lam > 0`. -/
theorem le_weightedStrength_of_solution' (hlam : 0 < lam)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) :
    ∀ t, 0 ≤ t → min (weightedStrength lam (x 0).1 (x 0).2) (flowScale * ε / (3 + 1 / lam)) ≤
      weightedStrength lam (x t).1 (x t).2 := by
  set c := min (weightedStrength lam (x 0).1 (x 0).2) (flowScale * ε / (3 + 1 / lam))
  have hC : 0 < 3 + 1 / lam := by positivity
  rcases le_or_gt c 0 with hc | hc
  · exact fun t _ ↦ le_trans hc (weightedStrength_nonneg hlam.le _ _)
  apply ge_of_deriv_pos_below (half_pos hc) (hasDerivWithinAt_weightedStrength hx)
    (min_le_left _ _)
  intro s _ hlt hge
  set R := weightedStrength lam (x s).1 (x s).2
  have h1 : R < flowScale * ε / (3 + 1 / lam) := lt_of_lt_of_le hlt (min_le_right _ _)
  have h1' : (3 + 1 / lam) * R < flowScale * ε := by rwa [lt_div_iff₀ hC, mul_comm] at h1
  have h2 : 0 < R := by linarith
  have hD := radialDamping_le_weightedStrength_sq hlam (x s).1 (x s).2
  apply div_pos _ flowScale_pos
  nlinarith [mul_pos h2 (show 0 < flowScale * ε - (3 + 1 / lam) * R by linarith)]

theorem weightedStrength_pos_lower_of_solution' (hlam : 0 < lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0)) (h0 : x 0 ≠ 0) :
    0 < min (weightedStrength lam (x 0).1 (x 0).2) (flowScale * ε / (3 + 1 / lam)) ∧
    ∀ t, 0 ≤ t → min (weightedStrength lam (x 0).1 (x 0).2) (flowScale * ε / (3 + 1 / lam)) ≤
      weightedStrength lam (x t).1 (x t).2 :=
  ⟨lt_min (weightedStrength_pos hlam (by simpa using h0))
      (by have := flowScale_pos; positivity),
    le_weightedStrength_of_solution' hlam hx⟩

private theorem mul3_le' {β b m u c v K : ℝ} (hβ : 0 ≤ β) (hb : β ≤ b) (hm : 0 ≤ m) (hu : m ≤ u)
    (hc : 0 ≤ c) (hv : c ≤ v) (hK : 0 < K) : β * m * c / K ≤ b * u * v / K := by
  apply div_le_div_of_nonneg_right _ hK.le
  exact mul_le_mul (mul_le_mul hb hu hm (le_trans hβ hb)) hv hc
    (mul_nonneg (le_trans hβ hb) (le_trans hm hu))

/-- In the region `b (lam b + a) > 0` the inverse ratio `a/b` tends to `1` (`lam > 0`). -/
theorem tendsto_inverseRatio_one' (hlam0 : 0 < lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (hq : 0 < (x 0).2 * (lam * (x 0).2 + (x 0).1)) :
    Tendsto (fun s ↦ (x s).1 / (x s).2) atTop (𝓝 1) := by
  have hb0 : (x 0).2 ≠ 0 := by intro h; rw [h, zero_mul] at hq; exact lt_irrefl 0 hq
  have hb := ne_zero_of_pos_mul (mixing_eq_pos_mul hx) hb0
  have hx0 : x 0 ≠ 0 := fun h ↦ hb0 (by rw [h]; rfl)
  obtain ⟨hRlo, hRle⟩ := weightedStrength_pos_lower_of_solution' hlam0 hε hx hx0
  set Rlo := min (weightedStrength lam (x 0).1 (x 0).2) (flowScale * ε / (3 + 1 / lam))
  set u : ℝ → ℝ := fun s ↦ (x s).1 / (x s).2 with hu_def
  have hu' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt u
      ((x s).2 ^ 2 * (1 - u s) * (u s + lam) / flowScale) (Ici 0) s := fun s hs ↦
    familyField_hasDerivWithinAt_inverseRatio (hb s hs) (solution_fst hx s hs)
      (solution_snd hx s hs)
  have hq' := pos_of_pos_mul (sectorQ_eq_pos_mul hlam0.ne' hx) hq
  have hlamu : ∀ s, 0 ≤ s → 0 < u s + lam := by
    intro s hs
    have h1 := hq' s hs
    have hbs := hb s hs
    have e : (x s).2 * (lam * (x s).2 + (x s).1) = (x s).2 ^ 2 * (u s + lam) := by
      simp only [u]; field_simp; ring
    rw [e] at h1
    by_contra hneg
    rw [not_lt] at hneg
    linarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (x s).2) hneg]
  have hpe : ∀ s, (x s).2 ≠ 0 →
      (x s).2 * ((x s).2 - (x s).1) = (x s).2 ^ 2 * (1 - u s) := fun s hbs ↦ by
    simp only [u]; field_simp
  have hpm := sectorP_eq_pos_mul hx
  have hu0lam := hlamu 0 le_rfl
  rcases lt_trichotomy ((x 0).2 * ((x 0).2 - (x 0).1)) 0 with hp0 | hp0 | hp0
  · have hgt : ∀ s, 0 ≤ s → 1 < u s := by
      intro s hs
      have h1 := neg_of_pos_mul hpm hp0 s hs
      rw [hpe s (hb s hs)] at h1
      by_contra hle
      rw [not_lt] at hle
      linarith [mul_nonneg (sq_nonneg (x s).2) (show 0 ≤ 1 - u s by linarith)]
    have h := tendsto_of_deriv_nonneg_bounded (y := fun s ↦ -u s)
      (y' := fun s ↦ -((x s).2 ^ 2 * (1 - u s) * (u s + lam) / flowScale)) (L := -1)
      (fun s hs ↦ (hu' s hs).neg) (fun s hs ↦ by linarith [hgt s hs])
      (fun s hs ↦ by
        have := mul_nonneg (mul_nonneg (sq_nonneg (x s).2)
          (show 0 ≤ u s - 1 by linarith [hgt s hs])) (hlamu s hs).le
        rw [neg_nonneg]
        apply div_nonpos_of_nonpos_of_nonneg _ flowScale_pos.le
        nlinarith)
      (by
        intro M hM
        have hpos : 0 < u 0 ^ 2 + 3 * lam := by positivity
        refine ⟨Rlo / (u 0 ^ 2 + 3 * lam) * (-M - 1) * (1 + lam) / flowScale,
          by apply div_pos _ flowScale_pos; apply mul_pos (mul_pos (div_pos hRlo hpos)
            (by linarith)) (by linarith), ?_⟩
        intro s hs h0 hMs
        have h1s := hgt s hs
        have hβ := mixing_sq_lower (hb s hs) (hRle s hs) (B := u 0 ^ 2)
          (by simp only [u] at h0 ⊢; nlinarith) hpos
        have := mul3_le' (div_pos hRlo hpos).le hβ (show 0 ≤ -M - 1 by linarith)
          (show -M - 1 ≤ u s - 1 by linarith) (show 0 ≤ 1 + lam by linarith)
          (show 1 + lam ≤ u s + lam by linarith) flowScale_pos
        have e : -((x s).2 ^ 2 * (1 - u s) * (u s + lam) / flowScale) =
            (x s).2 ^ 2 * (u s - 1) * (u s + lam) / flowScale := by ring
        simp only [e]
        exact this)
    simpa using h.neg
  · have heq : ∀ s, 0 ≤ s → u s = 1 := by
      intro s hs
      have h1 := zero_of_pos_mul hpm hp0 s hs
      rw [hpe s (hb s hs)] at h1
      have := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 (hb s hs))
      linarith
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with s hs
    exact (heq s hs).symm
  · have hlt : ∀ s, 0 ≤ s → u s < 1 := by
      intro s hs
      have h1 := pos_of_pos_mul hpm hp0 s hs
      rw [hpe s (hb s hs)] at h1
      by_contra hle
      rw [not_lt] at hle
      linarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (x s).2) (show 1 - u s ≤ 0 by linarith)]
    apply tendsto_of_deriv_nonneg_bounded hu' (fun s hs ↦ (hlt s hs).le)
    · intro s hs
      apply div_nonneg _ flowScale_pos.le
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith [hlt s hs])) (hlamu s hs).le
    · intro M hM
      have hpos : 0 < u 0 ^ 2 + 1 + 3 * lam := by positivity
      refine ⟨Rlo / (u 0 ^ 2 + 1 + 3 * lam) * (1 - M) * (u 0 + lam) / flowScale,
        by apply div_pos _ flowScale_pos; exact mul_pos (mul_pos (div_pos hRlo hpos)
          (by linarith)) hu0lam, ?_⟩
      intro s hs h0 hMs
      have hβ := mixing_sq_lower (hb s hs) (hRle s hs) (B := u 0 ^ 2 + 1)
        (by
          change u s ^ 2 ≤ u 0 ^ 2 + 1
          rcases le_or_gt 0 (u s) with h | h
          · nlinarith
          · nlinarith) (by linarith)
      exact mul3_le' (div_pos hRlo (by linarith)).le hβ (by linarith) (by linarith)
        hu0lam.le (by linarith) flowScale_pos

/-- In the region `b (lam b + a) > 0`, `b²` tends to `K ε / (1 + lam)` (`lam > 0`). -/
theorem tendsto_mixing_sq_equalStrength' (hlam : 0 < lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (hq : 0 < (x 0).2 * (lam * (x 0).2 + (x 0).1)) :
    Tendsto (fun s ↦ (x s).2 ^ 2) atTop (𝓝 (flowScale * ε / (1 + lam))) := by
  have hb0 : (x 0).2 ≠ 0 := by intro h; rw [h, zero_mul] at hq; exact lt_irrefl 0 hq
  have h := tendsto_mixing_sq hlam.le hε hx (ne_zero_of_pos_mul (mixing_eq_pos_mul hx) hb0)
    (tendsto_inverseRatio_one' hlam hε hx hq)
  have e : mixingStrength lam 1 = 1 + lam := by unfold mixingStrength; ring
  rwa [e] at h

/-- Convergence to the equal-strength point on the side of the initial mixing sign (`lam > 0`). -/
theorem tendsto_equalStrength_point' (hlam : 0 < lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (hq : 0 < (x 0).2 * (lam * (x 0).2 + (x 0).1)) :
    (0 < (x 0).2 → Tendsto x atTop
        (𝓝 (equalStrengthLevel lam ε, equalStrengthLevel lam ε))) ∧
    ((x 0).2 < 0 → Tendsto x atTop
        (𝓝 (-equalStrengthLevel lam ε, -equalStrengthLevel lam ε))) := by
  have hb0 : (x 0).2 ≠ 0 := by intro h; rw [h, zero_mul] at hq; exact lt_irrefl 0 hq
  have hb := ne_zero_of_pos_mul (mixing_eq_pos_mul hx) hb0
  have hu := tendsto_inverseRatio_one' hlam hε hx hq
  have hsq := tendsto_mixing_sq_equalStrength' hlam hε hx hq
  have ha : ∀ {c : ℝ}, Tendsto (fun s ↦ (x s).2) atTop (𝓝 c) →
      Tendsto (fun s ↦ (x s).1) atTop (𝓝 c) := fun {c} hbc ↦ by
    have := hu.mul hbc
    rw [one_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with s hs
    exact div_mul_cancel₀ _ (hb s hs)
  refine ⟨fun hpos ↦ ?_, fun hneg ↦ ?_⟩
  · have hbc := tendsto_of_sq_of_pos (pos_of_pos_mul (mixing_eq_pos_mul hx) hpos) hsq
    exact (ha hbc).prodMk_nhds hbc
  · have hbc := tendsto_of_sq_of_neg (neg_of_pos_mul (mixing_eq_pos_mul hx) hneg) hsq
    exact (ha hbc).prodMk_nhds hbc

end

end ThirteenPlanes.PencilFlow.Dynamics
