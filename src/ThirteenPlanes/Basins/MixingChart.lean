module

public import ThirteenPlanes.Basins.Strength

@[expose] public section

set_option backward.privateInPublic true

/-! The basin of the equal-strength diagonal, in the chart `u = a/b`.

The open region `b (lam b + a) > 0` is invariant and contains the diagonal. On it `b ≠ 0`, the chart
`u = a/b` satisfies `K u' = b² (1 - u)(u + lam)` with `u + lam > 0`, and `u - 1` keeps its sign;
so `u` moves monotonically to `1`. The region contains the pure-mixing axis `a = 0`, which the
chart treats like any other direction. -/

open Set Filter Topology

namespace ThirteenPlanes

noncomputable section

variable {lam ε : ℝ} {x : ℝ → ℝ × ℝ}

/-- Lower bound for `b²` from the weighted strength in the chart `u = a/b`. -/
theorem mixing_sq_lower {lam Rlo B a b : ℝ} (hb : b ≠ 0) (hR : Rlo ≤ weightedStrength lam a b)
    (hB : (a / b) ^ 2 ≤ B) (hpos : 0 < B + 3 * lam) : Rlo / (B + 3 * lam) ≤ b ^ 2 := by
  rw [div_le_iff₀ hpos]
  have e : weightedStrength lam a b = b ^ 2 * (a / b) ^ 2 + b ^ 2 * (3 * lam) := by
    unfold weightedStrength; field_simp
  have := mul_le_mul_of_nonneg_left hB (sq_nonneg b)
  rw [e] at hR
  linarith

private theorem mul3_le {β b m u c v K : ℝ} (hβ : 0 ≤ β) (hb : β ≤ b) (hm : 0 ≤ m) (hu : m ≤ u)
    (hc : 0 ≤ c) (hv : c ≤ v) (hK : 0 < K) : β * m * c / K ≤ b * u * v / K := by
  apply div_le_div_of_nonneg_right _ hK.le
  exact mul_le_mul (mul_le_mul hb hu hm (le_trans hβ hb)) hv hc
    (mul_nonneg (le_trans hβ hb) (le_trans hm hu))

/-- In the region `b (lam b + a) > 0` the inverse ratio `a/b` tends to `1`. -/
theorem tendsto_inverseRatio_one (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (hq : 0 < (x 0).2 * (lam * (x 0).2 + (x 0).1)) :
    Tendsto (fun s ↦ (x s).1 / (x s).2) atTop (𝓝 1) := by
  have hlam0 : 0 < lam := by linarith
  have hb0 : (x 0).2 ≠ 0 := by intro h; rw [h, zero_mul] at hq; exact lt_irrefl 0 hq
  have hb := ne_zero_of_pos_mul (mixing_eq_pos_mul hx) hb0
  have hx0 : x 0 ≠ 0 := fun h ↦ hb0 (by rw [h]; rfl)
  obtain ⟨hRlo, hRle⟩ := weightedStrength_pos_lower_of_solution hlam hε hx hx0
  set Rlo := min (weightedStrength lam (x 0).1 (x 0).2) (flowScale * ε / 3)
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
  · -- `u > 1` throughout: `-u` increases to `-1`
    have hgt : ∀ s, 0 ≤ s → 1 < u s := by
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
        have := mul3_le (div_pos hRlo hpos).le hβ (show 0 ≤ -M - 1 by linarith)
          (show -M - 1 ≤ u s - 1 by linarith) (show 0 ≤ 1 + lam by linarith)
          (show 1 + lam ≤ u s + lam by linarith) flowScale_pos
        have e : -((x s).2 ^ 2 * (1 - u s) * (u s + lam) / flowScale) =
            (x s).2 ^ 2 * (u s - 1) * (u s + lam) / flowScale := by ring
        simp only [e]
        exact this)
    simpa using h.neg
  · -- `u = 1` throughout
    have heq : ∀ s, 0 ≤ s → u s = 1 := by
      intro s hs
      have h1 := zero_of_pos_mul hpm hp0 s hs
      rw [hpe s (hb s hs)] at h1
      have := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 (hb s hs))
      linarith
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with s hs
    exact (heq s hs).symm
  · -- `u < 1` throughout: `u` increases to `1`
    have hlt : ∀ s, 0 ≤ s → u s < 1 := by
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
      exact mul3_le (div_pos hRlo (by linarith)).le hβ (by linarith) (by linarith)
        hu0lam.le (by linarith) flowScale_pos

/-- In the region `b (lam b + a) > 0`, `b²` tends to `K ε / (1 + lam)`. -/
theorem tendsto_mixing_sq_equalStrength (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (hq : 0 < (x 0).2 * (lam * (x 0).2 + (x 0).1)) :
    Tendsto (fun s ↦ (x s).2 ^ 2) atTop (𝓝 (flowScale * ε / (1 + lam))) := by
  have hb0 : (x 0).2 ≠ 0 := by intro h; rw [h, zero_mul] at hq; exact lt_irrefl 0 hq
  have h := tendsto_mixing_sq (by linarith) hε hx (ne_zero_of_pos_mul (mixing_eq_pos_mul hx) hb0)
    (tendsto_inverseRatio_one hlam hε hx hq)
  have e : mixingStrength lam 1 = 1 + lam := by unfold mixingStrength; ring
  rwa [e] at h

/-- The common coordinate of the equal-strength fixed point, `√(K ε / (1 + lam))`. -/
def equalStrengthLevel (lam ε : ℝ) : ℝ := Real.sqrt (flowScale * ε / (1 + lam))

/-- Every forward solution in the region `b (lam b + a) > 0` converges to the equal-strength fixed
point on the side of its initial mixing sign. -/
theorem tendsto_equalStrength_point (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (hq : 0 < (x 0).2 * (lam * (x 0).2 + (x 0).1)) :
    (0 < (x 0).2 → Tendsto x atTop
        (𝓝 (equalStrengthLevel lam ε, equalStrengthLevel lam ε))) ∧
    ((x 0).2 < 0 → Tendsto x atTop
        (𝓝 (-equalStrengthLevel lam ε, -equalStrengthLevel lam ε))) := by
  have hb0 : (x 0).2 ≠ 0 := by intro h; rw [h, zero_mul] at hq; exact lt_irrefl 0 hq
  have hb := ne_zero_of_pos_mul (mixing_eq_pos_mul hx) hb0
  have hu := tendsto_inverseRatio_one hlam hε hx hq
  have hsq := tendsto_mixing_sq_equalStrength hlam hε hx hq
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

/-- A solution in the region `b (lam b + a) > 0` that starts with `a/b < 0` crosses the
pure-mixing axis `a = 0` at a positive time. -/
theorem exists_pureMixing_crossing (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (hq : 0 < (x 0).2 * (lam * (x 0).2 + (x 0).1)) (hu0 : (x 0).1 / (x 0).2 < 0) :
    ∃ s, 0 < s ∧ (x s).1 = 0 := by
  have hb0 : (x 0).2 ≠ 0 := by intro h; rw [h, zero_mul] at hq; exact lt_irrefl 0 hq
  have hb := ne_zero_of_pos_mul (mixing_eq_pos_mul hx) hb0
  have hu := tendsto_inverseRatio_one hlam hε hx hq
  obtain ⟨s₁, hs₁⟩ := ((hu.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).and
    (eventually_ge_atTop 0)).exists
  have hcont : ContinuousOn (fun s ↦ (x s).1 / (x s).2) (Ici 0) := fun s hs ↦
    ((solution_fst hx s hs).continuousWithinAt).div ((solution_snd hx s hs).continuousWithinAt)
      (hb s hs)
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hs₁.2 (hcont.mono Icc_subset_Ici_self)
    ⟨hu0.le, hs₁.1.le⟩
  refine ⟨r, ?_, ?_⟩
  · rcases hr.1.eq_or_lt with h | h
    · rw [← h] at hr0; simp only at hr0; linarith
    · exact h
  · simp only at hr0
    exact (div_eq_zero_iff.mp hr0).resolve_right (hb r hr.1)

/-- The common scale of the fixed point on the third line, `√(K ε / ((lam + 1)(lam + 2)))`. -/
def thirdLineLevel (lam ε : ℝ) : ℝ := Real.sqrt (flowScale * ε / ((lam + 1) * (lam + 2)))

/-- A forward solution starting on the third stationary line `a = -lam b`, `b ≠ 0`, stays on it
and converges to the fixed point there on the side of its initial mixing sign. -/
theorem tendsto_thirdLine_point (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (hline : (x 0).1 = -lam * (x 0).2) :
    (0 < (x 0).2 → Tendsto x atTop
        (𝓝 (-lam * thirdLineLevel lam ε, thirdLineLevel lam ε))) ∧
    ((x 0).2 < 0 → Tendsto x atTop
        (𝓝 (lam * thirdLineLevel lam ε, -thirdLineLevel lam ε))) := by
  have hlam0 : 0 < lam := by linarith
  have hl := thirdLine_invariant hlam0.ne' hx hline
  have key : (x 0).2 ≠ 0 → Tendsto (fun s ↦ (x s).2 ^ 2) atTop
      (𝓝 (flowScale * ε / ((lam + 1) * (lam + 2)))) := fun hb0 ↦ by
    have hb := ne_zero_of_pos_mul (mixing_eq_pos_mul hx) hb0
    have hu : Tendsto (fun s ↦ (x s).1 / (x s).2) atTop (𝓝 (-lam)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with s hs
      rw [hl s hs, mul_div_cancel_right₀ _ (hb s hs)]
    have h := tendsto_mixing_sq hlam0.le hε hx hb hu
    have e : mixingStrength lam (-lam) = (lam + 1) * (lam + 2) := by
      unfold mixingStrength; ring
    rwa [e] at h
  have ha : ∀ {c : ℝ}, Tendsto (fun s ↦ (x s).2) atTop (𝓝 c) →
      Tendsto (fun s ↦ (x s).1) atTop (𝓝 (-lam * c)) := fun {c} hbc ↦ by
    refine (hbc.const_mul (-lam)).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with s hs
    exact (hl s hs).symm
  refine ⟨fun hpos ↦ ?_, fun hneg ↦ ?_⟩
  · have hbc := tendsto_of_sq_of_pos (pos_of_pos_mul (mixing_eq_pos_mul hx) hpos)
      (key hpos.ne')
    exact (ha hbc).prodMk_nhds hbc
  · have hbc := tendsto_of_sq_of_neg (neg_of_pos_mul (mixing_eq_pos_mul hx) hneg)
      (key hneg.ne)
    have := (ha hbc).prodMk_nhds hbc
    simp only [mul_neg, neg_mul, neg_neg] at this
    exact this

end

end ThirteenPlanes
