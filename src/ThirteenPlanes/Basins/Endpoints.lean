module

public import ThirteenPlanes.Basins.Global
public import ThirteenPlanes.Basins.Existence

@[expose] public section

/-! Basin statements in the chart `g = a`, `t = b/a`, at general `lam ≥ 1/2` and at the two
physical values `lam = 2` (26 fields) and `lam = 1/2` (eight fields). -/

open Set Filter Topology

namespace ThirteenPlanes

noncomputable section

variable {lam ε : ℝ} {x : ℝ → ℝ × ℝ}

/-- In the region `b (lam b + a) > 0`: the ratio `b/a` tends to `1` and `a²/K` to
`ε / (1 + lam)`. -/
theorem equalStrength_basin_chart (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (hq : 0 < (x 0).2 * (lam * (x 0).2 + (x 0).1)) :
    Tendsto (fun s ↦ (x s).2 / (x s).1) atTop (𝓝 1) ∧
    Tendsto (fun s ↦ (x s).1 ^ 2 / flowScale) atTop (𝓝 (ε / (1 + lam))) := by
  have hb0 : (x 0).2 ≠ 0 := by intro h; rw [h, zero_mul] at hq; exact lt_irrefl 0 hq
  have hb := ne_zero_of_pos_mul (mixing_eq_pos_mul hx) hb0
  have hu := tendsto_inverseRatio_one hlam hε hx hq
  have hsq := tendsto_mixing_sq_equalStrength hlam hε hx hq
  refine ⟨?_, ?_⟩
  · have := hu.inv₀ one_ne_zero
    rw [inv_one] at this
    refine this.congr' ?_
    filter_upwards with s
    rw [inv_div]
  · have := ((hu.pow 2).mul hsq).div_const flowScale
    rw [one_pow, one_mul] at this
    have e : flowScale * ε / (1 + lam) / flowScale = ε / (1 + lam) := by
      field_simp [flowScale_ne_zero]
    rw [e] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with s hs
    rw [← mul_pow, div_mul_cancel₀ _ (hb s hs)]

/-- For initial ratio in `(-1/lam, 0]`: the ratio `b/a` tends to `0` and `a²/K` to `ε`. -/
theorem decoupled_basin_chart (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (ha0 : (x 0).1 ≠ 0) (hlo : -1 / lam < (x 0).2 / (x 0).1) (hhi : (x 0).2 / (x 0).1 ≤ 0) :
    Tendsto (fun s ↦ (x s).2 / (x s).1) atTop (𝓝 0) ∧
    Tendsto (fun s ↦ (x s).1 ^ 2 / flowScale) atTop (𝓝 ε) := by
  obtain ⟨ha, -, ht⟩ := tendsto_ratio_zero hlam hε hx ha0 hlo hhi
  have hsq := tendsto_diag_sq hε hx ha ht (by rw [strengthPolynomial_eq]; norm_num)
  refine ⟨ht, ?_⟩
  have := hsq.div_const flowScale
  rw [strengthPolynomial_eq] at this
  convert this using 2
  field_simp [flowScale_ne_zero]
  ring

/-! ### Thirteen planes, `lam = 2` -/

/-- Thirteen planes: along every forward solution the weighted squared strength stays between
two positive constants. -/
theorem twentySix_strength_bounds (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField 2 ε) (Ici 0)) (h0 : x 0 ≠ 0) :
    ∃ r R : ℝ, 0 < r ∧ ∀ t, 0 ≤ t →
      r ≤ weightedStrength 2 (x t).1 (x t).2 ∧ weightedStrength 2 (x t).1 (x t).2 ≤ R := by
  obtain ⟨hpos, hle⟩ := weightedStrength_pos_lower_of_solution (by norm_num) hε hx h0
  exact ⟨_, _, hpos, fun t ht ↦ ⟨hle t ht, weightedStrength_le_of_solution (by norm_num) hx t ht⟩⟩

/-- Thirteen planes: if initially `b ≠ 0` and either `a = 0` or `t = b/a ∉ [-1/2, 0]`, then
`t → 1`, `a²/K → ε/3`, the coupling converges to the equal-strength fixed point with the sign of
`b`, and a solution starting with `t < -1/2` crosses the pure-mixing axis. -/
theorem twentySix_basin_equalStrength (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField 2 ε) (Ici 0)) (hb0 : (x 0).2 ≠ 0)
    (hchart : (x 0).1 = 0 ∨ (x 0).2 / (x 0).1 ∉ Icc (-1 / 2) 0) :
    Tendsto (fun s ↦ (x s).2 / (x s).1) atTop (𝓝 1) ∧
    Tendsto (fun s ↦ (x s).1 ^ 2 / flowScale) atTop (𝓝 (ε / 3)) ∧
    (0 < (x 0).2 → Tendsto x atTop (𝓝 (equalStrengthLevel 2 ε, equalStrengthLevel 2 ε))) ∧
    ((x 0).2 < 0 → Tendsto x atTop (𝓝 (-equalStrengthLevel 2 ε, -equalStrengthLevel 2 ε))) ∧
    ((x 0).1 ≠ 0 → (x 0).2 / (x 0).1 < -1 / 2 → ∃ s, 0 < s ∧ (x s).1 = 0) := by
  have hq := sectorQ_pos_of_chart (lam := 2) (by norm_num) hb0 hchart
  obtain ⟨h1, h2⟩ := equalStrength_basin_chart (by norm_num) hε hx hq
  obtain ⟨h3, h4⟩ := tendsto_equalStrength_point (by norm_num) hε hx hq
  refine ⟨h1, by norm_num at h2 ⊢; exact h2, h3, h4, fun ha0 ht ↦ ?_⟩
  apply exists_pureMixing_crossing (by norm_num) hε hx hq
  have hpos : 0 < (x 0).2 / (x 0).1 * ((x 0).1 / (x 0).2) := by
    rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero ha0 hb0)]; norm_num
  have htneg : (x 0).2 / (x 0).1 < 0 := by linarith
  by_contra h
  rw [not_lt] at h
  nlinarith

/-- Thirteen planes: if initially `a ≠ 0` and `-1/2 < t = b/a < 0`, then `t → 0`, `a²/K → ε`,
and the coupling converges to the decoupled fixed point with the sign of `a`. -/
theorem twentySix_basin_decoupled (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField 2 ε) (Ici 0)) (ha0 : (x 0).1 ≠ 0)
    (hlo : -1 / 2 < (x 0).2 / (x 0).1) (hhi : (x 0).2 / (x 0).1 < 0) :
    Tendsto (fun s ↦ (x s).2 / (x s).1) atTop (𝓝 0) ∧
    Tendsto (fun s ↦ (x s).1 ^ 2 / flowScale) atTop (𝓝 ε) ∧
    (0 < (x 0).1 → Tendsto x atTop (𝓝 (decoupledLevel ε, 0))) ∧
    ((x 0).1 < 0 → Tendsto x atTop (𝓝 (-decoupledLevel ε, 0))) := by
  obtain ⟨h1, h2⟩ := decoupled_basin_chart (by norm_num) hε hx ha0 hlo hhi.le
  obtain ⟨h3, h4⟩ := tendsto_decoupled_point (by norm_num) hε hx ha0 hlo hhi.le
  exact ⟨h1, h2, h3, h4⟩

/-! ### Four planes, `lam = 1/2` -/

/-- Four planes: if initially `a ≠ 0` and `0 < t = b/a < 1`, then `(a²/K, t)` converges to the
fixed point `(2ε/3, 1)`. (The hypotheses `a ≠ 0` and `t < 1` are implied or unnecessary: every
`t > 0` lies in the same basin.) -/
theorem eight_basin_equalStrength (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField (1 / 2) ε) (Ici 0)) (_ha0 : (x 0).1 ≠ 0)
    (hlo : 0 < (x 0).2 / (x 0).1) (_hhi : (x 0).2 / (x 0).1 < 1) :
    Tendsto (fun s ↦ ((x s).1 ^ 2 / flowScale, (x s).2 / (x s).1)) atTop
      (𝓝 (2 * ε / 3, 1)) := by
  have hb0 : (x 0).2 ≠ 0 := by intro h; rw [h, zero_div] at hlo; exact lt_irrefl 0 hlo
  have hq := sectorQ_pos_of_chart (lam := 1 / 2) (by norm_num) hb0
    (Or.inr fun h ↦ absurd h.2 (not_le.mpr hlo))
  obtain ⟨h1, h2⟩ := equalStrength_basin_chart (by norm_num) hε hx hq
  have e : ε / (1 + 1 / 2) = 2 * ε / 3 := by ring
  rw [e] at h2
  exact h2.prodMk_nhds h1

/-- Four planes: if initially `a ≠ 0` and `-2 < t = b/a < 0`, then `(a²/K, t)` converges to the
fixed point `(ε, 0)`. -/
theorem eight_basin_decoupled (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField (1 / 2) ε) (Ici 0)) (ha0 : (x 0).1 ≠ 0)
    (hlo : -2 < (x 0).2 / (x 0).1) (hhi : (x 0).2 / (x 0).1 < 0) :
    Tendsto (fun s ↦ ((x s).1 ^ 2 / flowScale, (x s).2 / (x s).1)) atTop (𝓝 (ε, 0)) := by
  obtain ⟨h1, h2⟩ := decoupled_basin_chart (lam := 1 / 2) (by norm_num) hε hx ha0
    (by norm_num; linarith) hhi.le
  exact h2.prodMk_nhds h1

/-- The eight-field acceptance statement: the fixed-point table at `t = 1, -2, 0` with both signs
of `g ≠ 0`, the strength exponent `+ε`, the ratio exponents and dimensions, and convergence of
`(g²/K, t)` from the two ratio intervals `(0, 1)` and `(-2, 0)`. -/
theorem eight_acceptance (hε : 0 < ε) :
    (∀ a t : ℝ, a ≠ 0 → (familyField (1 / 2) ε (a, a * t) = 0 ↔
      (t = 1 ∧ a ^ 2 / flowScale = 2 * ε / 3) ∨ (t = -2 ∧ a ^ 2 / flowScale = ε / 15) ∨
      (t = 0 ∧ a ^ 2 / flowScale = ε))) ∧
    (∀ t : ℝ, t = 1 ∨ t = -2 ∨ t = 0 → ∃ a : ℝ, 0 < a ∧
      familyField (1 / 2) ε (a, a * t) = 0 ∧ familyField (1 / 2) ε (-a, -a * t) = 0) ∧
    (∀ a t : ℝ, a ≠ 0 → familyField (1 / 2) ε (a, a * t) = 0 →
      HasDerivAt (fun y ↦ (chartField (1 / 2) ε (y, t)).1) (-ε) a ∧
      ((t = 1 ∧ ratioExponent (1 / 2) a t = ε ∧
          scalarDimension (1 / 2) ε a t = 1 - 2 * ε / 9) ∨
        (t = -2 ∧ ratioExponent (1 / 2) a t = -2 * ε / 5 ∧
          scalarDimension (1 / 2) ε a t = 1 - 19 * ε / 45) ∨
        (t = 0 ∧ ratioExponent (1 / 2) a t = 0 ∧ scalarDimension (1 / 2) ε a t = 1 - ε / 3))) ∧
    (∀ x : ℝ → ℝ × ℝ, IsIntegralCurveOn x (fun _ ↦ familyField (1 / 2) ε) (Ici 0) →
      (x 0).1 ≠ 0 → 0 < (x 0).2 / (x 0).1 → (x 0).2 / (x 0).1 < 1 →
      Tendsto (fun s ↦ ((x s).1 ^ 2 / flowScale, (x s).2 / (x s).1)) atTop
        (𝓝 (2 * ε / 3, 1))) ∧
    (∀ x : ℝ → ℝ × ℝ, IsIntegralCurveOn x (fun _ ↦ familyField (1 / 2) ε) (Ici 0) →
      (x 0).1 ≠ 0 → -2 < (x 0).2 / (x 0).1 → (x 0).2 / (x 0).1 < 0 →
      Tendsto (fun s ↦ ((x s).1 ^ 2 / flowScale, (x s).2 / (x s).1)) atTop (𝓝 (ε, 0))) :=
  ⟨fun _ _ ha ↦ eight_fixed_iff ha, fun _ ht ↦ eight_fixed_exists_at_ratio hε ht,
    fun _ _ ha hf ↦ ⟨(chartLinearization_at_fixed ha hf).1, eight_stationary_scaling ha hf⟩,
    fun _ hx ha hlo hhi ↦ eight_basin_equalStrength hε hx ha hlo hhi,
    fun _ hx ha hlo hhi ↦ eight_basin_decoupled hε hx ha hlo hhi⟩

/-- Thirteen planes, acceptance form: the fixed-point table at `t = 1, -1/2, 0` with both signs of
`g ≠ 0`, the strength exponent `+ε`, the ratio exponents and dimensions, and the two basins. -/
theorem twentySix_acceptance (hε : 0 < ε) :
    (∀ a t : ℝ, a ≠ 0 → (familyField 2 ε (a, a * t) = 0 ↔
      (t = 1 ∧ a ^ 2 / flowScale = ε / 3) ∨ (t = -1 / 2 ∧ a ^ 2 / flowScale = ε / 3) ∨
      (t = 0 ∧ a ^ 2 / flowScale = ε))) ∧
    (∀ t : ℝ, t = 1 ∨ t = -1 / 2 ∨ t = 0 → ∃ a : ℝ, 0 < a ∧
      familyField 2 ε (a, a * t) = 0 ∧ familyField 2 ε (-a, -a * t) = 0) ∧
    (∀ a t : ℝ, a ≠ 0 → familyField 2 ε (a, a * t) = 0 →
      HasDerivAt (fun y ↦ (chartField 2 ε (y, t)).1) (-ε) a ∧
      ((t = 1 ∧ ratioExponent 2 a t = ε ∧ scalarDimension 2 ε a t = 1 - ε / 9) ∨
        (t = -1 / 2 ∧ ratioExponent 2 a t = -ε / 4 ∧
          scalarDimension 2 ε a t = 1 - 13 * ε / 36) ∨
        (t = 0 ∧ ratioExponent 2 a t = 0 ∧ scalarDimension 2 ε a t = 1 - ε / 3))) ∧
    (∀ x : ℝ → ℝ × ℝ, IsIntegralCurveOn x (fun _ ↦ familyField 2 ε) (Ici 0) →
      (x 0).2 ≠ 0 → ((x 0).1 = 0 ∨ (x 0).2 / (x 0).1 ∉ Icc (-1 / 2) 0) →
      Tendsto (fun s ↦ ((x s).1 ^ 2 / flowScale, (x s).2 / (x s).1)) atTop
        (𝓝 (ε / 3, 1))) ∧
    (∀ x : ℝ → ℝ × ℝ, IsIntegralCurveOn x (fun _ ↦ familyField 2 ε) (Ici 0) →
      (x 0).1 ≠ 0 → -1 / 2 < (x 0).2 / (x 0).1 → (x 0).2 / (x 0).1 < 0 →
      Tendsto (fun s ↦ ((x s).1 ^ 2 / flowScale, (x s).2 / (x s).1)) atTop (𝓝 (ε, 0))) :=
  ⟨fun _ _ ha ↦ twentySix_fixed_iff ha, fun _ ht ↦ twentySix_fixed_exists_at_ratio hε ht,
    fun _ _ ha hf ↦ ⟨(chartLinearization_at_fixed ha hf).1, twentySix_stationary_scaling ha hf⟩,
    fun _ hx hb h ↦ by
      obtain ⟨h1, h2, -⟩ := twentySix_basin_equalStrength hε hx hb h
      exact h2.prodMk_nhds h1,
    fun _ hx ha hlo hhi ↦ by
      obtain ⟨h1, h2, -⟩ := twentySix_basin_decoupled hε hx ha hlo hhi
      exact h2.prodMk_nhds h1⟩

/-- For `lam ≥ 1/2` and `ε > 0`, every initial coupling away from the origin has a unique forward
solution on `[0, ∞)`, and it converges to a nonzero fixed point. -/
theorem existsUnique_forward_solution_tendsto_fixedPoint (hlam : 1 / 2 ≤ lam) (hε : 0 < ε)
    {x₀ : ℝ × ℝ} (h0 : x₀ ≠ 0) :
    ∃ x : ℝ → ℝ × ℝ, x 0 = x₀ ∧ IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0) ∧
      (∀ y : ℝ → ℝ × ℝ, y 0 = x₀ → IsIntegralCurveOn y (fun _ ↦ familyField lam ε) (Ici 0) →
        EqOn y x (Ici 0)) ∧
      ∃ p : ℝ × ℝ, p ≠ 0 ∧ familyField lam ε p = 0 ∧ Tendsto x atTop (𝓝 p) := by
  have hlam0 : 0 < lam := by linarith
  obtain ⟨x, hx0, hx⟩ := exists_forward_solution hlam0 ε x₀
  refine ⟨x, hx0, hx, fun y hy0 hy ↦ forward_solution_unique hlam0 hy hx (hy0.trans hx0.symm),
    exists_tendsto_fixedPoint hlam hε hx (by rwa [hx0])⟩

end

end ThirteenPlanes
