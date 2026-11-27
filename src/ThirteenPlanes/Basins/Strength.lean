module

public import ThirteenPlanes.Basins.Invariant

@[expose] public section

/-! Convergence of the strength once the direction converges.

In the chart `u = a/b` (where `b ≠ 0`) the reciprocal `1/b²` obeys a linear equation
`v' = -ε v + mixingStrength(u)/K`; in the chart `t = b/a` (where `a ≠ 0`) the reciprocal `1/a²`
obeys `w' = -ε w + strengthPolynomial(t)/K`. Convergent forcing gives convergent strength. -/

open Set Filter Topology

namespace ThirteenPlanes

noncomputable section

variable {lam ε : ℝ} {x : ℝ → ℝ × ℝ}

/-- Strength coefficient in the chart `b = h`, `a = h * u`. -/
def mixingStrength (lam u : ℝ) : ℝ := u ^ 2 - 2 * u + 2 + lam

theorem mixingStrength_pos {lam : ℝ} (hlam : 0 ≤ lam) (u : ℝ) : 0 < mixingStrength lam u := by
  unfold mixingStrength
  nlinarith [sq_nonneg (u - 1)]

theorem continuous_mixingStrength (lam : ℝ) : Continuous (mixingStrength lam) := by
  unfold mixingStrength
  fun_prop

theorem continuous_strengthPolynomial (lam : ℝ) : Continuous (strengthPolynomial lam) := by
  have : strengthPolynomial lam = fun t ↦ 1 + lam * t ^ 2 * (3 - 2 * t) :=
    funext (strengthPolynomial_eq lam)
  rw [this]
  fun_prop

/-- The reciprocal squared mixing coordinate obeys a forced linear equation. -/
theorem hasDerivWithinAt_inv_mixing_sq
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (hb : ∀ s, 0 ≤ s → (x s).2 ≠ 0) :
    ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun r ↦ ((x r).2 ^ 2)⁻¹)
      (-ε * ((x s).2 ^ 2)⁻¹ + mixingStrength lam ((x s).1 / (x s).2) / flowScale) (Ici 0) s := by
  intro s hs
  have hbs := hb s hs
  have h := ((solution_snd hx s hs).pow 2).inv (pow_ne_zero 2 hbs)
  convert h using 1
  simp only [Pi.pow_apply]
  rw [familyField_mixing_factor]
  simp only [mixingStrength, familyM, flowScale, Nat.cast_ofNat]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The reciprocal squared decoupled coordinate obeys a forced linear equation. -/
theorem hasDerivWithinAt_inv_diag_sq
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (ha : ∀ s, 0 ≤ s → (x s).1 ≠ 0) :
    ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun r ↦ ((x r).1 ^ 2)⁻¹)
      (-ε * ((x s).1 ^ 2)⁻¹ + strengthPolynomial lam ((x s).2 / (x s).1) / flowScale)
      (Ici 0) s := by
  intro s hs
  have has := ha s hs
  have h := ((solution_fst hx s hs).pow 2).inv (pow_ne_zero 2 has)
  convert h using 1
  simp only [Pi.pow_apply]
  have hstr := familyField_strength lam ε (x s).1 ((x s).2 / (x s).1)
  rw [mul_div_cancel₀ _ has] at hstr
  have hK := flowScale_ne_zero
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)] at hstr
  have e : (familyField lam ε ((x s).1, (x s).2)).1 =
      (flowScale * ε * (x s).1 - strengthPolynomial lam ((x s).2 / (x s).1) * (x s).1 ^ 3) /
        (2 * flowScale) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hK)]
    linear_combination hstr
  rw [e]
  field_simp
  ring

/-- If the inverse ratio `a/b` converges, so does `b²`, to `K ε / mixingStrength`. -/
theorem tendsto_mixing_sq (hlam : 0 ≤ lam) (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (hb : ∀ s, 0 ≤ s → (x s).2 ≠ 0) {U : ℝ}
    (hu : Tendsto (fun s ↦ (x s).1 / (x s).2) atTop (𝓝 U)) :
    Tendsto (fun s ↦ (x s).2 ^ 2) atTop (𝓝 (flowScale * ε / mixingStrength lam U)) := by
  have hF : Tendsto (fun s ↦ mixingStrength lam ((x s).1 / (x s).2) / flowScale) atTop
      (𝓝 (mixingStrength lam U / flowScale)) :=
    (((continuous_mixingStrength lam).tendsto U).comp hu).div_const _
  have hv := tendsto_of_forced_linear hε (hasDerivWithinAt_inv_mixing_sq hx hb) hF
  have hne : mixingStrength lam U / flowScale / ε ≠ 0 :=
    div_ne_zero (div_ne_zero (mixingStrength_pos hlam U).ne' flowScale_ne_zero) hε.ne'
  have := hv.inv₀ hne
  simp only [inv_inv] at this
  convert this using 2
  field_simp

/-- If the ratio `b/a` converges, so does `a²`, to `K ε / strengthPolynomial`. -/
theorem tendsto_diag_sq (hε : 0 < ε)
    (hx : IsIntegralCurveOn x (fun _ ↦ familyField lam ε) (Ici 0))
    (ha : ∀ s, 0 ≤ s → (x s).1 ≠ 0) {T : ℝ}
    (ht : Tendsto (fun s ↦ (x s).2 / (x s).1) atTop (𝓝 T))
    (hS : 0 < strengthPolynomial lam T) :
    Tendsto (fun s ↦ (x s).1 ^ 2) atTop (𝓝 (flowScale * ε / strengthPolynomial lam T)) := by
  have hF : Tendsto (fun s ↦ strengthPolynomial lam ((x s).2 / (x s).1) / flowScale) atTop
      (𝓝 (strengthPolynomial lam T / flowScale)) :=
    (((continuous_strengthPolynomial lam).tendsto T).comp ht).div_const _
  have hv := tendsto_of_forced_linear hε (hasDerivWithinAt_inv_diag_sq hx ha) hF
  have hne : strengthPolynomial lam T / flowScale / ε ≠ 0 :=
    div_ne_zero (div_ne_zero hS.ne' flowScale_ne_zero) hε.ne'
  have := hv.inv₀ hne
  simp only [inv_inv] at this
  convert this using 2
  field_simp

/-- A function of constant positive sign whose square converges to `L > 0` converges to `√L`. -/
theorem tendsto_of_sq_of_pos {f : ℝ → ℝ} {L : ℝ} (hf : ∀ s, 0 ≤ s → 0 < f s)
    (hsq : Tendsto (fun s ↦ f s ^ 2) atTop (𝓝 L)) : Tendsto f atTop (𝓝 (Real.sqrt L)) := by
  have h := (Real.continuous_sqrt.tendsto L).comp hsq
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with s hs
  simp [Real.sqrt_sq (hf s hs).le]

/-- A function of constant negative sign whose square converges to `L` converges to `-√L`. -/
theorem tendsto_of_sq_of_neg {f : ℝ → ℝ} {L : ℝ} (hf : ∀ s, 0 ≤ s → f s < 0)
    (hsq : Tendsto (fun s ↦ f s ^ 2) atTop (𝓝 L)) : Tendsto f atTop (𝓝 (-Real.sqrt L)) := by
  have h := tendsto_of_sq_of_pos (f := fun s ↦ -f s) (fun s hs ↦ neg_pos.mpr (hf s hs))
    (by simpa using hsq)
  simpa using h.neg

end

end ThirteenPlanes
