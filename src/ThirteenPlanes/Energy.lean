module

public import ThirteenPlanes.Contracts

@[expose] public section

/-! Energy of unit fields on the homogeneous coupling family.

From three marked unit fields with energies `a²`, `(a²+b²)/2`, `(a²+ab+b²)/3` and the square law of
the equal-strength cubic, the unit-sphere energy of `aD + bC` is direction-independent exactly when
`a = b`, with common value `a²`. At `(a,b) = (1,t)` this is `t = 1` with common value one, and the two
shared-field energies recover the ratio as `t = 3E₃ - 2E₂`. -/

namespace ThirteenPlanes

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A real function on `V` is constant on the unit sphere with value `c`. -/
def ConstantOnSphere (f : V → ℝ) (c : ℝ) : Prop :=
  ∀ x : V, ‖x‖ = 1 → f x = c

/-- On the equal-strength ray the unit energy of every unit field is `a²`. -/
theorem unitEnergy_same {P : CubicPair V} (law : HasSquareLaw (interactionCubic P 1)) (a : ℝ)
    {x : V} (hx : ‖x‖ = 1) : unitEnergy (coupling P (a, a)) x = a ^ 2 := by
  rw [unitEnergy, coupling_same, SymmetricCubic.squareMap_smul, norm_smul, mul_pow, law x, hx,
    Real.norm_eq_abs, sq_abs]
  ring

/-- The unit energy of `aD + bC` is the same on the whole unit sphere iff `a = b`; the common value
is then `a²`. -/
theorem unitEnergy_constant_iff {P : CubicPair V} {n₁ n₂ n₃ : V} (T : EnergyTests P n₁ n₂ n₃)
    (u : ℝ × ℝ) :
    (∃ c, ConstantOnSphere (unitEnergy (coupling P u)) c) ↔ u.1 = u.2 := by
  constructor
  · rintro ⟨c, hc⟩
    have e₁ := (hc n₁ T.unit₁).trans (hc n₂ T.unit₂).symm
    have e₂ := (hc n₁ T.unit₁).trans (hc n₃ T.unit₃).symm
    rw [T.energy₁, T.energy₂] at e₁
    rw [T.energy₁, T.energy₃] at e₂
    have hsq : u.1 * (u.1 - u.2) = 0 := by linear_combination 3 * e₂ - 2 * e₁
    rcases mul_eq_zero.mp hsq with h0 | h0
    · have : u.2 ^ 2 = 0 := by rw [h0] at e₁; linear_combination -2 * e₁
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      rw [h0, this]
    · linarith
  · intro h
    refine ⟨u.1 ^ 2, fun x hx => ?_⟩
    rcases u with ⟨a, b⟩
    simp only at h
    subst h
    exact unitEnergy_same T.squareLaw a hx

/-- The common value of a direction-independent unit energy on the family is `a²`. -/
theorem unitEnergy_constant_value {P : CubicPair V} {n₁ n₂ n₃ : V} (T : EnergyTests P n₁ n₂ n₃)
    (u : ℝ × ℝ) {c : ℝ} (hc : ConstantOnSphere (unitEnergy (coupling P u)) c) : c = u.1 ^ 2 :=
  (hc n₁ T.unit₁).symm.trans (T.energy₁ u)

/-- At `(1,t)` the unit-sphere energy is direction-independent iff `t = 1`, and then equals one. -/
theorem unitEnergy_constant_iff_mixingRatio_eq_one {P : CubicPair V} {n₁ n₂ n₃ : V}
    (T : EnergyTests P n₁ n₂ n₃) (t : ℝ) :
    (∃ c, ConstantOnSphere (unitEnergy (interactionCubic P t)) c) ↔ t = 1 := by
  rw [interactionCubic, unitEnergy_constant_iff T (1, t), eq_comm]

/-- At ratio one every unit field has unit energy one. -/
theorem unitEnergy_interactionCubic_one {P : CubicPair V} {n₁ n₂ n₃ : V}
    (T : EnergyTests P n₁ n₂ n₃) : ConstantOnSphere (unitEnergy (interactionCubic P 1)) 1 := by
  intro x hx
  have := unitEnergy_same T.squareLaw 1 hx
  rw [coupling_same, one_smul] at this
  simpa using this

/-- The two shared-field energies at `(1,t)` recover the ratio: `t = 3E₃ - 2E₂`. -/
theorem mixingRatio_eq_of_energies {P : CubicPair V} {n₁ n₂ n₃ : V}
    (T : EnergyTests P n₁ n₂ n₃) (t : ℝ) :
    t = 3 * unitEnergy (interactionCubic P t) n₃ - 2 * unitEnergy (interactionCubic P t) n₂ := by
  rw [interactionCubic, T.energy₂, T.energy₃]
  ring

end

end ThirteenPlanes
