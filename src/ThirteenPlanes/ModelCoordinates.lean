module

public import ThirteenPlanes.Reduction

@[expose] public section

namespace ThirteenPlanes

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The named diagonal and mixing cubics give genuine coordinates on the model family. -/
theorem modelCubics_independent {P : CubicPair V} {p q r : V} (h : EnergyTests P p q r) :
    LinearIndependent ℝ ![P.diagonalCubic, P.mixingCubic] := by
  apply (LinearIndependent.pair_iff (R := ℝ) (M := SymmetricCubic V)).mpr
  intro a b hab
  have hzero (x : V) : unitEnergy (0 : SymmetricCubic V) x = 0 := by
    simp [unitEnergy, SymmetricCubic.squareMap]
  have hc : coupling P (a, b) = 0 := by simpa only [coupling_apply] using hab
  have ha := h.energy₁ (a, b)
  have hb := h.energy₂ (a, b)
  rw [hc, hzero] at ha hb
  change 0 = a ^ 2 at ha
  change 0 = (a ^ 2 + b ^ 2) / 2 at hb
  have ha₀ : a = 0 := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ha.symm
  have hb₀ : b ^ 2 = 0 := by rw [ha₀] at hb; linarith
  exact ⟨ha₀, (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hb₀⟩

/-- The pure-plane and equal two-plane tests distinguish both homogeneous coupling coordinates. -/
theorem modelCoupling_injective {P : CubicPair V} {p q r : V} (h : EnergyTests P p q r) :
    Function.Injective (coupling P) := coupling_injective P (modelCubics_independent h)

end ThirteenPlanes
