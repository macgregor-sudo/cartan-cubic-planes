module

public import ThirteenPlanes.Weyl
public import ThirteenPlanes.SignedPair

@[expose] public section

namespace ThirteenPlanes
noncomputable section

/-- Evaluation of the ternary character indexed by χ on the grade x. -/
def chargeWeight (χ x : Charge) : ZMod 3 := ∑ i, χ i * x i

theorem chargeWeight_add_grade (χ x y : Charge) :
    chargeWeight χ (x+y) = chargeWeight χ x + chargeWeight χ y := by
  simp [chargeWeight, mul_add, Finset.sum_add_distrib]

theorem chargeWeight_neg (χ x : Charge) : chargeWeight χ (-x) = -chargeWeight χ x := by
  simp [chargeWeight, Finset.sum_neg_distrib]

theorem chargePhase_norm (a : ZMod 3) : ‖chargePhase a‖ = 1 := by
  have eqn := congrArg norm (chargePhase_add a (-a))
  rw [add_neg_cancel, chargePhase_zero, norm_one, norm_mul, chargePhase_neg,
    norm_star] at eqn
  nlinarith [norm_nonneg (chargePhase a)]

def chargeActionMap (χ : Charge) : SignedField →ₗ[ℝ] SignedField where
  toFun x := (⟨fun i => chargePhase (chargeWeight χ i.val) * signedCoordinates x i, by
    intro i
    change chargePhase (chargeWeight χ (-i.val)) * signedCoordinates x (oppositeCharge i) = _
    rw [chargeWeight_neg, chargePhase_neg, (show signedCoordinates x (oppositeCharge i) =
      star (signedCoordinates x i) from x.property i)]
    simp⟩ : ↥signedFields)
  map_add' x y := by
    apply Subtype.ext; funext i
    change chargePhase _ * (signedCoordinates (x+y) i) =
      chargePhase _ * signedCoordinates x i + chargePhase _ * signedCoordinates y i
    simp [mul_add]
  map_smul' r x := by
    apply Subtype.ext; funext i
    change chargePhase _ * signedCoordinates (r • x) i =
      r • (chargePhase _ * signedCoordinates x i)
    simp; ring

@[simp] theorem chargeActionMap_apply (χ : Charge) (x : SignedField) (i : NonzeroCharge) :
    signedCoordinates (chargeActionMap χ x) i =
      chargePhase (chargeWeight χ i.val) * signedCoordinates x i := rfl

theorem chargeActionMap_add (χ ψ : Charge) (x : SignedField) :
    chargeActionMap (χ+ψ) x = chargeActionMap χ (chargeActionMap ψ x) := by
  apply Subtype.ext; funext i
  change chargePhase (chargeWeight (χ+ψ) i.val) * _ = _ * (_ * _)
  simp [chargeWeight, add_mul, Finset.sum_add_distrib, chargePhase_add, mul_assoc]

@[simp] theorem chargeActionMap_zero (x : SignedField) : chargeActionMap 0 x = x := by
  apply Subtype.ext; funext i
  change chargePhase (chargeWeight 0 i.val) * _ = _
  simp [chargeWeight]; rfl

def chargeAction (χ : Charge) : SignedField ≃ₗᵢ[ℝ] SignedField where
  __ := chargeActionMap χ
  invFun := chargeActionMap (-χ)
  left_inv x := by change chargeActionMap (-χ) (chargeActionMap χ x) = x; rw [← chargeActionMap_add, neg_add_cancel, chargeActionMap_zero]
  right_inv x := by change chargeActionMap χ (chargeActionMap (-χ) x) = x; rw [← chargeActionMap_add, add_neg_cancel, chargeActionMap_zero]
  norm_map' x := by
    change ‖chargeActionMap χ x‖ = ‖x‖
    have h : ‖chargeActionMap χ x‖ ^ 2 = ‖x‖ ^ 2 := by
      simp [signedField_norm_sq, chargePhase_norm]
    nlinarith [norm_nonneg (chargeActionMap χ x), norm_nonneg x]

theorem chargePhase_triple_of_sum_zero (χ : Charge) {i j k : NonzeroCharge}
    (h : i.val + j.val + k.val = 0) :
    chargePhase (chargeWeight χ i.val) * chargePhase (chargeWeight χ j.val) *
      chargePhase (chargeWeight χ k.val) = 1 := by
  rw [← chargePhase_add, ← chargeWeight_add_grade, ← chargePhase_add, ← chargeWeight_add_grade, h]
  simp [chargeWeight]

theorem chargeAction_preserves_full (χ : Charge) (x y z : SignedField) :
    signedEqualCubic.apply (chargeAction χ x) (chargeAction χ y) (chargeAction χ z) =
      signedEqualCubic.apply x y z := by
  simp only [signedEqualCubic_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : i.val+j.val+k.val=0
  · change (signedCoefficient i j k * (chargePhase _ * signedCoordinates x i) * (chargePhase _ * signedCoordinates y j) * (chargePhase _ * signedCoordinates z k)).re = _
    apply congrArg Complex.re
    linear_combination (signedCoefficient i j k * signedCoordinates x i * signedCoordinates y j *
      signedCoordinates z k) * (chargePhase_triple_of_sum_zero χ h)
  · simp [signedCoefficient_zero_of_grade_sum_ne_zero i j k h]

theorem chargeAction_preserves_diagonal (χ : Charge) (x y z : SignedField) :
    signedDiagonalCubic.apply (chargeAction χ x) (chargeAction χ y) (chargeAction χ z) =
      signedDiagonalCubic.apply x y z := by
  rw [signedDiagonalCubic_sum, signedDiagonalCubic_sum]
  apply congrArg (fun a : ℝ => 3 * a)
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : i.val + i.val + i.val = 0 := by
    funext j
    change i.val j + i.val j + i.val j = 0
    linear_combination i.val j * (by decide : (3 : ZMod 3) = 0)
  change ((chargePhase _ * signedCoordinates x i) * (chargePhase _ * signedCoordinates y i) * (chargePhase _ * signedCoordinates z i)).re = _
  apply congrArg Complex.re
  linear_combination (signedCoordinates x i * signedCoordinates y i * signedCoordinates z i) *
    (chargePhase_triple_of_sum_zero χ h)

/-- The charge symmetry preserves the entire homogeneous family, including pure mixing. -/
theorem chargeAction_preserves_coupling (χ : Charge) (u : ℝ × ℝ) (x y z : SignedField) :
    (coupling signedPair u).apply (chargeAction χ x) (chargeAction χ y) (chargeAction χ z) =
    (coupling signedPair u).apply x y z := by
  have split : coupling signedPair u =
      (u.1-u.2) • signedDiagonalCubic + u.2 • signedEqualCubic := by
    rw [coupling_apply]
    change u.1 • signedDiagonalCubic + u.2 • (signedEqualCubic-signedDiagonalCubic) = _
    module
  simp only [split, SymmetricCubic.apply_add, SymmetricCubic.apply_smul,
    chargeAction_preserves_full, chargeAction_preserves_diagonal]

end
end ThirteenPlanes
