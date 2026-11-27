module

public import ThirteenPlanes.FiniteGroup.Lifts

@[expose] public section

set_option backward.privateInPublic true

/-! The special linear group of the ternary charges is transitive on nonzero charges and on ordered
independent pairs. -/

open Matrix

namespace ThirteenPlanes

namespace FiniteGroup

/-- The determinant of the matrix with columns `x`, `y`, `w`. -/
def det3 (x y w : Charge) : ZMod 3 :=
  x 0 * (y 1 * w 2 - y 2 * w 1) - y 0 * (x 1 * w 2 - x 2 * w 1) + w 0 * (x 1 * y 2 - x 2 * y 1)

private theorem exists_det3_aux : ∀ x y : Charge, ¬ (x = 0 ∨ y = 0 ∨ x = y ∨ x = -y) →
    ∃ w, det3 x y w = 1 := by
  unfold det3
  decide

theorem exists_det3 (x y : Charge) (h : ¬ dependentGrades x y) : ∃ w, det3 x y w = 1 :=
  exists_det3_aux x y h

private theorem exists_independent_aux : ∀ x : Charge, x ≠ 0 →
    ∃ y, ¬ (x = 0 ∨ y = 0 ∨ x = y ∨ x = -y) := by
  decide

theorem exists_independent (x : Charge) (hx : x ≠ 0) : ∃ y, ¬ dependentGrades x y :=
  exists_independent_aux x hx

/-- The matrix with columns `x`, `y`, `w`. -/
def colMatrix (x y w : Charge) : ChargeMatrix := Matrix.of fun i j => ![x, y, w] j i

theorem det_colMatrix (x y w : Charge) : (colMatrix x y w).det = det3 x y w := by
  simp [colMatrix, Matrix.det_fin_three, det3]
  ring

theorem colMatrix_mulVec_zero (x y w : Charge) :
    colMatrix x y w *ᵥ (Pi.single 0 1 : Charge) = x := by
  funext i
  simp [colMatrix, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem colMatrix_mulVec_one (x y w : Charge) :
    colMatrix x y w *ᵥ (Pi.single 1 1 : Charge) = y := by
  funext i
  simp [colMatrix, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_sl_basis (x y : Charge) (h : ¬ dependentGrades x y) :
    ∃ A : SpecialLinearGroup (Fin 3) (ZMod 3),
      (A : ChargeMatrix) *ᵥ (Pi.single 0 1 : Charge) = x ∧
        (A : ChargeMatrix) *ᵥ (Pi.single 1 1 : Charge) = y := by
  obtain ⟨w, hw⟩ := exists_det3 x y h
  refine ⟨⟨colMatrix x y w, by rw [det_colMatrix, hw]⟩, ?_, ?_⟩
  · exact colMatrix_mulVec_zero x y w
  · exact colMatrix_mulVec_one x y w

/-- Transitivity on ordered independent pairs. -/
theorem sl_transitive_pairs {x y x' y' : Charge} (h : ¬ dependentGrades x y)
    (h' : ¬ dependentGrades x' y') :
    ∃ A : SpecialLinearGroup (Fin 3) (ZMod 3),
      (A : ChargeMatrix) *ᵥ x = x' ∧ (A : ChargeMatrix) *ᵥ y = y' := by
  obtain ⟨B, hB0, hB1⟩ := exists_sl_basis x y h
  obtain ⟨C, hC0, hC1⟩ := exists_sl_basis x' y' h'
  refine ⟨C * B⁻¹, ?_, ?_⟩
  · rw [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← hB0, mulVec_inv_mulVec, hC0]
  · rw [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← hB1, mulVec_inv_mulVec, hC1]

/-- Transitivity on nonzero charges. -/
theorem sl_transitive {x x' : Charge} (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ∃ A : SpecialLinearGroup (Fin 3) (ZMod 3), (A : ChargeMatrix) *ᵥ x = x' := by
  obtain ⟨y, hy⟩ := exists_independent x hx
  obtain ⟨y', hy'⟩ := exists_independent x' hx'
  obtain ⟨A, hA, -⟩ := sl_transitive_pairs hy hy'
  exact ⟨A, hA⟩

end FiniteGroup

end ThirteenPlanes
