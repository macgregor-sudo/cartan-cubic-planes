/- SPDX-License-Identifier: Apache-2.0 -/
module

public import PlaneComparator.ComplexModel
public import ThirteenPlanes.Fields.RadialClassification

@[expose] public section

set_option backward.privateInPublic true

/-! Literal coordinate and trace-pairing comparisons for the Albert model. -/

open scoped BigOperators InnerProductSpace

namespace Challenge.Bridge

open ThirteenPlanes

noncomputable section

private def albertCoordinates : Glennie.Albert ≃ₗ[ℝ] Hermitian3 where
  toFun x := (![x.d0, x.d1, x.d2], ![x.o01, x.o02, x.o12])
  invFun x := ⟨x.1 0, x.1 1, x.1 2, x.2 0, x.2 1, x.2 2⟩
  left_inv x := by cases x; rfl
  right_inv x := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_add' x y := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_smul' r x := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

private theorem albertCoordinates_trace (x : Glennie.Albert) :
    jordanTrace (albertCoordinates x) = Glennie.trace x := by
  simp [jordanTrace, Fin.sum_univ_three, albertCoordinates, Glennie.trace]

private theorem albertCoordinates_product (x y : Glennie.Albert) :
    jordanMul (albertCoordinates x) (albertCoordinates y) =
      albertCoordinates (Glennie.jordan x y) := by
  have hM (z : Glennie.Albert) : hermitianMatrix (albertCoordinates z) = Glennie.toMatrix z := rfl
  have hmul (A B : Matrix (Fin 3) (Fin 3) Octonion) :
      octMatrixMul A B = Glennie.matrixMul A B := rfl
  unfold jordanMul
  simp only [hM, hmul]
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · rfl

private def toAlbertModel : NativeTraceless →ₗ[ℝ] TracelessHermitian3 where
  toFun x := ⟨albertCoordinates x.val, by
    change jordanTrace (albertCoordinates x.val) = 0
    rw [albertCoordinates_trace, nativeTraceless_trace]⟩
  map_add' x y := Subtype.ext (map_add albertCoordinates x.val y.val)
  map_smul' r x := Subtype.ext (map_smul albertCoordinates r x.val)

def albertModel : NativeTraceless ≃ₗ[ℝ] TracelessHermitian3 :=
  LinearEquiv.ofBijective toAlbertModel ⟨fun x y eq =>
    Subtype.ext (albertCoordinates.injective (congrArg Subtype.val eq)), fun x => by
    let y := albertCoordinates.symm x.val
    have hy : Glennie.trace y = 0 := by
      rw [← albertCoordinates_trace, LinearEquiv.apply_symm_apply]
      exact x.property
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    exact albertCoordinates.apply_symm_apply x.val⟩

theorem albertModel_tracePairing (x y : NativeTraceless) :
    jordanTrace (jordanMul (albertModel x).val (albertModel y).val) = ⟪x, y⟫_ℝ := by
  change jordanTrace (jordanMul (albertCoordinates x.val) (albertCoordinates y.val)) =
    Glennie.inner x.val y.val
  rw [albertCoordinates_product, albertCoordinates_trace]
  rfl

theorem albertModel_traceCube (x : NativeTraceless) :
    jordanTrace (jordanMul (jordanMul (albertModel x).val (albertModel x).val) (albertModel x).val) =
      Glennie.trace (Glennie.jordan (Glennie.jordan x.val x.val) x.val) := by
  change jordanTrace (jordanMul (jordanMul (albertCoordinates x.val) (albertCoordinates x.val))
    (albertCoordinates x.val)) = _
  rw [albertCoordinates_product, albertCoordinates_product, albertCoordinates_trace]

/-- The two field-model conclusions use the same real gradient and coefficient polynomial. -/
theorem field_classification {m : ℕ} (hm : 1 ≤ m)
    (T : IncreasingTriple m → RealTrilinear) (hr : RadialFieldEnergy T) :
    m = 1 ∨ (m = 4 ∧ ∃ I : FieldSpace m ≃ₗ[ℝ] TracelessComplexHermitian3,
      (∀ x y, ⟪x, y⟫_ℝ = (Matrix.trace (complexMatrix (I x) * complexMatrix (I y))).re) ∧
      ∀ x, fieldPolynomial T x = Real.sqrt 6 * (Matrix.trace (complexMatrix (I x) ^ 3)).re) ∨
    (m = 13 ∧ ∃ I : FieldSpace m ≃ₗ[ℝ] TracelessHermitian3,
      (∀ x y, ⟪x, y⟫_ℝ = jordanTrace (jordanMul (I x).val (I y).val)) ∧
      ∀ x, fieldPolynomial T x = Real.sqrt 6 *
        jordanTrace (jordanMul (jordanMul (I x).val (I x).val) (I x).val)) := by
  rcases Fields.field_polynomial_count_and_model hm T hr with hh | ⟨hn, J, hJ⟩ | ⟨hn, J, hJ⟩
  · exact Or.inl hh
  · refine Or.inr (Or.inl ⟨hn, J.toLinearEquiv.trans complexModel, ?_, ?_⟩)
    · intro x y
      change ⟪x, y⟫_ℝ = (Matrix.trace
        (complexMatrix (complexModel (J x)) * complexMatrix (complexModel (J y)))).re
      rw [complexModel_tracePairing]
      have hm := norm_add_sq_real (J x) (J y)
      rw [← J.map_add, J.norm_map, J.norm_map, J.norm_map] at hm
      nlinarith only [hm, norm_add_sq_real x y]
    · exact hJ
  · refine Or.inr (Or.inr ⟨hn, J.toLinearEquiv.trans albertModel, ?_, ?_⟩)
    · intro x y
      change ⟪x, y⟫_ℝ = jordanTrace (jordanMul (albertModel (J x)).val (albertModel (J y)).val)
      rw [albertModel_tracePairing]
      have hm := norm_add_sq_real (J x) (J y)
      rw [← J.map_add, J.norm_map, J.norm_map, J.norm_map] at hm
      nlinarith only [hm, norm_add_sq_real x y]
    · intro x
      change Fields.polynomial T x = Real.sqrt 6 *
        jordanTrace (jordanMul (jordanMul (albertModel (J x)).val (albertModel (J x)).val)
          (albertModel (J x)).val)
      rw [albertModel_traceCube]
      exact hJ x

theorem field_witnesses :
    (∃ T : IncreasingTriple 4 → RealTrilinear, RadialFieldEnergy T) ∧
    (∃ T : IncreasingTriple 13 → RealTrilinear, RadialFieldEnergy T) :=
  Fields.four_and_thirteen_radial_field_polynomials

end

end Challenge.Bridge
