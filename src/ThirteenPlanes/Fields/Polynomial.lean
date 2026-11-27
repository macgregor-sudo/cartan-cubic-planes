module

public import ThirteenPlanes.Fields.FieldForm
public import ThirteenPlanes.Peirce.SlotTransport

@[expose] public section

set_option backward.privateInPublic true

/-! Polarization of the field polynomial for an arbitrary family of coefficients. -/

open scoped BigOperators InnerProductSpace

namespace ThirteenPlanes.Fields

noncomputable section

private def coordinate {m : ℕ} (i : Fin m) : FieldSpace m →ₗ[ℝ] ℂ :=
  (LinearMap.proj i).comp (WithLp.linearEquiv 2 ℝ (Fin m → ℂ)).toLinearMap

@[simp] private theorem coordinate_apply {m : ℕ} (i : Fin m) (z : FieldSpace m) :
    coordinate i z = z i := rfl

private def evalTrilinear {m : ℕ} (T : RealTrilinear) (i j k : Fin m) :
    FieldSpace m →ₗ[ℝ] FieldSpace m →ₗ[ℝ] FieldSpace m →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (T (coordinate i x) (coordinate j y)).comp (coordinate k))
    (by intros; ext z; simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply])
    (by intros; ext z; simp only [map_smul, LinearMap.smul_apply, LinearMap.comp_apply])
    (by intros; ext z; simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply])
    (by intros; ext z; simp only [map_smul, LinearMap.smul_apply, LinearMap.comp_apply])

@[simp] private theorem evalTrilinear_apply {m : ℕ} (T : RealTrilinear) (i j k : Fin m)
    (x y z : FieldSpace m) : evalTrilinear T i j k x y z = T (x i) (y j) (z k) := rfl

private def oneField : RealTrilinear :=
  LinearMap.mk₂ ℝ
    (fun a b => Complex.reCLM.toLinearMap.comp (LinearMap.mul ℝ ℂ (a * b)))
    (by intros; ext z; simp [add_mul])
    (by intros; ext z; simp; ring)
    (by intros; ext z; simp [mul_add, add_mul])
    (by intros; ext z; simp; ring)

@[simp] private theorem oneField_apply (x y z : ℂ) : oneField x y z = (x * y * z).re := rfl

private def interactionValue {m : ℕ} (T : RealTrilinear) (i j k : Fin m)
    (x y z : FieldSpace m) : ℝ :=
  T (coordinate i x) (coordinate j y) (coordinate k z) +
    T (coordinate i x) (coordinate j z) (coordinate k y) +
    T (coordinate i y) (coordinate j x) (coordinate k z) +
    T (coordinate i y) (coordinate j z) (coordinate k x) +
    T (coordinate i z) (coordinate j x) (coordinate k y) +
    T (coordinate i z) (coordinate j y) (coordinate k x)

private def interactionLinear {m : ℕ} (T : RealTrilinear) (i j k : Fin m)
    (x y : FieldSpace m) : FieldSpace m →ₗ[ℝ] ℝ where
  toFun := interactionValue T i j k x y
  map_add' := by intros; simp only [interactionValue, map_add, LinearMap.add_apply]; ring
  map_smul' := by intros; simp only [interactionValue, map_smul, LinearMap.smul_apply,
    RingHom.id_apply, smul_eq_mul]; ring

private def interactionPolarization {m : ℕ} (T : RealTrilinear) (i j k : Fin m) :
    FieldSpace m →ₗ[ℝ] FieldSpace m →ₗ[ℝ] FieldSpace m →ₗ[ℝ] ℝ :=
  (1 / 6 : ℝ) • LinearMap.mk₂ ℝ (interactionLinear T i j k)
    (by intros; ext z; simp only [LinearMap.add_apply, interactionLinear, LinearMap.coe_mk,
      AddHom.coe_mk, interactionValue, map_add]; ring)
    (by intros; ext z; simp only [LinearMap.smul_apply, interactionLinear, LinearMap.coe_mk,
      AddHom.coe_mk, interactionValue, map_smul, smul_eq_mul]; ring)
    (by intros; ext z; simp only [LinearMap.add_apply, interactionLinear, LinearMap.coe_mk,
      AddHom.coe_mk, interactionValue, map_add]; ring)
    (by intros; ext z; simp only [LinearMap.smul_apply, interactionLinear, LinearMap.coe_mk,
      AddHom.coe_mk, interactionValue, map_smul, smul_eq_mul]; ring)

private theorem interactionPolarization_apply {m : ℕ} (T : RealTrilinear) (i j k : Fin m)
    (x y z : FieldSpace m) : interactionPolarization T i j k x y z =
      (T (x i) (y j) (z k) + T (x i) (z j) (y k) + T (y i) (x j) (z k) +
        T (y i) (z j) (x k) + T (z i) (x j) (y k) + T (z i) (y j) (x k)) / 6 := by
  simp only [interactionPolarization, LinearMap.smul_apply, LinearMap.mk₂_apply, LinearMap.coe_mk,
    interactionLinear, AddHom.coe_mk, smul_eq_mul, interactionValue, coordinate_apply]
  ring

private def fieldPolarization {m : ℕ} (T : IncreasingTriple m → RealTrilinear) :
    FieldSpace m →ₗ[ℝ] FieldSpace m →ₗ[ℝ] FieldSpace m →ₗ[ℝ] ℝ :=
  (∑ i, evalTrilinear oneField i i i) +
    ∑ t, interactionPolarization (T t) t.1.1 t.1.2.1 t.1.2.2

/-- The symmetric cubic of the stated polynomial exists for every real trilinear coefficient family. -/
def coefficientCubic {m : ℕ} (T : IncreasingTriple m → RealTrilinear) :
    SymmetricCubic (FieldSpace m) :=
  SymmetricCubic.ofPolarization (fieldPolarization T)
    (by
      intro x y z
      simp only [fieldPolarization, LinearMap.add_apply, LinearMap.sum_apply,
        evalTrilinear_apply, oneField_apply, mul_comm (x _) (y _), interactionPolarization_apply]
      congr 1
      apply Finset.sum_congr rfl
      intros
      ring)
    (by
      intro x y z
      simp only [fieldPolarization, LinearMap.add_apply, LinearMap.sum_apply,
        evalTrilinear_apply, oneField_apply, interactionPolarization_apply]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [mul_right_comm]
      · apply Finset.sum_congr rfl
        intros
        ring)

@[simp] theorem coefficientCubic_diagonal {m : ℕ} (T : IncreasingTriple m → RealTrilinear)
    (z : FieldSpace m) : (coefficientCubic T).apply z z z = polynomial T z := by
  simp only [coefficientCubic, SymmetricCubic.apply_ofPolarization, fieldPolarization, polynomial,
    LinearMap.add_apply, LinearMap.sum_apply, evalTrilinear_apply, oneField_apply,
    interactionPolarization_apply]
  congr 1
  · exact Finset.sum_congr rfl (fun _ _ => by rw [pow_succ, pow_two])
  · exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- The trilinear routes to the manuscript polynomial give the same symmetric cubic. -/
theorem coefficientCubic_unique {m : ℕ} (T : IncreasingTriple m → RealTrilinear)
    (h : SymmetricCubic (FieldSpace m)) (hh : ∀ z, h.apply z z z = polynomial T z) :
    h = coefficientCubic T :=
  Peirce.cubic_eq_of_diagonal_eq fun z => (hh z).trans (coefficientCubic_diagonal T z).symm

/-- Lemma 6-fields, quantified directly over the manuscript's coefficients. -/
theorem radial_polynomial_isRound {m : ℕ} (hm : 1 ≤ m) (T : IncreasingTriple m → RealTrilinear)
    (radial : ∀ x y : FieldSpace m, ‖x‖ = ‖y‖ →
      ‖gradient (polynomial T) x‖ = ‖gradient (polynomial T) y‖) :
    IsRound (coefficientCubic T) 1 ∧ (coefficientCubic T).TraceFree ∧
      IsClosedPlaneSystem (coefficientCubic T) (coordinatePlanes m) :=
  fieldForm_round_of_radial_gradient hm _ ⟨T, coefficientCubic_diagonal T⟩
    (by simpa only [coefficientCubic_diagonal] using radial)

end

end ThirteenPlanes.Fields
