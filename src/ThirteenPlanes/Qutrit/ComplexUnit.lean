module

public import ThirteenPlanes.Shares.ComplexTraceFrames

@[expose] public section

set_option backward.privateInPublic true

/-! Scalar and traceless coordinates of the full complex matrix Jordan product. -/

open scoped RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

open AlbertSequential

noncomputable section

private theorem matrix_real_smul (r : ℝ) (A : ComplexMatrix3) :
    r • A = (r : ℂ) • A := by
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- The traceless and scalar coordinates are equivalent to literal Hermitian matrices. -/
def complexQutritJoin : (TracelessHermitian3 × ℝ) ≃ₗ[ℝ] Hermitian3 where
  toFun u := ⟨TracelessHermitian3.toMatrix u.1 + u.2 • (1 : ComplexMatrix3),
    u.1.isHermitian.add (Matrix.isHermitian_one.smul (show IsSelfAdjoint u.2 from star_trivial _))⟩
  invFun A := (TracelessHermitian3.ofMatrix (traceFreePart A.val)
    (traceFreePart_hermitian A.property) (trace_traceFreePart _), (Matrix.trace A.val).re / 3)
  left_inv u := by
    have ht : Matrix.trace (TracelessHermitian3.toMatrix u.1 + u.2 • (1 : ComplexMatrix3)) =
        3 * (u.2 : ℂ) := by
      rw [Matrix.trace_add, u.1.trace_eq_zero, matrix_real_smul, Matrix.trace_smul,
        trace_one_matrix3, zero_add, smul_eq_mul, mul_comm]
    apply Prod.ext
    · apply TracelessHermitian3.toMatrix_injective
      rw [TracelessHermitian3.toMatrix_ofMatrix, traceFreePart, ht]
      change TracelessHermitian3.toMatrix u.1 + u.2 • (1 : ComplexMatrix3) -
        ((3 * (u.2 : ℂ)) / 3) • (1 : ComplexMatrix3) = _
      rw [matrix_real_smul, show 3 * (u.2 : ℂ) / 3 = u.2 by ring, add_sub_cancel_right]
    · change (Matrix.trace (TracelessHermitian3.toMatrix u.1 + u.2 • (1 : ComplexMatrix3))).re / 3 = u.2
      rw [ht]
      simp [Complex.mul_re]
  right_inv A := by
    apply Subtype.ext
    change TracelessHermitian3.toMatrix (TracelessHermitian3.ofMatrix (traceFreePart A.val)
      (traceFreePart_hermitian A.property) (trace_traceFreePart _)) +
      ((Matrix.trace A.val).re / 3 : ℝ) • (1 : ComplexMatrix3) = A.val
    rw [TracelessHermitian3.toMatrix_ofMatrix, traceFreePart, matrix_real_smul,
      Complex.ofReal_div, ← hermitian_trace_eq_real (show A.val.IsHermitian from A.property)]
    norm_num
  map_add' u v := by
    apply Subtype.ext
    change TracelessHermitian3.toMatrix (u.1 + v.1) + (u.2 + v.2) • (1 : ComplexMatrix3) =
      (TracelessHermitian3.toMatrix u.1 + u.2 • (1 : ComplexMatrix3)) +
        (TracelessHermitian3.toMatrix v.1 + v.2 • (1 : ComplexMatrix3))
    rw [map_add, add_smul]
    abel
  map_smul' r u := by
    apply Subtype.ext
    change TracelessHermitian3.toMatrix (r • u.1) + (r * u.2) • (1 : ComplexMatrix3) =
      r • (TracelessHermitian3.toMatrix u.1 + u.2 • (1 : ComplexMatrix3))
    rw [map_smul, smul_add, smul_smul]

@[simp] theorem complexQutritJoin_coe (x : TracelessHermitian3) (r : ℝ) :
    (complexQutritJoin (x, r)).val = TracelessHermitian3.toMatrix x + r • (1 : ComplexMatrix3) :=
  rfl

theorem complexQutritJoin_trace (x : TracelessHermitian3) (r : ℝ) :
    (Matrix.trace (complexQutritJoin (x, r)).val).re = 3 * r := by
  rw [complexQutritJoin_coe, Matrix.trace_add, x.trace_eq_zero, matrix_real_smul,
    Matrix.trace_smul, trace_one_matrix3, zero_add, smul_eq_mul]
  norm_num [Complex.mul_re]
  ring

private theorem centered_product_trace (x y : TracelessHermitian3) :
    Matrix.trace (symmetricMatrixProduct (TracelessHermitian3.toMatrix x)
      (TracelessHermitian3.toMatrix y)) = (⟪x, y⟫ : ℝ) := by
  let A := TracelessHermitian3.toMatrix x
  let B := TracelessHermitian3.toMatrix y
  rw [hermitian_trace_eq_real (symmetricMatrixProduct_hermitian x.isHermitian y.isHermitian),
    TracelessHermitian3.inner_eq_tracePairing]
  exact congrArg Complex.ofReal (RoundCubics.tracePairing_eq_re_trace_jordan A B).symm

theorem complexQutritJoin_product (x y : TracelessHermitian3) (r s : ℝ) :
    (complexQutritJoin (TracelessHermitian3.jordan x y + r • y + s • x,
      ⟪x, y⟫ / 3 + r * s)).val =
    symmetricMatrixProduct (complexQutritJoin (x, r)).val (complexQutritJoin (y, s)).val := by
  rw [complexQutritJoin_coe, complexQutritJoin_coe, complexQutritJoin_coe]
  simp only [map_add, map_smul, TracelessHermitian3.toMatrix_jordan, traceFreePart,
    centered_product_trace, matrix_real_smul, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_mul]
  generalize TracelessHermitian3.toMatrix x = A
  generalize TracelessHermitian3.toMatrix y = B
  generalize (⟪x, y⟫ : ℝ) = u
  simp only [symmetricMatrixProduct, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, smul_add, smul_smul, add_smul]
  module

end

end ThirteenPlanes.JordanFrames
