module

public import ThirteenPlanes.Fields.FieldForm
public import ThirteenPlanes.Peirce.SlotComplexModel
public import ThirteenPlanes.Shares.PlaneTransport
public import ThirteenPlanes.FourPlanesEnergy
public import ThirteenPlanes.PilotContractions

@[expose] public section

set_option backward.privateInPublic true

/-! The explicit four-field Cartan polynomial and its Hermitian matrix coordinates. -/

namespace ThirteenPlanes.FourField

open Fields Peirce TracelessHermitian3 AlbertSequential
open scoped BigOperators RealInnerProductSpace Matrix

noncomputable section

abbrev Space := FieldSpace 4

/-- The four-field polynomial of the manuscript. -/
def polynomial (z : Space) : ℝ :=
  Complex.re ((z 0)^3 + (z 1)^3 + (z 2)^3 + (z 3)^3 - 3 * z 1 * z 2 * z 3 -
    3 * z 0 * (star (z 1) * z 2 + star (z 2) * z 3 + star (z 3) * z 1))

private def u₀ (z : Space) : ℂ := z 1 + z 2 + z 3
private def u₁ (z : Space) : ℂ := z 1 + qutritRoot * z 2 + star qutritRoot * z 3
private def u₂ (z : Space) : ℂ := z 1 + star qutritRoot * z 2 + qutritRoot * z 3

/-- The diagonal entries are twice the real Fourier coordinates of the first field.
The off-diagonal slots are the three Fourier coordinates of the other fields. -/
def matrix (z : Space) : ComplexMatrix3 :=
  complexSlotMatrix (2 * (z 0).re) (-(z 0).re + Real.sqrt 3 * (z 0).im)
    (-(z 0).re - Real.sqrt 3 * (z 0).im) (u₀ z) (star (u₁ z)) (u₂ z)

theorem matrix_isHermitian (z : Space) : (matrix z).IsHermitian :=
  complexSlotMatrix_isHermitian _ _ _ _ _ _

theorem matrix_trace (z : Space) : Matrix.trace (matrix z) = 0 := by
  rw [matrix, complexSlotMatrix_trace]
  push_cast
  ring

private theorem sqrtThree_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private theorem norm_sq_field (z : Space) : ‖z‖ ^ 2 = ∑ i : Fin 4, ‖z i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq z, PiLp.inner_apply]
  simp only [real_inner_self_eq_norm_sq]

/-- In these coordinates the trace norm is six times the squared field norm. -/
theorem matrix_norm (z : Space) : tracePairing (matrix z) (matrix z) = 6 * ‖z‖ ^ 2 := by
  rw [matrix, complexSlotMatrix_tracePairing, norm_sq_field, Fin.sum_univ_four]
  simp only [real_inner_self_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    u₀, u₁, u₂, qutritRoot, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring_nf
  simp only [sqrtThree_sq]
  ring

/-- The exact comparison with the matrix cubic at the coordinates printed in the paper. -/
theorem matrix_trace_cube (z : Space) : (Matrix.trace (matrix z ^ 3)).re = 6 * polynomial z := by
  rw [matrix, complexSlotMatrix_trace_cube]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.inner]
  simp only [polynomial, u₀, u₁, u₂, qutritRoot, pow_succ, pow_zero, one_mul, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
  ring_nf
  simp only [sqrtThree_sq]
  ring

private def matrixLinear : Space →ₗ[ℝ] TracelessHermitian3 where
  toFun z := ofMatrix (matrix z) (matrix_isHermitian z) (matrix_trace z)
  map_add' x y := by
    apply toMatrix_injective
    rw [map_add, toMatrix_ofMatrix, toMatrix_ofMatrix, toMatrix_ofMatrix]
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      simp [matrix, complexSlotMatrix, u₀, u₁, u₂, mul_add] <;> ring
  map_smul' t x := by
    apply toMatrix_injective
    rw [map_smul, toMatrix_ofMatrix, toMatrix_ofMatrix]
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      simp [matrix, complexSlotMatrix, u₀, u₁, u₂, Complex.real_smul, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub] <;> ring

private theorem matrixLinear_norm (z : Space) : ‖matrixLinear z‖ = Real.sqrt 6 * ‖z‖ := by
  have hm := norm_sq_eq_tracePairing (matrixLinear z)
  change ‖matrixLinear z‖ ^ 2 = tracePairing (matrix z) (matrix z) at hm
  rw [matrix_norm] at hm
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (6 : ℝ))]
  exact hm

/-- Dividing the displayed matrix by √6 gives an onto real isometry. -/
def matrixIsometry : Space ≃ₗᵢ[ℝ] TracelessHermitian3 :=
  let f : Space →ₗᵢ[ℝ] TracelessHermitian3 :=
    { toLinearMap := (Real.sqrt 6)⁻¹ • matrixLinear
      norm_map' := fun z => by
        simp only [LinearMap.smul_apply, norm_smul, Real.norm_of_nonneg
          (inv_nonneg.mpr (Real.sqrt_nonneg _)), matrixLinear_norm]
        rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr (by norm_num : 0 < (6 : ℝ))).ne', one_mul] }
  LinearIsometryEquiv.ofSurjective f ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) (by
      rw [Peirce.finrank_eq_twice_card (coordinatePlanes 4), fourPlane_dimension]
      norm_num)).mp f.injective)

theorem matrixIsometry_toMatrix (z : Space) :
    toMatrix (matrixIsometry z) = (Real.sqrt 6)⁻¹ • matrix z := by
  change toMatrix ((Real.sqrt 6)⁻¹ • matrixLinear z) = _
  rw [map_smul]
  rfl

/-- The normalized Cartan tensor in the manuscript's four complex coordinates. -/
def tensor : SymmetricCubic Space :=
  (Real.sqrt 6 • matrixEqualCubic).pullback matrixIsometry.toLinearMap

private theorem matrixIsometry_apply (z : Space) :
    matrixIsometry z = (Real.sqrt 6)⁻¹ • matrixLinear z := rfl

set_option maxHeartbeats 600000 in
theorem tensor_diagonal (z : Space) : tensor.apply z z z = polynomial z := by
  have hs : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hm : matrixEqualCubic.apply (matrixLinear z) (matrixLinear z) (matrixLinear z) =
      6 * polynomial z := by
    change ⟪jordan (matrixLinear z) (matrixLinear z), matrixLinear z⟫ = _
    rw [jordan_self, real_inner_comm, inner_square_eq_trace_cube]
    exact matrix_trace_cube z
  rw [tensor, SymmetricCubic.pullback_apply]
  change (Real.sqrt 6 • matrixEqualCubic).apply (matrixIsometry z) (matrixIsometry z) (matrixIsometry z) = _
  rw [matrixIsometry_apply, SymmetricCubic.apply_smul, SymmetricCubic.apply_smul₁,
    SymmetricCubic.apply_smul₂, SymmetricCubic.apply_smul₃, hm]
  field_simp [hs.ne']
  linear_combination -(polynomial z) * hs2

theorem tensor_isRound : IsRound tensor 1 := by
  apply RoundCubics.IsRound.pullback_isometry
  refine ⟨by norm_num, fun x => ?_⟩
  rw [SymmetricCubic.squareMap_smul, norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by norm_num), matrixEqualCubic_squareMap, TracelessHermitian3.square_norm_sq]
  ring

end
end ThirteenPlanes.FourField
