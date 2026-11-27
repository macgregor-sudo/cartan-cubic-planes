module

public import ThirteenPlanes.PlaneContractions.Traces

@[expose] public section

/-! The contraction identities of the equal-strength cubic `d` and of its diagonal part `D`
under the plane hypotheses and the square law. -/

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace ThirteenPlanes

noncomputable section

namespace PlaneContractions

open SymmetricCubic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] {planes : PlaneDecomposition V ι} {P : CubicPair V}
variable (hP : HasPlaneData P planes) (hsq : HasSquareLaw (interactionCubic P 1))
include hP hsq

theorem slice_mul (i : ι) (x y : V) :
    LinearMap.trace ℝ (planes.plane i)
        (slice planes (interactionCubic P 1) i x * slice planes (interactionCubic P 1) i y) =
      ⟪piP planes i x, piP planes i y⟫ / 3 := by
  have := trace_mul_of_squareLaw (restriction_squareLaw hP.repeatedPlane hsq i) (hP.traceFree i)
    (piP planes i x) (piP planes i y)
  rw [planes.dimension i] at this
  rw [slice, slice, this]
  ring

theorem slice_triple (i : ι) (x y z : V) :
    LinearMap.trace ℝ (planes.plane i)
        (slice planes (interactionCubic P 1) i x *
          (slice planes (interactionCubic P 1) i y * slice planes (interactionCubic P 1) i z)) =
      0 := by
  have := congrArg (fun h : SymmetricCubic (planes.plane i) =>
      h.apply (piP planes i x) (piP planes i y) (piP planes i z))
    (triangleContraction_of_squareLaw (restriction_squareLaw hP.repeatedPlane hsq i)
      (hP.traceFree i))
  simp only [apply_triangleContraction, apply_smul, planes.dimension i] at this
  rw [slice, slice, slice, ← mul_assoc, this]
  norm_num

omit hsq in
theorem compress_diag (i : ι) (z : V) :
    piP planes i ∘ₗ P.diagonalCubic.L z ∘ₗ (planes.plane i).subtype =
      slice planes (interactionCubic P 1) i z := by
  rw [← LinearMap.comp_assoc, piP_comp_L_diag hP.diagonal_eq, LinearMap.comp_assoc,
    piP_subtype, LinearMap.comp_id]

omit hsq in
theorem compress_mul_diag (i : ι) (y : V) (Y : Module.End ℝ V) :
    piP planes i ∘ₗ (P.diagonalCubic.L y * Y) ∘ₗ (planes.plane i).subtype =
      slice planes (interactionCubic P 1) i y * (piP planes i ∘ₗ Y ∘ₗ (planes.plane i).subtype) := by
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc,
    ← LinearMap.comp_assoc, piP_comp_L_diag hP.diagonal_eq]
  simp only [LinearMap.comp_assoc]

omit hsq in
/-- The diagonal cubic is trace-free. -/
theorem trace_L_diag (z : V) : LinearMap.trace ℝ V (P.diagonalCubic.L z) = 0 := by
  have := trace_diag_mul hP.diagonal_eq z 1
  rw [mul_one] at this
  rw [this]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Module.End.one_eq_id, LinearMap.id_comp, piP_subtype, ← Module.End.one_eq_id, mul_one]
  exact hP.traceFree i _

omit hsq in
/-- The equal-strength cubic is trace-free. -/
theorem traceFree_interaction : (interactionCubic P 1).TraceFree := by
  intro x
  have hsum : (interactionCubic P 1).L x = (∑ i, planes.proj i) * (interactionCubic P 1).L x := by
    rw [sum_proj]; rfl
  rw [hsum, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [proj_eq, Module.End.mul_eq_comp, LinearMap.comp_assoc, LinearMap.trace_comp_comm',
    LinearMap.comp_assoc, compress_slice hP.repeatedPlane]
  exact hP.traceFree i _

theorem trace_diag_mul_d (z w : V) :
    LinearMap.trace ℝ V (P.diagonalCubic.L z * (interactionCubic P 1).L w) = ⟪z, w⟫ / 3 := by
  rw [trace_diag_mul hP.diagonal_eq]
  simp only [compress_slice hP.repeatedPlane, slice_mul hP hsq]
  rw [← Finset.sum_div, sum_inner_piP]

theorem trace_diag_mul_diag (z w : V) :
    LinearMap.trace ℝ V (P.diagonalCubic.L z * P.diagonalCubic.L w) = ⟪z, w⟫ / 3 := by
  rw [trace_diag_mul hP.diagonal_eq]
  simp only [compress_diag hP, slice_mul hP hsq]
  rw [← Finset.sum_div, sum_inner_piP]

theorem trace_diag_diag_d (x y z : V) :
    LinearMap.trace ℝ V
      (P.diagonalCubic.L x * P.diagonalCubic.L y * (interactionCubic P 1).L z) = 0 := by
  rw [mul_assoc, trace_diag_mul hP.diagonal_eq]
  simp only [compress_mul_diag hP, compress_slice hP.repeatedPlane, slice_triple hP hsq,
    Finset.sum_const_zero]

theorem trace_diag_diag_diag (x y z : V) :
    LinearMap.trace ℝ V (P.diagonalCubic.L x * P.diagonalCubic.L y * P.diagonalCubic.L z) = 0 := by
  rw [mul_assoc, trace_diag_mul hP.diagonal_eq]
  simp only [compress_mul_diag hP, compress_diag hP, slice_triple hP hsq, Finset.sum_const_zero]

/-- One diagonal factor in the triangle: the polarized law gives `(D - d) / 6`. -/
theorem trace_diag_d_d (z x y : V) :
    LinearMap.trace ℝ V
      (P.diagonalCubic.L z * (interactionCubic P 1).L x * (interactionCubic P 1).L y) =
      (P.diagonalCubic.apply z x y - (interactionCubic P 1).apply z x y) / 6 := by
  have hT := triangle_identity hsq P.diagonalCubic x y z
  rw [trace_L_diag hP, zero_mul, add_zero, trace_diag_mul_d hP hsq] at hT
  have h1 : ⟪z, (interactionCubic P 1).L x y⟫ = (interactionCubic P 1).apply z x y := by
    rw [real_inner_comm]
    change (interactionCubic P 1).apply x y z = _
    rw [(interactionCubic P 1).apply_swap₂₃, (interactionCubic P 1).apply_swap₁₂]
  rw [h1] at hT
  linear_combination hT / 2

end PlaneContractions

end

end ThirteenPlanes
