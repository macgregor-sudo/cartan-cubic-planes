module

public import ThirteenPlanes.FourFieldModel

@[expose] public section

set_option backward.privateInPublic true

/-! The four coordinate planes are closed for the explicit four-field polynomial. -/

namespace ThirteenPlanes.FourField

open Fields
open scoped BigOperators

noncomputable section

private abbrev conjugateField := Complex.conjAe.toLinearEquiv.toLinearMap

private def interaction (f g : ℂ →ₗ[ℝ] ℂ) : RealTrilinear :=
  (-3 : ℝ) • LinearMap.mk₂ ℝ
    (fun x y => Complex.reCLM.toLinearMap.comp ((LinearMap.mul ℝ ℂ (x * f y)).comp g))
    (by intros; ext z; simp [add_mul])
    (by intros; ext z; simp; ring)
    (by intros; ext z; simp [map_add, mul_add, add_mul])
    (by
      intro c x y
      ext z
      change (x * f (c • y) * g z).re = c * (x * f y * g z).re
      rw [f.map_smul]
      simp
      ring)

private theorem interaction_apply (f g : ℂ →ₗ[ℝ] ℂ) (x y z : ℂ) :
    interaction f g x y z = (-3 : ℝ) * (x * f y * g z).re := rfl

private def coefficients (t : IncreasingTriple 4) : RealTrilinear :=
  if t.1.1 = 1 then interaction LinearMap.id LinearMap.id
  else if t.1.2.1 = 1 ∧ t.1.2.2 = 3 then interaction LinearMap.id conjugateField
  else interaction conjugateField LinearMap.id

private def t012 : IncreasingTriple 4 := ⟨(0, 1, 2), by decide⟩
private def t013 : IncreasingTriple 4 := ⟨(0, 1, 3), by decide⟩
private def t023 : IncreasingTriple 4 := ⟨(0, 2, 3), by decide⟩
private def t123 : IncreasingTriple 4 := ⟨(1, 2, 3), by decide⟩

theorem tensor_hasFieldForm : HasFieldForm tensor := by
  refine ⟨coefficients, fun z => ?_⟩
  rw [tensor_diagonal, Fields.polynomial, Fin.sum_univ_four]
  have all : (Finset.univ : Finset (IncreasingTriple 4)) = {t012, t013, t023, t123} := by decide
  rw [all]
  simp only [Finset.sum_insert (by decide : t012 ∉ ({t013, t023, t123} : Finset _)),
    Finset.sum_insert (by decide : t013 ∉ ({t023, t123} : Finset _)),
    Finset.sum_insert (by decide : t023 ∉ ({t123} : Finset _)), Finset.sum_singleton]
  norm_num [coefficients, t012, t013, t023, t123, interaction_apply, polynomial, conjugateField,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.star_def]
  ring

/-- The four coordinate two-planes form an exhaustive orthogonal closed system for W₄. -/
theorem coordinatePlanes_isClosed : IsClosedPlaneSystem tensor (coordinatePlanes 4) :=
  fieldForm_coordinatePlanes_closed tensor tensor_hasFieldForm

/-- The coordinate decomposition of the displayed polynomial transported to actual matrices. -/
def matrixCoordinatePlanes : PlaneDecomposition TracelessHermitian3 (Fin 4) :=
  RoundCubics.pullbackPlaneSystem (V := TracelessHermitian3) (W := Space) (coordinatePlanes 4) matrixIsometry.symm

theorem matrixCoordinatePlanes_isClosed : IsClosedPlaneSystem matrixEqualCubic matrixCoordinatePlanes := by
  intro i
  let U := ((coordinatePlanes 4).plane i).map matrixIsometry.toLinearMap
  have closed : IsClosedPiece (Real.sqrt 6 • matrixEqualCubic) U :=
    RoundCubics.isClosedPiece_map_isometry (V := Space) (W := TracelessHermitian3)
      (h := tensor) (k := Real.sqrt 6 • matrixEqualCubic) matrixIsometry rfl (coordinatePlanes_isClosed i)
  exact (RoundCubics.isClosedPiece_smul_iff (h := matrixEqualCubic)
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne' U).mp closed

end

end ThirteenPlanes.FourField
