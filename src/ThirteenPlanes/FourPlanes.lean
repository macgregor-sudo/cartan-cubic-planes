/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.FourPlanesGeometry
public import ThirteenPlanes.Contracts

@[expose] public section

set_option backward.privateInPublic true

/-! The diagonal and mixed cubics of the four-plane matrix model. -/

noncomputable section

namespace ThirteenPlanes

open TracelessHermitian3

def matrixEqualCubic : SymmetricCubic TracelessHermitian3 :=
  SymmetricCubic.ofProduct jordan jordan_comm inner_jordan_swap

@[simp] theorem matrixEqualCubic_squareMap (x : TracelessHermitian3) :
    matrixEqualCubic.squareMap x = square x := jordan_self x

def matrixDiagonalCubic : SymmetricCubic TracelessHermitian3 :=
  ∑ k : Fin 4, matrixEqualCubic.pullback (matrixFrameProjection k)

/-- The cubic pair on the actual traceless Hermitian three-by-three matrices. -/
def fourPlanePair : CubicPair TracelessHermitian3 where
  diagonalCubic := matrixDiagonalCubic
  mixingCubic := matrixEqualCubic - matrixDiagonalCubic

private theorem coupling_difference {W : Type*} [AddCommGroup W] [Module ℝ W]
    (D d : W) (a b : ℝ) : a • D + b • (d - D) = (a - b) • D + b • d := by
  rw [sub_smul, smul_sub]
  abel

theorem coupling_fourPlanePair (a b : ℝ) :
    coupling fourPlanePair (a, b) = (a - b) • matrixDiagonalCubic + b • matrixEqualCubic :=
  coupling_difference matrixDiagonalCubic matrixEqualCubic a b

@[simp] theorem interactionCubic_fourPlanePair_one :
    interactionCubic fourPlanePair 1 = matrixEqualCubic := by
  rw [interactionCubic, coupling_fourPlanePair, sub_self, zero_smul, zero_add, one_smul]

theorem fourPlane_squareLaw : HasSquareLaw (interactionCubic fourPlanePair 1) := by
  intro x
  rw [interactionCubic_fourPlanePair_one, matrixEqualCubic_squareMap]
  exact square_norm_sq x

theorem matrixDiagonalCubic_squareMap (x : TracelessHermitian3) :
    matrixDiagonalCubic.squareMap x = ∑ k : Fin 4, square (matrixFrameProjection k x) := by
  apply ext_inner_right ℝ
  intro z
  change matrixDiagonalCubic.apply x x z = _
  rw [matrixDiagonalCubic]
  change inner ℝ ((SymmetricCubic.L (∑ k : Fin 4, matrixEqualCubic.pullback
    (matrixFrameProjection k))) x x) z = _
  simp only [map_sum, LinearMap.sum_apply, sum_inner]
  apply Finset.sum_congr rfl
  intro k _
  change (matrixEqualCubic.pullback (matrixFrameProjection k)).apply x x z = _
  rw [SymmetricCubic.pullback_apply]
  change inner ℝ (matrixEqualCubic.squareMap (matrixFrameProjection k x))
    (matrixFrameProjection k z) = _
  rw [matrixEqualCubic_squareMap, ← matrixFrameProjection_inner_swap]
  have h : matrixFrameProjection k (matrixFrameProjection k x) = matrixFrameProjection k x := by
    rw [matrixFrameProjection_comp, ite_eq_left rfl]
  have hsq : matrixFrameProjection k (square (matrixFrameProjection k x)) =
      square (matrixFrameProjection k x) := by
    simp only [← jordan_self]
    exact project_jordan_of_fixed k _ _ h h
  rw [hsq]

theorem coupling_fourPlanePair_squareMap (a b : ℝ) (x : TracelessHermitian3) :
    (coupling fourPlanePair (a, b)).squareMap x =
      (a - b) • (∑ k : Fin 4, square (matrixFrameProjection k x)) + b • square x := by
  rw [coupling_fourPlanePair, SymmetricCubic.squareMap_add, SymmetricCubic.squareMap_smul,
    SymmetricCubic.squareMap_smul, matrixDiagonalCubic_squareMap, matrixEqualCubic_squareMap]

end ThirteenPlanes
