/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Matrix3

/-! The eight-field carrier as a subspace of the real Euclidean space of complex matrix entries. -/

@[expose] public section
noncomputable section

namespace ThirteenPlanes

open scoped Matrix
open WithLp

abbrev MatrixEntries3 := EuclideanSpace ℂ (Fin 3 × Fin 3)

def matrixEntries3 : MatrixEntries3 →ₗ[ℝ] ComplexMatrix3 where
  toFun x := fun i j => x (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem matrixEntries3_apply (x : MatrixEntries3) (i j : Fin 3) :
    matrixEntries3 x i j = x (i, j) := rfl

def tracelessHermitianSubspace : Submodule ℝ MatrixEntries3 where
  carrier := {x | (matrixEntries3 x).IsHermitian ∧ Matrix.trace (matrixEntries3 x) = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx, htx⟩ ⟨hy, hty⟩
    change (matrixEntries3 (x + y)).IsHermitian ∧ Matrix.trace (matrixEntries3 (x + y)) = 0
    rw [map_add, Matrix.trace_add, htx, hty, add_zero]
    exact ⟨hx.add hy, rfl⟩
  smul_mem' := by
    rintro r x ⟨hx, htx⟩
    change (matrixEntries3 (r • x)).IsHermitian ∧ Matrix.trace (matrixEntries3 (r • x)) = 0
    rw [map_smul, Matrix.trace_smul, htx, smul_zero]
    exact ⟨hx.smul (show IsSelfAdjoint r from star_trivial r), rfl⟩

abbrev TracelessHermitian3 := ↥tracelessHermitianSubspace

namespace TracelessHermitian3

def toMatrix : TracelessHermitian3 →ₗ[ℝ] ComplexMatrix3 :=
  matrixEntries3.comp tracelessHermitianSubspace.subtype

def ofMatrix (X : ComplexMatrix3) (hX : X.IsHermitian) (htr : Matrix.trace X = 0) :
    TracelessHermitian3 :=
  ⟨toLp 2 (fun ij : Fin 3 × Fin 3 => X ij.1 ij.2), ⟨hX, htr⟩⟩

theorem isHermitian (x : TracelessHermitian3) : (toMatrix x).IsHermitian := x.property.1

@[simp] theorem trace_eq_zero (x : TracelessHermitian3) : Matrix.trace (toMatrix x) = 0 :=
  x.property.2

@[simp] theorem toMatrix_ofMatrix (X : ComplexMatrix3) (hX htr) :
    toMatrix (ofMatrix X hX htr) = X := rfl

@[simp] theorem ofMatrix_toMatrix (x : TracelessHermitian3) :
    ofMatrix (toMatrix x) x.isHermitian x.trace_eq_zero = x := by
  apply Subtype.ext
  rfl

theorem toMatrix_injective : Function.Injective toMatrix := by
  intro x y hxy
  rw [← ofMatrix_toMatrix x, ← ofMatrix_toMatrix y]
  congr

@[ext] theorem ext {x y : TracelessHermitian3} (h : toMatrix x = toMatrix y) :
    x = y := toMatrix_injective h

theorem inner_eq_tracePairing (x y : TracelessHermitian3) :
    inner ℝ x y = tracePairing (toMatrix x) (toMatrix y) := by
  have hx (ij : Fin 3 × Fin 3) :
      (star (toMatrix x ij.1 ij.2)) = toMatrix x ij.2 ij.1 :=
    congrFun (congrFun x.isHermitian.eq ij.2) ij.1
  change inner ℝ x.val y.val = _
  rw [PiLp.inner_apply]
  change (∑ ij : Fin 3 × Fin 3,
    Complex.reAddGroupHom (toMatrix y ij.1 ij.2 * star (toMatrix x ij.1 ij.2))) =
    Complex.reAddGroupHom (∑ i, ∑ j, toMatrix x i j * toMatrix y j i)
  rw [← map_sum, Fintype.sum_prod_type]
  apply congrArg Complex.re
  calc
    _ = ∑ i, ∑ j, toMatrix y i j * toMatrix x j i := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (toMatrix y i j * ·) (hx (i, j))
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _

theorem norm_sq_eq_tracePairing (x : TracelessHermitian3) :
    ‖x‖ ^ 2 = tracePairing (toMatrix x) (toMatrix x) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_tracePairing]

def square (x : TracelessHermitian3) : TracelessHermitian3 :=
  ofMatrix (tracelessSquare (toMatrix x)) (tracelessSquare_hermitian x.isHermitian)
    (trace_traceFreePart _)

@[simp] theorem toMatrix_square (x : TracelessHermitian3) :
    toMatrix (square x) = tracelessSquare (toMatrix x) := rfl

theorem square_norm_sq (x : TracelessHermitian3) : ‖square x‖ ^ 2 = ‖x‖ ^ 4 / 6 := by
  rw [norm_sq_eq_tracePairing, toMatrix_square, tracelessSquare_tracePairing _
    x.isHermitian x.trace_eq_zero, ← norm_sq_eq_tracePairing]
  ring

end TracelessHermitian3

end ThirteenPlanes
