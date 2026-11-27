/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Matrix3Metric
import Mathlib.LinearAlgebra.BilinearMap

/-! The centered Jordan product on the trace-free Hermitian matrix carrier. -/

@[expose] public section
noncomputable section

namespace ThirteenPlanes

open scoped Matrix

theorem traceFreePart_add (X Y : ComplexMatrix3) :
    traceFreePart (X + Y) = traceFreePart X + traceFreePart Y := by
  simp only [traceFreePart, Matrix.trace_add, add_div, add_smul]
  abel

theorem traceFreePart_smul (r : ℂ) (X : ComplexMatrix3) :
    traceFreePart (r • X) = r • traceFreePart X := by
  simp only [traceFreePart, Matrix.trace_smul, smul_eq_mul, mul_div_assoc, mul_smul, smul_sub]

theorem tracePairing_traceFreePart_left (X Y : ComplexMatrix3) (hY : Matrix.trace Y = 0) :
    tracePairing (traceFreePart X) Y = tracePairing X Y := by
  simp only [tracePairing, traceFreePart, sub_mul, Matrix.smul_mul, one_mul, Matrix.trace_sub,
    Matrix.trace_smul, hY, smul_zero, sub_zero]

def symmetricMatrixProduct (X Y : ComplexMatrix3) : ComplexMatrix3 :=
  (1 / 2 : ℂ) • (X * Y + Y * X)

theorem symmetricMatrixProduct_hermitian {X Y : ComplexMatrix3}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (symmetricMatrixProduct X Y).IsHermitian := by
  have h : (X * Y + Y * X).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hX.eq, hY.eq, add_comm]
  exact h.smul (by change star (1 / 2 : ℂ) = 1 / 2; simp)

theorem symmetricMatrixProduct_self (X : ComplexMatrix3) :
    symmetricMatrixProduct X X = X * X := by
  simp only [symmetricMatrixProduct, ← two_smul ℂ (X * X), smul_smul]
  norm_num

namespace TracelessHermitian3

def jordanValue (x y : TracelessHermitian3) : TracelessHermitian3 :=
  ofMatrix (traceFreePart (symmetricMatrixProduct (toMatrix x) (toMatrix y)))
    (traceFreePart_hermitian (symmetricMatrixProduct_hermitian x.isHermitian y.isHermitian))
    (trace_traceFreePart _)

theorem jordanValue_comm (x y : TracelessHermitian3) :
    jordanValue x y = jordanValue y x := by
  apply toMatrix_injective
  simp only [jordanValue, toMatrix_ofMatrix, symmetricMatrixProduct, add_comm]

theorem jordanValue_add (x y z : TracelessHermitian3) :
    jordanValue (x + y) z = jordanValue x z + jordanValue y z := by
  apply toMatrix_injective
  simp only [jordanValue, toMatrix_ofMatrix, map_add, symmetricMatrixProduct,
    add_mul, mul_add]
  rw [show toMatrix x * toMatrix z + toMatrix y * toMatrix z +
      (toMatrix z * toMatrix x + toMatrix z * toMatrix y) =
    (toMatrix x * toMatrix z + toMatrix z * toMatrix x) +
      (toMatrix y * toMatrix z + toMatrix z * toMatrix y) by abel, smul_add, traceFreePart_add]

theorem jordanValue_smul (r : ℝ) (x y : TracelessHermitian3) :
    jordanValue (r • x) y = r • jordanValue x y := by
  apply toMatrix_injective
  simp only [jordanValue, toMatrix_ofMatrix, map_smul]
  change traceFreePart (symmetricMatrixProduct ((r : ℂ) • toMatrix x) (toMatrix y)) =
    (r : ℂ) • traceFreePart (symmetricMatrixProduct (toMatrix x) (toMatrix y))
  rw [symmetricMatrixProduct, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
    smul_comm (1 / 2 : ℂ) (r : ℂ), traceFreePart_smul]
  rfl

def jordan : TracelessHermitian3 →ₗ[ℝ] TracelessHermitian3 →ₗ[ℝ] TracelessHermitian3 :=
  LinearMap.mk₂ ℝ jordanValue jordanValue_add jordanValue_smul
    (fun x y z => by rw [jordanValue_comm x, jordanValue_add, jordanValue_comm y, jordanValue_comm z])
    (fun r x y => by rw [jordanValue_comm x, jordanValue_smul, jordanValue_comm y])

@[simp] theorem toMatrix_jordan (x y : TracelessHermitian3) :
    toMatrix (jordan x y) = traceFreePart (symmetricMatrixProduct (toMatrix x) (toMatrix y)) := rfl

theorem jordan_comm (x y : TracelessHermitian3) : jordan x y = jordan y x :=
  jordanValue_comm x y

theorem jordan_self (x : TracelessHermitian3) : jordan x x = square x := by
  apply toMatrix_injective
  rw [toMatrix_jordan, symmetricMatrixProduct_self, toMatrix_square]
  rfl

theorem inner_jordan (x y z : TracelessHermitian3) :
    inner ℝ (jordan x y) z =
      ((Matrix.trace (toMatrix x * toMatrix y * toMatrix z)).re +
        (Matrix.trace (toMatrix y * toMatrix x * toMatrix z)).re) / 2 := by
  rw [inner_eq_tracePairing, toMatrix_jordan, tracePairing_traceFreePart_left _ _ z.trace_eq_zero]
  simp only [tracePairing, symmetricMatrixProduct, Matrix.smul_mul, add_mul,
    Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  norm_num [Complex.add_re, Complex.mul_re, Complex.div_re]
  ring

theorem inner_jordan_swap (x y z : TracelessHermitian3) :
    inner ℝ (jordan x y) z = inner ℝ (jordan x z) y := by
  rw [inner_jordan, inner_jordan, Matrix.trace_mul_cycle (toMatrix x) (toMatrix y) (toMatrix z),
    Matrix.trace_mul_cycle (toMatrix x) (toMatrix z) (toMatrix y)]
  ring

end TracelessHermitian3

end ThirteenPlanes
