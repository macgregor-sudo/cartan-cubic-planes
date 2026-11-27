/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! The real trace metric and the traceless square on complex three-by-three matrices. -/

@[expose] public section
noncomputable section

namespace ThirteenPlanes

open scoped Matrix

abbrev ComplexMatrix3 := Matrix (Fin 3) (Fin 3) ℂ

def tracePairing (X Y : ComplexMatrix3) : ℝ := (Matrix.trace (X * Y)).re

def traceFreePart (X : ComplexMatrix3) : ComplexMatrix3 :=
  X - (Matrix.trace X / 3) • 1

def tracelessSquare (X : ComplexMatrix3) : ComplexMatrix3 :=
  traceFreePart (X * X)

@[simp] theorem trace_one_matrix3 : Matrix.trace (1 : ComplexMatrix3) = 3 := by
  simp [Matrix.trace_one]

@[simp] theorem trace_traceFreePart (X : ComplexMatrix3) :
    Matrix.trace (traceFreePart X) = 0 := by
  rw [traceFreePart, Matrix.trace_sub, Matrix.trace_smul, trace_one_matrix3, smul_eq_mul]
  ring

theorem hermitian_trace_conj {X : ComplexMatrix3} (hX : X.IsHermitian) :
    star (Matrix.trace X) = Matrix.trace X := by
  rw [← Matrix.trace_conjTranspose, hX.eq]

theorem hermitian_trace_eq_real {X : ComplexMatrix3} (hX : X.IsHermitian) :
    Matrix.trace X = ((Matrix.trace X).re : ℂ) := by
  have h := congrArg Complex.im (hermitian_trace_conj hX)
  have him : (Matrix.trace X).im = 0 := by
    change -(Matrix.trace X).im = (Matrix.trace X).im at h
    linarith
  exact Complex.ext rfl (by simpa using him)

theorem traceFreePart_hermitian {X : ComplexMatrix3} (hX : X.IsHermitian) :
    (traceFreePart X).IsHermitian := by
  change (X - (Matrix.trace X / 3) • (1 : ComplexMatrix3))ᴴ =
    X - (Matrix.trace X / 3) • 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hX.eq]
  rw [hermitian_trace_eq_real hX]
  simp

theorem tracelessSquare_hermitian {X : ComplexMatrix3} (hX : X.IsHermitian) :
    (tracelessSquare X).IsHermitian :=
  traceFreePart_hermitian (by rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hX.eq])

/-- The fourth trace power of a traceless three-by-three matrix. -/
theorem trace_fourth_power (X : ComplexMatrix3) (hX : Matrix.trace X = 0) :
    Matrix.trace (X ^ 4) = (Matrix.trace (X ^ 2)) ^ 2 / 2 := by
  have hdiag : X 2 2 = -(X 0 0 + X 1 1) := by
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three] at hX
    linear_combination hX
  simp only [pow_succ, pow_zero, one_mul, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Fin.sum_univ_three, hdiag]
  ring

private theorem trace_square_traceFreePart (Y : ComplexMatrix3) :
    Matrix.trace (traceFreePart Y * traceFreePart Y) =
      Matrix.trace (Y * Y) - (Matrix.trace Y) ^ 2 / 3 := by
  simp only [traceFreePart, sub_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul, mul_one,
    one_mul, Matrix.trace_sub, Matrix.trace_smul, trace_one_matrix3, smul_eq_mul]
  ring

/-- The Jordan member's energy identity for every traceless Hermitian matrix. -/
theorem tracelessSquare_tracePairing (X : ComplexMatrix3) (hX : X.IsHermitian)
    (htr : Matrix.trace X = 0) :
    tracePairing (tracelessSquare X) (tracelessSquare X) = (tracePairing X X) ^ 2 / 6 := by
  have hsq : (X * X).IsHermitian := by rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hX.eq]
  have hquartic := trace_fourth_power X htr
  rw [show (4 : ℕ) = 2 + 2 by decide, pow_add, pow_two] at hquartic
  have hquartic' : Matrix.trace (X * X * (X * X)) = (Matrix.trace (X * X)) ^ 2 / 2 := by
    simpa only [pow_two X] using hquartic
  rw [tracePairing, tracePairing, tracelessSquare, trace_square_traceFreePart,
    hquartic', hermitian_trace_eq_real hsq]
  norm_num [pow_two, Complex.div_re, Complex.mul_re]
  ring

end ThirteenPlanes
