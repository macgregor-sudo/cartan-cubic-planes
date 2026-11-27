/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.FourPlanesProjectors
public import ThirteenPlanes.Matrix3
import Mathlib.Tactic.NoncommRing

/-! The cubic trace of the marked three-plane sum used in plane-share energy formula (c). -/

@[expose] public section
noncomputable section

namespace ThirteenPlanes

open AlbertSequential
open scoped Matrix ComplexOrder

def markedProjectionSum : ComplexMatrix3 :=
  qutritMUBProjection 0 0 + qutritMUBProjection 1 0 + qutritMUBProjection 3 1

theorem markedProjectionSum_trace : Matrix.trace markedProjectionSum = 3 := by
  norm_num [markedProjectionSum, qutritMUBProjection_trace]

private theorem trace_mul_repeat_middle (X Y : ComplexMatrix3) (hX : X * X = X) :
    Matrix.trace (X * Y * X) = Matrix.trace (X * Y) := by
  rw [Matrix.trace_mul_cycle, hX]

private theorem trace_mul_repeat_right (X Y : ComplexMatrix3) (hX : X * X = X) :
    Matrix.trace (Y * X * X) = Matrix.trace (X * Y) := by
  rw [Matrix.mul_assoc, hX, Matrix.trace_mul_comm]

private theorem trace_sum_cube_idempotents (A B C : ComplexMatrix3)
    (hA : A * A = A) (hB : B * B = B) (hC : C * C = C) :
    Matrix.trace ((A + B + C) ^ 3) =
      Matrix.trace A + Matrix.trace B + Matrix.trace C +
      6 * (Matrix.trace (A * B) + Matrix.trace (A * C) + Matrix.trace (B * C)) +
      3 * (Matrix.trace (A * B * C) + Matrix.trace (A * C * B)) := by
  rw [show (A + B + C) ^ 3 =
      A*A*A + A*A*B + A*A*C + A*B*A + A*B*B + A*B*C + A*C*A + A*C*B + A*C*C +
      (B*A*A + B*A*B + B*A*C + B*B*A + B*B*B + B*B*C + B*C*A + B*C*B + B*C*C) +
      (C*A*A + C*A*B + C*A*C + C*B*A + C*B*B + C*B*C + C*C*A + C*C*B + C*C*C)
        by noncomm_ring]
  simp only [Matrix.trace_add, trace_mul_repeat_middle A B hA, trace_mul_repeat_middle A C hA,
    trace_mul_repeat_middle B A hB, trace_mul_repeat_middle B C hB,
    trace_mul_repeat_middle C A hC, trace_mul_repeat_middle C B hC,
    trace_mul_repeat_right A B hA, trace_mul_repeat_right A C hA,
    trace_mul_repeat_right B A hB, trace_mul_repeat_right B C hB,
    trace_mul_repeat_right C A hC, trace_mul_repeat_right C B hC,
    hA, hB, hC]
  rw [Matrix.trace_mul_cycle B A C, Matrix.trace_mul_cycle C B A,
    Matrix.trace_mul_cycle B C A, Matrix.trace_mul_cycle A B C,
    Matrix.trace_mul_comm B A, Matrix.trace_mul_comm C A, Matrix.trace_mul_comm C B]
  ring

theorem markedProjectionSum_trace_square : Matrix.trace (markedProjectionSum ^ 2) = 5 := by
  simp only [markedProjectionSum, pow_two, add_mul, mul_add, Matrix.trace_add,
    qutritMUBProjection_idempotent, qutritMUBProjection_trace, qutritProjection_pairTrace]
  norm_num

theorem markedProjection_reverseTrace :
    Matrix.trace (qutritMUBProjection 0 0 * qutritMUBProjection 3 1 *
      qutritMUBProjection 1 0) = star ((2 + qutritRoot) / 9) := by
  calc
    _ = Matrix.trace ((qutritMUBProjection 0 0 * qutritMUBProjection 1 0 *
        qutritMUBProjection 3 1)ᴴ) := by
      simp only [Matrix.conjTranspose_mul,
        (qutritMUBProjection_positive 0 0).isHermitian.eq,
        (qutritMUBProjection_positive 1 0).isHermitian.eq,
        (qutritMUBProjection_positive 3 1).isHermitian.eq, ← Matrix.mul_assoc]
      rw [Matrix.trace_mul_cycle (qutritMUBProjection 3 1) (qutritMUBProjection 1 0)
        (qutritMUBProjection 0 0)]
    _ = _ := by rw [Matrix.trace_conjTranspose, markedProjection_orderedTrace]

theorem markedProjectionSum_trace_cube : Matrix.trace (markedProjectionSum ^ 3) = 10 := by
  rw [markedProjectionSum, trace_sum_cube_idempotents _ _ _
    (qutritMUBProjection_idempotent _ _) (qutritMUBProjection_idempotent _ _)
    (qutritMUBProjection_idempotent _ _)]
  simp only [qutritMUBProjection_trace, qutritProjection_pairTrace,
    markedProjection_orderedTrace, markedProjection_reverseTrace]
  apply Complex.ext <;>
    norm_num [qutritRoot, Complex.star_def, Complex.div_re, Complex.div_im, Complex.mul_re,
      Complex.mul_im]
  ring

/-- The unnormalized cube that gives the marked three-plane energy cross term. -/
theorem markedProjectionSum_centeredTraceCube :
    Matrix.trace ((markedProjectionSum - 1) ^ 3) = 1 := by
  rw [show (markedProjectionSum - 1) ^ 3 = markedProjectionSum ^ 3 -
      (markedProjectionSum ^ 2 + markedProjectionSum ^ 2 + markedProjectionSum ^ 2) +
      (markedProjectionSum + markedProjectionSum + markedProjectionSum) - 1 by noncomm_ring]
  simp only [Matrix.trace_sub, Matrix.trace_add, markedProjectionSum_trace_cube,
    markedProjectionSum_trace_square, markedProjectionSum_trace, trace_one_matrix3]
  norm_num

end ThirteenPlanes
