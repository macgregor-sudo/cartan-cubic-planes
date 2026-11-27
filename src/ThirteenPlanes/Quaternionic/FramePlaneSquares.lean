module

public import ThirteenPlanes.Quaternionic.Capacity
public import Mathlib.Tactic.Module

@[expose] public section

/-! # Matrix square sum of the actual orthonormal basis of a frame plane -/

noncomputable section

open scoped BigOperators Matrix

namespace QuaternionicMUB

lemma Frame.centeredHilbert_matrix (F : Frame) (a : Outcome) :
    matrixHilbertEquiv (F.centeredHilbert a).val = F.centeredPointMatrix a := by
  exact congrArg Subtype.val
    (tracelessHilbertEquiv.apply_symm_apply (F.centeredPoint a))

lemma Frame.planeOrtho_matrix_zero (F : Frame) :
    matrixHilbertEquiv (F.planeOrtho 0).val =
      Real.sqrt (3 / 2 : ℝ) • F.centeredPointMatrix 0 := by
  rw [F.planeOrtho_zero]
  change matrixHilbertEquiv (Real.sqrt (3 / 2 : ℝ) • (F.centeredHilbert 0).val) = _
  rw [map_smul, F.centeredHilbert_matrix]

lemma Frame.planeOrtho_matrix_one (F : Frame) :
    matrixHilbertEquiv (F.planeOrtho 1).val =
      Real.sqrt 2 • (F.centeredPointMatrix 1 + (1 / 2 : ℝ) • F.centeredPointMatrix 0) := by
  rw [F.planeOrtho_one]
  change matrixHilbertEquiv (Real.sqrt 2 •
    ((F.centeredHilbert 1).val + (1 / 2 : ℝ) • (F.centeredHilbert 0).val)) = _
  rw [map_smul, map_add, map_smul, F.centeredHilbert_matrix, F.centeredHilbert_matrix]

lemma real_smul_square (r : ℝ) (A : QMat) : (r • A) ^ 2 = r ^ 2 • A ^ 2 := by
  simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- The matrix square sum is literal, not a trace-only or supplied certificate. -/
theorem Frame.planeOrtho_square_sum (F : Frame) :
    (matrixHilbertEquiv (F.planeOrtho 0).val) ^ 2 +
      (matrixHilbertEquiv (F.planeOrtho 1).val) ^ 2 = (2 / 3 : ℝ) • (1 : QMat) := by
  have h0 : F.point 0 * F.point 0 = F.point 0 := by
    simpa only [jordan_self] using F.idempotent 0
  have h1 : F.point 1 * F.point 1 = F.point 1 := by
    simpa only [jordan_self] using F.idempotent 1
  have h01 : F.point 1 * F.point 0 + F.point 0 * F.point 1 = 0 := by
    have h := F.orthogonal 1 0 (by decide)
    rw [jordan] at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have h10 : F.point 1 * F.point 0 = -(F.point 0 * F.point 1) :=
    eq_neg_of_add_eq_zero_left h01
  have hs3 : Real.sqrt (3 / 2 : ℝ) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [F.planeOrtho_matrix_zero, F.planeOrtho_matrix_one,
    real_smul_square, real_smul_square, hs3, hs2]
  simp only [Frame.centeredPointMatrix, pow_two, add_mul, mul_add, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul, h0, h1, h10]
  module

end QuaternionicMUB
