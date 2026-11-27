/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.FourPlanes
public import ThirteenPlanes.FourPlanesMarkedTrace
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Energy on fields in one or two planes and on the marked three-plane share. -/

noncomputable section

namespace ThirteenPlanes

open AlbertSequential TracelessHermitian3

theorem matrixSquare_smul (r : ℝ) (x : TracelessHermitian3) :
    square (r • x) = r ^ 2 • square x := by
  simp [← jordan_self, smul_smul, pow_two]

@[simp] theorem matrixSquare_zero : square (0 : TracelessHermitian3) = 0 := by
  simp [← jordan_self]

theorem matrixFrameProjection_fixed (k l : Fin 4) (x : TracelessHermitian3)
    (hx : matrixFrameProjection l x = x) :
    matrixFrameProjection k x = if k = l then x else 0 := by
  simpa only [hx] using matrixFrameProjection_comp k l x

theorem matrixFrameOrthogonality (k l : Fin 4) (hkl : k ≠ l)
    (x y : TracelessHermitian3) (hx : matrixFrameProjection k x = x)
    (hy : matrixFrameProjection l y = y) : inner ℝ x y = 0 := by
  calc
    _ = inner ℝ (matrixFrameProjection k x) y := by rw [hx]
    _ = _ := by
      rw [matrixFrameProjection_inner_swap, matrixFrameProjection_fixed k l y hy, ite_eq_right hkl,
        inner_zero_right]

theorem matrixDiagonalSquare_single (k : Fin 4) (x : TracelessHermitian3)
    (hx : matrixFrameProjection k x = x) : matrixDiagonalCubic.squareMap x = square x := by
  rw [matrixDiagonalCubic_squareMap]
  simp only [matrixFrameProjection_fixed _ k _ hx, apply_ite square, matrixSquare_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem fourPlane_singleEnergy (k : Fin 4) (x : TracelessHermitian3)
    (hx : matrixFrameProjection k x = x) (hunit : ‖x‖ = 1) (a b : ℝ) :
    unitEnergy (coupling fourPlanePair (a, b)) x = a ^ 2 := by
  rw [unitEnergy, coupling_fourPlanePair, SymmetricCubic.squareMap_add, SymmetricCubic.squareMap_smul,
    SymmetricCubic.squareMap_smul, matrixDiagonalSquare_single k x hx, matrixEqualCubic_squareMap,
    ← add_smul, sub_add_cancel, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, square_norm_sq, hunit]
  ring

def matrixCornerCoeff (b c : Fin 3) : ℝ := if c = b then 2 else -1

theorem matrixCornerCoeff_sum (b : Fin 3) : ∑ c, matrixCornerCoeff b c = 0 := by
  fin_cases b <;> norm_num [matrixCornerCoeff, Fin.sum_univ_three]

/-- The vector (3q-I) for the selected rank-one projection. It has squared norm six. -/
def matrixCorner (k : Fin 4) (b : Fin 3) : TracelessHermitian3 :=
  ofMatrix (matrixFrameSynthesis k (matrixCornerCoeff b))
    (matrixFrameSynthesis_hermitian _ _) (by simp [matrixCornerCoeff_sum])

theorem matrixCorner_fixed (k : Fin 4) (b : Fin 3) :
    matrixFrameProjection k (matrixCorner k b) = matrixCorner k b :=
  matrixFrameProjection_synthesis _ _ (matrixCornerCoeff_sum b)

theorem matrixCorner_square (k : Fin 4) (b : Fin 3) : square (matrixCorner k b) = matrixCorner k b := by
  apply toMatrix_injective
  simp only [toMatrix_square, matrixCorner, toMatrix_ofMatrix, tracelessSquare,
    matrixFrameSynthesis_mul, traceFreePart_matrixFrameSynthesis]
  congr 1
  funext c
  fin_cases b <;> fin_cases c <;> norm_num [matrixCornerCoeff, Fin.sum_univ_three]

theorem matrixCorner_norm_sq (k : Fin 4) (b : Fin 3) : ‖matrixCorner k b‖ ^ 2 = 6 := by
  simp only [norm_sq_eq_tracePairing, matrixCorner, toMatrix_ofMatrix, tracePairing_synthesis_left,
    matrixFrameAnalysis_synthesis]
  fin_cases b <;> norm_num [matrixCornerCoeff, Fin.sum_univ_three]

theorem toMatrix_matrixCorner (k : Fin 4) (b : Fin 3) :
    toMatrix (matrixCorner k b) = (3 : ℝ) • qutritMUBProjection k b - 1 := by
  change matrixFrameSynthesis k (matrixCornerCoeff b) = _
  let single : Fin 3 → ℝ := Pi.single b 1
  have h : matrixCornerCoeff b = (3 : ℝ) • single - fun _ => 1 := by
    funext c
    by_cases h : c = b <;> norm_num [matrixCornerCoeff, single, h]
  have hsingle : matrixFrameSynthesis k single = qutritMUBProjection k b := by
    change (∑ c, single c • qutritMUBProjection k c) = _
    simp [single]
  rw [h, map_sub, map_smul, hsingle, matrixFrameSynthesis_const, one_smul]

def markedCornerTriple : TracelessHermitian3 := matrixCorner 0 0 + matrixCorner 1 0 + matrixCorner 3 1

/-- The unit equal share of the three specified corners in the paper. -/
def fourPlaneMarkedThree : TracelessHermitian3 := (Real.sqrt 18)⁻¹ • markedCornerTriple

theorem markedCornerTriple_norm_sq : ‖markedCornerTriple‖ ^ 2 = 18 := by
  rw [markedCornerTriple, norm_add_sq_real, norm_add_sq_real, inner_add_left,
    matrixCorner_norm_sq, matrixCorner_norm_sq, matrixCorner_norm_sq,
    matrixFrameOrthogonality 0 1 (by decide) _ _ (matrixCorner_fixed _ _) (matrixCorner_fixed _ _),
    matrixFrameOrthogonality 0 3 (by decide) _ _ (matrixCorner_fixed _ _) (matrixCorner_fixed _ _),
    matrixFrameOrthogonality 1 3 (by decide) _ _ (matrixCorner_fixed _ _) (matrixCorner_fixed _ _)]
  ring

theorem markedCornerTriple_diagonalSquare : matrixDiagonalCubic.squareMap markedCornerTriple =
    markedCornerTriple := by
  rw [matrixDiagonalCubic_squareMap, markedCornerTriple]
  simp only [map_add, matrixFrameProjection_fixed _ _ _ (matrixCorner_fixed _ _)]
  norm_num [Fin.sum_univ_succ, matrixCorner_square, add_assoc]

theorem inner_square_eq_trace_cube (x : TracelessHermitian3) :
    inner ℝ x (square x) = (Matrix.trace (toMatrix x ^ 3)).re := by
  rw [real_inner_comm (square x) x, inner_eq_tracePairing, toMatrix_square, tracelessSquare,
    tracePairing_traceFreePart_left _ _ x.trace_eq_zero, tracePairing, pow_succ, pow_two]

theorem markedCornerTriple_inner_square : inner ℝ markedCornerTriple (square markedCornerTriple) = 27 := by
  have h : toMatrix markedCornerTriple = (3 : ℂ) • (markedProjectionSum - 1) := by
    simp only [markedCornerTriple, map_add, toMatrix_matrixCorner, markedProjectionSum, smul_sub,
      smul_add]
    change (3 : ℂ) • qutritMUBProjection 0 0 - 1 + ((3 : ℂ) • qutritMUBProjection 1 0 - 1) +
      ((3 : ℂ) • qutritMUBProjection 3 1 - 1) =
      (3 : ℂ) • qutritMUBProjection 0 0 + (3 : ℂ) • qutritMUBProjection 1 0 +
        (3 : ℂ) • qutritMUBProjection 3 1 - (3 : ℂ) • (1 : ComplexMatrix3)
    rw [show (3 : ℂ) • (1 : ComplexMatrix3) =
      (1 : ComplexMatrix3) + 1 + 1 by
        have hthree : (3 : ℂ) = 1 + 1 + 1 := by norm_num
        rw [hthree, add_smul, add_smul, one_smul]]
    abel
  rw [inner_square_eq_trace_cube, h]
  simp only [pow_succ, pow_zero, one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul]
  have hc : Matrix.trace ((markedProjectionSum - 1) * (markedProjectionSum - 1) *
      (markedProjectionSum - 1)) = 1 := by
    simpa only [pow_succ, pow_zero, one_mul] using markedProjectionSum_centeredTraceCube
  rw [hc]
  norm_num

theorem norm_rescaled_by_sqrt (x : TracelessHermitian3) (N : ℝ) (hN : 0 < N)
    (hx : ‖x‖ ^ 2 = N) : ‖(Real.sqrt N)⁻¹ • x‖ = 1 := by
  have h : ‖x‖ = Real.sqrt N := by
    rw [← hx, Real.sqrt_sq (norm_nonneg _)]
  rw [norm_smul, h, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 hN)),
    inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hN)]

theorem fourPlaneMarkedThree_unit : ‖fourPlaneMarkedThree‖ = 1 :=
  norm_rescaled_by_sqrt _ _ (by norm_num) markedCornerTriple_norm_sq

theorem fourPlaneMarkedThree_energy (a b : ℝ) :
    unitEnergy (coupling fourPlanePair (a, b)) fourPlaneMarkedThree =
      (a ^ 2 + a * b + b ^ 2) / 3 := by
  have hs : ((Real.sqrt 18)⁻¹) ^ 2 = (1 / 18 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num), one_div]
  rw [unitEnergy, fourPlaneMarkedThree, coupling_fourPlanePair_squareMap]
  simp only [map_smul, matrixSquare_smul, hs, ← Finset.smul_sum]
  rw [← matrixDiagonalCubic_squareMap, markedCornerTriple_diagonalSquare]
  simp only [smul_smul]
  have hin (r s : ℝ) : inner ℝ (r • markedCornerTriple) (s • square markedCornerTriple) =
      r * (s * 27) := by
    rw [real_inner_smul_left markedCornerTriple, real_inner_smul_right markedCornerTriple,
      markedCornerTriple_inner_square]
  have hsquare : ‖square markedCornerTriple‖ ^ 2 = 54 := by
    rw [square_norm_sq]
    calc
      _ = (‖markedCornerTriple‖ ^ 2) ^ 2 / 6 := by ring
      _ = _ := by rw [markedCornerTriple_norm_sq]; norm_num
  rw [norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs, hin, hsquare, markedCornerTriple_norm_sq]
  ring

end ThirteenPlanes
