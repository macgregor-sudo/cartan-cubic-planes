module

public import ThirteenPlanes.RealDerivations.Representation
public import ThirteenPlanes.ClosedBlocks.Transport

@[expose] public section

set_option backward.privateInPublic true

/-! Trace-freeness of the actual real matrix cubic. -/

open scoped Matrix BigOperators

namespace ThirteenPlanes.ClosedBlocks

open Peirce RealDerivations RoundCubics Module

noncomputable section

private theorem centered_product_matrix (x y : RealTracelessSymmetric3) :
    realTraceMatrix (realCartanCubic.L x y) =
      Real.sqrt 6 •
        ((jordan (traceMatrix x) (traceMatrix y)).val -
         (trace (jordan (traceMatrix x) (traceMatrix y)) / 3) • (1 : RealMatrix3)) := by
  rw [realCartan_product]
  change realTraceLinear (Real.sqrt 6 • readTraceZero (jordan (traceMatrix x) (traceMatrix y))) = _
  rw [map_smul]
  change Real.sqrt 6 • (traceMatrix (readTraceZero (jordan (traceMatrix x) (traceMatrix y)))).val = _
  rw [traceMatrix_readTraceZero, centerLinear_apply]
  rfl

/-- The real trace cubic is harmonic for the actual trace metric. -/
theorem realCartanCubic_traceFree : realCartanCubic.TraceFree := by
  intro x
  have hcoord (i : Fin 5) : traceCoord (coordBasis i) = Pi.single i 1 := by
    funext j
    change traceCoordEquiv (coordBasis i) j = _
    rw [← Basis.ofEquivFun_repr_apply]
    change (coordBasis.repr (coordBasis i)) j = _
    rw [Basis.repr_self, Finsupp.single_eq_pi_single]
  have hmatrix (i : Fin 5) : realTraceMatrix (coordBasis i) = traceChart (Pi.single i 1) := by
    rw [← traceChart_coord (coordBasis i), hcoord]
  rw [LinearMap.trace_eq_matrix_trace ℝ coordBasis, Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply]
  have hb (i : Fin 5) (y : RealTracelessSymmetric3) : coordBasis.repr y i = traceCoord y i := by
    simp only [coordBasis, Basis.ofEquivFun_repr_apply]
    rfl
  simp_rw [hb]
  have hcenter (y : RealTracelessSymmetric3) :
      realTraceMatrix (realCartanCubic.L x y) =
        Real.sqrt 6 •
          ((1 / 2 : ℝ) • (realTraceMatrix x * realTraceMatrix y + realTraceMatrix y * realTraceMatrix x) -
           (Matrix.trace ((1 / 2 : ℝ) •
             (realTraceMatrix x * realTraceMatrix y + realTraceMatrix y * realTraceMatrix x)) / 3) • 1) :=
    centered_product_matrix x y
  have ht : (realTraceMatrix x) 0 0 + (realTraceMatrix x) 1 1 + (realTraceMatrix x) 2 2 = 0 := by
    have hh := traceMatrix_trace x
    change Matrix.trace (realTraceMatrix x) = 0 at hh
    simpa [Matrix.trace, Fin.sum_univ_three] using hh
  simp [Fin.sum_univ_succ, traceCoord, hcenter, hmatrix, traceChart, Pi.single_apply, Matrix.trace,
    Matrix.mul_apply, Matrix.vecMul, dotProduct]
  linear_combination (5 * Real.sqrt 6 / 3) * ht

end

end ThirteenPlanes.ClosedBlocks
