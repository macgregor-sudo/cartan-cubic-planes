/- SPDX-License-Identifier: Apache-2.0 -/

module

public import ThirteenPlanes.FourPlanesDecomposition

@[expose] public section

/-! The trace-free plane restrictions required by the common contraction proof. -/

noncomputable section

namespace ThirteenPlanes

open TracelessHermitian3

def matrixPlaneChartEquiv (k : Fin 4) : (Fin 2 → ℝ) ≃ₗ[ℝ] matrixPlane k :=
  LinearEquiv.ofBijective ((matrixPlaneChart k).codRestrict (matrixPlane k)
    (fun u => (mem_matrixPlane_iff k _).2 (matrixPlaneChart_fixed k u))) (by
      constructor
      · intro u v h
        exact matrixPlaneChart_injective k (congrArg Subtype.val h)
      · intro x
        have hx : (x : TracelessHermitian3) ∈ LinearMap.range (matrixPlaneChart k) := by
          rw [matrixPlaneChart_range]
          exact x.property
        obtain ⟨u, hu⟩ := hx
        exact ⟨u, Subtype.ext hu⟩)

theorem matrixPlaneChartEquiv_symm_apply (k : Fin 4) (x : matrixPlane k) (b : Fin 2) :
    (matrixPlaneChartEquiv k).symm x b = matrixFrameAnalysis k (toMatrix x) b.castSucc := by
  have h := congrArg (fun w : matrixPlane k => matrixFrameAnalysis k (toMatrix w) b.castSucc)
    ((matrixPlaneChartEquiv k).apply_symm_apply x)
  change matrixFrameAnalysis k (matrixFrameSynthesis k
    (traceFreeDiagonalEntries ((matrixPlaneChartEquiv k).symm x))) b.castSucc = _ at h
  rw [matrixFrameAnalysis_synthesis, ite_eq_left rfl] at h
  fin_cases b <;> exact h

theorem matrixPlane_restriction_L (k : Fin 4) (x y : matrixPlane k) :
    ((fourPlaneDecomposition.restriction k (interactionCubic fourPlanePair 1)).L x y :
      TracelessHermitian3) = jordan x y := by
  let j : matrixPlane k := ⟨jordan x y, (mem_matrixPlane_iff k _).2 (project_jordan_of_fixed k _ _
    ((mem_matrixPlane_iff k _).1 x.property) ((mem_matrixPlane_iff k _).1 y.property))⟩
  suffices h : (fourPlaneDecomposition.restriction k (interactionCubic fourPlanePair 1)).L x y =
      j by exact congrArg Subtype.val h
  apply ext_inner_right ℝ
  intro z
  change (fourPlaneDecomposition.restriction k (interactionCubic fourPlanePair 1)).apply x y z = _
  rw [PlaneDecomposition.restriction_apply,
    interactionCubic_fourPlanePair_one]
  rfl

theorem matrixPlane_slice_traceFree (k : Fin 4) :
    (fourPlaneDecomposition.restriction k (interactionCubic fourPlanePair 1)).TraceFree := by
  intro x
  let r := matrixFrameAnalysis k (toMatrix x)
  let e := matrixPlaneChartEquiv k
  let f : Module.End ℝ (matrixPlane k) :=
    (fourPlaneDecomposition.restriction k (interactionCubic fourPlanePair 1)).L x
  let g := e.symm.conj f
  have hr : r 2 = -(r 0 + r 1) := by
    have h : ∑ b, r b = 0 := by
      change (∑ b, matrixFrameAnalysis k (toMatrix x) b) = _
      rw [sum_matrixFrameAnalysis, trace_eq_zero, Complex.zero_re]
    rw [Fin.sum_univ_three] at h
    linarith
  have hcoeff (u : Fin 2 → ℝ) (b : Fin 2) :
      g u b = r b.castSucc * traceFreeDiagonalEntries u b.castSucc -
        (∑ c, r c * traceFreeDiagonalEntries u c) / 3 := by
    let y := e u
    change (matrixPlaneChartEquiv k).symm (f y) b = _
    rw [matrixPlaneChartEquiv_symm_apply]
    change matrixFrameAnalysis k (toMatrix
      ((fourPlaneDecomposition.restriction k (interactionCubic fourPlanePair 1)).L x y :
        TracelessHermitian3)) b.castSucc = _
    rw [matrixPlane_restriction_L]
    have hmat := toMatrix_jordan_matrixFrameProjection k x y
    rw [(mem_matrixPlane_iff k _).1 x.property, (mem_matrixPlane_iff k _).1 y.property] at hmat
    have hy : matrixFrameAnalysis k (toMatrix y) = traceFreeDiagonalEntries u := by
      funext c
      change matrixFrameAnalysis k (matrixFrameSynthesis k (traceFreeDiagonalEntries u)) c = _
      simp [matrixFrameAnalysis_synthesis]
    rw [hmat, hy, matrixFrameAnalysis_synthesis, ite_eq_left rfl]
  change LinearMap.trace ℝ (matrixPlane k) f = 0
  rw [← LinearMap.trace_conj' f e.symm]
  change LinearMap.trace ℝ (Fin 2 → ℝ) g = 0
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 2))]
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, LinearMap.toMatrix_apply,
    Pi.basisFun_repr, Pi.basisFun_apply, hcoeff]
  norm_num [traceFreeDiagonalEntries, Fin.sum_univ_three, Pi.single_apply, hr]
  ring

theorem fourPlaneData : HasPlaneData fourPlanePair fourPlaneDecomposition where
  diagonal_eq := fourPlaneDecomposition_diagonal_eq
  traceFree := matrixPlane_slice_traceFree
  repeatedPlane := fourPlaneDecomposition_repeatedPlane

end ThirteenPlanes
