module

public import ThirteenPlanes.FourPlaneUniqueness
public import ThirteenPlanes.Shares.PlaneTransport
public import ThirteenPlanes.Shares.ComplexTraceFrames
public import ThirteenPlanes.PencilFlow.Model.FourPlanes
public import ThirteenPlanes.JordanFrames.ComplexDiagonalization

@[expose] public section

set_option backward.privateInPublic true

/-! Unitary conjugation of traceless Hermitian matrices and their frame planes. -/

open scoped Matrix RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

open RoundCubics TracelessHermitian3 AlbertSequential

noncomputable section

private def unitaryTraceLinear (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    TracelessHermitian3 →ₗ[ℝ] TracelessHermitian3 where
  toFun x := ofMatrix (complexConjugate U (toMatrix x))
    (by
      change star (complexConjugate U (toMatrix x)) = _
      rw [← map_star]
      exact congrArg (complexConjugate U) x.isHermitian.eq)
    ((complexConjugate_trace U _).trans (trace_eq_zero x))
  map_add' x y := toMatrix_injective (by simp [map_add])
  map_smul' r x := toMatrix_injective (by
    change complexConjugate U (toMatrix (r • x)) = toMatrix (r • (ofMatrix _ _ _))
    simp only [toMatrix.map_smul, toMatrix_ofMatrix]
    exact map_smul (Unitary.conjStarAlgAut ℝ ComplexMatrix3 U) r _)

/-- Conjugation by a genuine complex unitary on the real traceless Hermitian space. -/
def unitaryTraceIsometry (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    TracelessHermitian3 ≃ₗᵢ[ℝ] TracelessHermitian3 :=
  let L := unitaryTraceLinear U
  let F : TracelessHermitian3 →ₗᵢ[ℝ] TracelessHermitian3 :=
    { toLinearMap := L
      norm_map' := fun x => by
        have hn : ‖L x‖ ^ 2 = ‖x‖ ^ 2 := by
          rw [norm_sq_eq_tracePairing, norm_sq_eq_tracePairing]
          change (Matrix.trace (complexConjugate U (toMatrix x) * complexConjugate U (toMatrix x))).re = _
          rw [← map_mul, complexConjugate_trace]
          rfl
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn }
  LinearIsometryEquiv.ofSurjective F (LinearMap.surjective_of_injective (f := L) F.injective)

theorem toMatrix_unitaryTraceIsometry (U : Matrix.unitaryGroup (Fin 3) ℂ) (x : TracelessHermitian3) :
    toMatrix (unitaryTraceIsometry U x) = (U : ComplexMatrix3) * toMatrix x * (U : ComplexMatrix3)ᴴ := rfl

theorem unitaryTraceIsometry_preserves_cubic (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    matrixEqualCubic.pullback (unitaryTraceIsometry U).toLinearMap = matrixEqualCubic := by
  apply Peirce.cubic_eq_of_diagonal_eq
  intro x
  rw [SymmetricCubic.pullback_apply]
  have hd (y : TracelessHermitian3) :
      matrixEqualCubic.apply y y y = (Matrix.trace (toMatrix y ^ 3)).re := by
    change ⟪jordan y y, y⟫ = _
    rw [jordan_self, real_inner_comm, inner_square_eq_trace_cube]
  rw [hd, hd]
  change (Matrix.trace (complexConjugate U (toMatrix x) ^ 3)).re = _
  rw [← map_pow, complexConjugate_trace]

private theorem centered_reference_mem (k : Fin 4) (i : Fin 3) (x : TracelessHermitian3)
    (hx : toMatrix x = qutritMUBProjection k i - (1/3 : ℂ) • (1 : ComplexMatrix3)) :
    x ∈ matrixPlane k := by
  have he : x = (1/3 : ℝ) • matrixCorner k i := by
    apply toMatrix_injective
    rw [hx, map_smul, toMatrix_matrixCorner, smul_sub, smul_smul]
    norm_num
    change (1/3 : ℂ) • (1 : ComplexMatrix3) = (((1/3 : ℝ) : ℂ)) • (1 : ComplexMatrix3)
    norm_num
  rw [he]
  exact (matrixPlane k).smul_mem _ ((mem_matrixPlane_iff _ _).mpr (matrixCorner_fixed _ _))

/-- Conjugating the three points to the standard reference frame identifies the whole plane. -/
theorem unitary_framePlane_eq_reference (F : ComplexTraceFrame3) (U : Matrix.unitaryGroup (Fin 3) ℂ)
    (k : Fin 4) (σ : Equiv.Perm (Fin 3))
    (points : ∀ i, (U : ComplexMatrix3) * F.point i * (U : ComplexMatrix3)ᴴ = qutritMUBProjection k (σ i)) :
    F.plane = (pullbackPlaneSystem (V := TracelessHermitian3) (W := TracelessHermitian3)
      fourPlaneDecomposition (unitaryTraceIsometry U)).plane k := by
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (mem_pullbackPlaneSystem _ _ _ _).mpr
    apply centered_reference_mem k (σ i)
    change complexConjugate U (traceFreePart (F.point i)) = _
    rw [traceFreePart, F.trace_one, map_sub, map_smul, map_one]
    change (U : ComplexMatrix3) * F.point i * (U : ComplexMatrix3)ᴴ - _ = _
    rw [points]
  · rw [F.plane_dimension, (pullbackPlaneSystem (V := TracelessHermitian3) (W := TracelessHermitian3)
      fourPlaneDecomposition (unitaryTraceIsometry U)).dimension]

end

end ThirteenPlanes.JordanFrames
