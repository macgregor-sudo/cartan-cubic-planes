module

public import ThirteenPlanes.JordanFrames.Generic
public import ThirteenPlanes.Shares.ComplexTraceFrames
public import ThirteenPlanes.PilotContractions

@[expose] public section

/-! The frame-plane correspondence and capacity on the complex Hermitian trace carrier. -/

open scoped BigOperators Matrix RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

open RoundCubics

noncomputable section

/-- Centering a complex matrix frame point in the actual Hermitian trace-zero model. -/
def complexCenterPoint (F : ComplexTraceFrame3) (i : Fin 3) : TracelessHermitian3 :=
  TracelessHermitian3.ofMatrix (traceFreePart (F.point i))
    (traceFreePart_hermitian (F.hermitian i)) (trace_traceFreePart _)

theorem complex_plane_eq_centered_span (F : ComplexTraceFrame3) :
    F.plane = Submodule.span ℝ (Set.range (complexCenterPoint F)) := rfl

theorem complexCenterPoint_matrix (F : ComplexTraceFrame3) (i : Fin 3) :
    (complexCenterPoint F i).toMatrix = F.point i - (1 / 3 : ℂ) • (1 : ComplexMatrix3) := by
  change traceFreePart (F.point i) = _
  rw [traceFreePart, F.trace_one]

def complexTrace : ComplexMatrix3 →ₗ[ℝ] ℝ where
  toFun X := (Matrix.trace X).re
  map_add' X Y := by rw [Matrix.trace_add, Complex.add_re]
  map_smul' r X := by rw [Matrix.trace_smul]; exact Complex.reLm.map_smul r _

def complexJordan : ComplexMatrix3 →ₗ[ℝ] ComplexMatrix3 →ₗ[ℝ] ComplexMatrix3 :=
  (1 / 2 : ℝ) • (LinearMap.mul ℝ ComplexMatrix3 + (LinearMap.mul ℝ ComplexMatrix3).flip)

theorem complexJordan_apply (X Y : ComplexMatrix3) :
    complexJordan X Y = symmetricMatrixProduct X Y := by
  change ((1 / 2 : ℝ) : ℂ) • (X * Y + Y * X) = (1 / 2 : ℂ) • (X * Y + Y * X)
  push_cast
  rfl

/-- Complex frame planes agree if and only if their actual idempotents agree after a permutation. -/
theorem complex_framePlane_eq_iff_relabel (F G : ComplexTraceFrame3) :
    F.plane = G.plane ↔ ∃ σ : Equiv.Perm (Fin 3), ∀ i, G.point i = F.point (σ i) := by
  rw [complex_plane_eq_centered_span F, complex_plane_eq_centered_span G]
  constructor
  · intro heq
    have h := congrArg (fun U : Submodule ℝ TracelessHermitian3 =>
      U.map TracelessHermitian3.toMatrix) heq
    simp only [Submodule.map_span, ← Set.range_comp] at h
    have hc (H : ComplexTraceFrame3) :
        TracelessHermitian3.toMatrix ∘ complexCenterPoint H =
          fun i => H.point i - (1 / 3 : ℝ) • (1 : ComplexMatrix3) := by
      funext i
      change (complexCenterPoint H i).toMatrix = _
      rw [complexCenterPoint_matrix]
      change H.point i - (1 / 3 : ℂ) • (1 : ComplexMatrix3) =
        H.point i - ((1 / 3 : ℝ) : ℂ) • (1 : ComplexMatrix3)
      push_cast
      rfl
    rw [hc F, hc G] at h
    refine relabel_of_centered_span_eq complexJordan complexTrace 1 ?_ ?_ ?_ ?_ F.sum_unit h
    · intro i
      change (Matrix.trace (F.point i)).re = 1
      rw [F.trace_one, Complex.one_re]
    · intro i
      change (Matrix.trace (G.point i)).re = 1
      rw [G.trace_one, Complex.one_re]
    · intro i j
      rw [complexJordan_apply, F.jordan_point]
    · intro i j
      rw [complexJordan_apply, G.jordan_point]
  · rintro ⟨σ, hσ⟩
    have hc (i : Fin 3) : complexCenterPoint G i = complexCenterPoint F (σ i) := by
      apply TracelessHermitian3.toMatrix_injective
      simp only [complexCenterPoint_matrix, hσ]
    congr 1
    apply Set.Subset.antisymm
    · rintro _ ⟨i, rfl⟩
      exact ⟨σ.symm i, by rw [hc, σ.apply_symm_apply]⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨σ i, (hc i).symm⟩

/-- The centered trace Gram identity for two complex frame idempotents. -/
theorem complex_frame_centered_inner (F G : ComplexTraceFrame3) (i j : Fin 3) :
    ⟪complexCenterPoint F i, complexCenterPoint G j⟫ =
      tracePairing (F.point i) (G.point j) - 1 / 3 := by
  rw [TracelessHermitian3.inner_eq_tracePairing]
  change tracePairing (traceFreePart (F.point i)) (complexCenterPoint G j).toMatrix = _
  rw [tracePairing_traceFreePart_left _ _ (complexCenterPoint G j).trace_eq_zero,
    complexCenterPoint_matrix, tracePairing, tracePairing, mul_sub, Matrix.mul_smul, mul_one,
    Matrix.trace_sub, Matrix.trace_smul]
  have h := F.trace_one i
  rw [h]
  norm_num [smul_eq_mul, Complex.sub_re, Complex.div_re, Complex.mul_re]

/-- Two complex trace-zero frame planes are orthogonal exactly when their frames are unbiased. -/
theorem complex_framePlane_orthogonal_iff (F G : ComplexTraceFrame3) :
    Submodule.IsOrtho (𝕜 := ℝ) (E := TracelessHermitian3) F.plane G.plane ↔ ∀ i j, tracePairing (F.point i) (G.point j) = 1 / 3 := by
  rw [complex_plane_eq_centered_span, complex_plane_eq_centered_span,
    Submodule.isOrtho_span]
  constructor
  · intro h i j
    exact sub_eq_zero.mp ((complex_frame_centered_inner F G i j).symm.trans
      (h ⟨i, rfl⟩ ⟨j, rfl⟩))
  · rintro h _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rw [complex_frame_centered_inner, h, sub_self]


end
end ThirteenPlanes.JordanFrames
