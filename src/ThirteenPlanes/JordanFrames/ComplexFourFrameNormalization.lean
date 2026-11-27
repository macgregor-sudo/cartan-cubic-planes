module

public import ThirteenPlanes.FourPlaneClassification

@[expose] public section

set_option backward.privateInPublic true

/-! Normalize four literal complex matrix frames via their trace-zero planes. -/

open scoped BigOperators Matrix RealInnerProductSpace

namespace ThirteenPlanes.JordanFrames

open RoundCubics

noncomputable section

set_option maxHeartbeats 4000000 in
private theorem framePlanes_exhaustive (F : Fin 4 → ComplexTraceFrame3)
    (orth : Pairwise fun i j => Submodule.IsOrtho (𝕜 := ℝ) (E := TracelessHermitian3) (F i).plane (F j).plane) :
    (⨆ i, (F i).plane) = ⊤ := by
  let U : Fin 4 → Submodule ℝ TracelessHermitian3 := fun i => (F i).plane
  change (⨆ i, U i) = ⊤
  have hdim (i : Fin 4) : Module.finrank ℝ (U i) = 2 := (F i).plane_dimension
  have horth : Pairwise fun i j => Submodule.IsOrtho (𝕜 := ℝ) (E := TracelessHermitian3) (U i) (U j) := orth
  have h := orthogonalPlaneSpan_finrank (V := TracelessHermitian3) U hdim horth
  apply Submodule.eq_top_of_finrank_eq
  rw [h, Fintype.card_fin, fourPlane_dimension]

private def frameDecomposition (F : Fin 4 → ComplexTraceFrame3)
    (hF : ∀ i j, i ≠ j → ∀ a b, tracePairing ((F i).point a) ((F j).point b) = 1 / 3) :
    PlaneDecomposition TracelessHermitian3 (Fin 4) where
  plane i := (F i).plane
  dimension i := (F i).plane_dimension
  pairwise_orthogonal i j h := (complex_framePlane_orthogonal_iff (F i) (F j)).mpr (hF i j h)
  exhaustive := framePlanes_exhaustive F (fun i j h =>
    (complex_framePlane_orthogonal_iff (F i) (F j)).mpr (hF i j h))

private theorem conjugated_plane (U : Matrix.unitaryGroup (Fin 3) ℂ) (F : ComplexTraceFrame3) :
    (conjugateComplexFrame U F).plane = F.plane.map (unitaryTraceIsometry U).toLinearMap := by
  have center (a : Fin 3) : (conjugateComplexFrame U F).center a = unitaryTraceIsometry U (F.center a) := by
    apply TracelessHermitian3.toMatrix_injective
    change traceFreePart (complexConjugate U (F.point a)) = complexConjugate U (traceFreePart (F.point a))
    simp only [traceFreePart, map_sub, map_smul, map_one, complexConjugate_trace]
  rw [ComplexTraceFrame3.plane, ComplexTraceFrame3.plane, Submodule.map_span, ← Set.range_comp]
  congr 1
  exact congrArg Set.range (funext center)

theorem normalize_complex_frames (F : Fin 4 → ComplexTraceFrame3)
    (hF : ∀ i j, i ≠ j → ∀ a b, tracePairing ((F i).point a) ((F j).point b) = 1 / 3) :
    ∃ (U : Matrix.unitaryGroup (Fin 3) ℂ) (π : Equiv.Perm (Fin 4)),
      ∀ i, (conjugateComplexFrame U (F i)).plane = matrixPlane (π i) := by
  obtain ⟨U, π, hπ⟩ := complex_closedPlaneSystem_unitary (frameDecomposition F hF)
    (fun i => (F i).plane_closed)
  refine ⟨U, π, fun i => ?_⟩
  rw [conjugated_plane]
  ext x
  change x ∈ (F i).plane.map (unitaryTraceIsometry U).toLinearMap ↔ x ∈ matrixPlane (π i)
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hπ i y).mp hy
  · intro hx
    let y := (unitaryTraceIsometry U).symm x
    have hy : unitaryTraceIsometry U y = x := (unitaryTraceIsometry U).apply_symm_apply x
    exact ⟨y, (hπ i y).mpr (hy.symm ▸ hx), hy⟩

end

end ThirteenPlanes.JordanFrames
