module

public import ThirteenPlanes.AlbertGrading.Generation.NativePlanes
public import ThirteenPlanes.AlbertGrading.Recognition.NativePairNormalization
public import ThirteenPlanes.AlbertGrading.Completion.Completion
public import ThirteenPlanes.JordanFrames.Albert

@[expose] public section

/-! Transport the completion, generation and sparsest assertions to arbitrary native closed planes. -/

namespace ThirteenPlanes.AlbertGrading

open scoped BigOperators
open RoundCubics

noncomputable section

/-- Every native decomposition into thirteen closed planes has a frame code on those planes. -/
theorem nativeCode_of_closed_planes (P : PlaneDecomposition NativeTraceless (Fin 13))
    (hP : IsClosedPlaneSystem nativeEqualCubic P) : ∃ c : TightNativeCode, c.decomposition = P := by
  choose p hp hplane using fun i => nativeClosedPlaneHasFrame (P.plane i) (P.dimension i) (hP i)
  let c : TightNativeCode := {
    point := p
    frame := hp
    overlap := fun {i j} hij => by
      apply (JordanFrames.native_framePlane_orthogonal_iff (hp i) (hp j)).mp
      rw [← hplane i, ← hplane j]
      exact P.pairwise_orthogonal hij }
  refine ⟨c, ?_⟩
  have he : c.decomposition.plane = P.plane := funext fun i => (hplane i).symm
  cases P
  simpa only [TightNativeCode.decomposition, PlaneDecomposition.mk.injEq] using he

/-- The literal plane-system formulation of the seven generating thirds. -/
theorem generationCount_closedPlanes (P : PlaneDecomposition NativeTraceless (Fin 13))
    (hP : IsClosedPlaneSystem nativeEqualCubic P) (i j : Fin 13) (hij : i ≠ j) :
    ∃ c : TightNativeCode, c.decomposition = P ∧
      7 ≤ (Finset.univ.filter fun k : Fin 13 => k ≠ i ∧ k ≠ j ∧
        generated (Set.range (c.point i) ∪ Set.range (c.point j) ∪ Set.range (c.point k)) = ⊤).card := by
  obtain ⟨c, hc⟩ := nativeCode_of_closed_planes P hP
  exact ⟨c, hc, generationCount c i j hij⟩

/-- Sparsest closed native plane systems exist, and all their frame idempotents are conjugate. -/
theorem sparsest_closedPlaneSystems :
    (∃ P : PlaneDecomposition NativeTraceless (Fin 13), IsClosedPlaneSystem nativeEqualCubic P ∧
      (positivePlaneTriples nativeEqualCubic P).card = 52) ∧
    ∀ P Q : PlaneDecomposition NativeTraceless (Fin 13),
      IsClosedPlaneSystem nativeEqualCubic P → IsClosedPlaneSystem nativeEqualCubic Q →
      (positivePlaneTriples nativeEqualCubic P).card = 52 →
      (positivePlaneTriples nativeEqualCubic Q).card = 52 →
      ∃ c d : TightNativeCode, c.decomposition = P ∧ d.decomposition = Q ∧
        ∃ φ : Glennie.CompactAutomorphism, ∃ σ : Equiv.Perm (Fin 13),
          ∃ τ : Fin 13 → Equiv.Perm (Fin 3),
            ∀ i a, φ.equiv (c.point i a) = d.point (σ i) (τ i a) := by
  obtain ⟨⟨c, hc⟩, hconj⟩ := nativeSparsest
  refine ⟨⟨c.decomposition, fun i => framePlane_closed (c.frame i), hc⟩, ?_⟩
  intro P Q hP hQ hsizeP hsizeQ
  obtain ⟨c, hc⟩ := nativeCode_of_closed_planes P hP
  obtain ⟨d, hd⟩ := nativeCode_of_closed_planes Q hQ
  refine ⟨c, d, hc, hd, hconj c d ?_ ?_⟩
  · rwa [hc]
  · rwa [hd]

/-- Twelve orthogonal closed two-planes have one orthogonal closed two-plane. -/
theorem completionO_uniqueClosedPlane (P : Fin 12 → Submodule ℝ NativeTraceless)
    (dim : ∀ i, Module.finrank ℝ (P i) = 2) (closed : ∀ i, IsClosedPiece nativeEqualCubic (P i))
    (orth : Pairwise fun i j => (P i).IsOrtho (P j)) :
    ∃! Q : Submodule ℝ NativeTraceless,
      Module.finrank ℝ Q = 2 ∧ IsClosedPiece nativeEqualCubic Q ∧ ∀ i, (P i).IsOrtho Q := by
  let Q := (⨆ i, P i)ᗮ
  obtain ⟨q, hq, he⟩ := complement_isFramePlane P dim closed orth
  refine ⟨Q, ⟨complement_finrank P dim orth, ?_, fun i => ?_⟩, ?_⟩
  · change IsClosedPiece nativeEqualCubic (⨆ i, P i)ᗮ
    rw [← he]
    exact framePlane_closed hq
  · exact (Submodule.isOrtho_iff_le.mpr (Submodule.orthogonal_le (le_iSup P i))).symm
  · rintro U ⟨hU, _, horth⟩
    exact eq_complement_of_orthogonal P dim orth U hU horth

end

end ThirteenPlanes.AlbertGrading
