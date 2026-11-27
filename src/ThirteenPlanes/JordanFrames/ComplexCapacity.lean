module

public import ThirteenPlanes.JordanFrames.Complex

@[expose] public section

/-! Dimension count for closed planes and unbiased frames on the complex trace carrier. -/

open scoped BigOperators

namespace ThirteenPlanes.JordanFrames

open RoundCubics

noncomputable section

set_option maxHeartbeats 800000 in
/-- The dimension bound and equality criterion for arbitrary sets of complex frames. -/
theorem complex_frameSet_capacity (S : Set ComplexTraceFrame3)
    (orth : S.Pairwise fun F G => ∀ i j, tracePairing (F.point i) (G.point j) = 1 / 3) :
    S.Finite ∧ S.ncard ≤ 4 ∧ ((⨆ f : S, f.val.plane) = ⊤ ↔ S.ncard = 4) := by
  have hNoFive (e : Fin 5 ↪ S) : False := by
    let U : Fin 5 → Submodule ℝ TracelessHermitian3 := fun i => (e i).val.plane
    have horth : Pairwise fun i j =>
        Submodule.IsOrtho (𝕜 := ℝ) (E := TracelessHermitian3) (U i) (U j) := by
      intro i j hij
      apply (complex_framePlane_orthogonal_iff (e i).val (e j).val).mpr
      exact orth (e i).property (e j).property (fun h => hij (e.injective (Subtype.ext h)))
    have hfin := orthogonalPlaneSpan_finrank (V := TracelessHermitian3)
      U (fun i => (e i).val.plane_dimension) horth
    have hle := Submodule.finrank_le (⨆ i, U i)
    rw [hfin, Fintype.card_fin, fourPlane_dimension] at hle
    omega
  have hfinite : S.Finite := by
    by_contra hinfinite
    exact hNoFive (Fin.valEmbedding.trans (Set.Infinite.natEmbedding S hinfinite))
  let := hfinite.fintype
  let U : S → Submodule ℝ TracelessHermitian3 := fun F => F.val.plane
  have horth : Pairwise fun F G =>
      Submodule.IsOrtho (𝕜 := ℝ) (E := TracelessHermitian3) (U F) (U G) := by
    intro F G hFG
    exact (complex_framePlane_orthogonal_iff F.val G.val).mpr
      (orth F.property G.property (fun h => hFG (Subtype.ext h)))
  have hfin : Module.finrank ℝ (↥(⨆ F, U F)) = 2 * S.ncard := by
    rw [orthogonalPlaneSpan_finrank (V := TracelessHermitian3)
      U (fun F => F.val.plane_dimension) horth, Set.fintypeCard_eq_ncard]
  have hle := Submodule.finrank_le (⨆ F, U F)
  rw [hfin, fourPlane_dimension] at hle
  refine ⟨hfinite, by omega, ?_, ?_⟩
  · intro htop
    change (⨆ F, U F) = ⊤ at htop
    rw [htop, finrank_top, fourPlane_dimension] at hfin
    omega
  · intro hcard
    change (⨆ F, U F) = ⊤
    apply Submodule.eq_top_of_finrank_eq
    rw [hfin, hcard, fourPlane_dimension]

set_option maxHeartbeats 800000 in
/-- A complete system of complex closed planes has four planes. -/
theorem complex_completePlane_count {ι : Type*} [Fintype ι]
    (P : PlaneDecomposition TracelessHermitian3 ι) :
    Fintype.card ι = 4 := by
  have h := orthogonalPlaneSpan_finrank (V := TracelessHermitian3) P.plane P.dimension
    P.pairwise_orthogonal
  rw [P.exhaustive, finrank_top, fourPlane_dimension] at h
  omega

end
end ThirteenPlanes.JordanFrames
