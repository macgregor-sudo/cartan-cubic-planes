module

public import ThirteenPlanes.Cartan.OperatorTransport
public import ThirteenPlanes.ClosedBlocks.Transport

@[expose] public section

/-! Rotating a subfamily of an orthogonal decomposition while preserving its span. -/

namespace ThirteenPlanes.Cartan

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*}

/-- The subspaces with indices on the chosen line are transported by the given map. -/
def rotatedSummands (U : ι → Submodule ℝ V) (L : Set ι) (g : V ≃ₗᵢ[ℝ] V) (i : ι) :
    Submodule ℝ V := by
  classical
  exact if i ∈ L then (U i).map g.toLinearMap else U i

theorem rotatedSummands_orthogonalSplit [DecidableEq ι] [FiniteDimensional ℝ V]
    (U : ι → Submodule ℝ V) (split : OrthogonalSplit U) (L : Set ι) (g : V ≃ₗᵢ[ℝ] V)
    (preserves : (⨆ i : L, U i.val).map g.toLinearMap = ⨆ i : L, U i.val) :
    OrthogonalSplit (rotatedSummands U L g) := by
  classical
  let B := ⨆ i : L, U i.val
  let W := rotatedSummands U L g
  have inside {i} (hi : i ∈ L) : (U i).map g.toLinearMap ≤ B := by
    change (U i).map g.toLinearMap ≤ ⨆ j : L, U j.val
    rw [← preserves]
    exact Submodule.map_mono (le_iSup (fun j : L => U j.val) ⟨i, hi⟩)
  have outside {j} (hj : j ∉ L) : B.IsOrtho (U j) := by
    apply Submodule.isOrtho_iSup_left.mpr
    intro i
    exact split.1 (fun h => hj (h ▸ i.property))
  have ortho : Pairwise (fun i j => (W i).IsOrtho (W j)) := by
    intro i j hne
    by_cases hi : i ∈ L <;> by_cases hj : j ∈ L
    · simpa only [W, rotatedSummands, ite_eq_left hi, ite_eq_left hj] using
        RoundCubics.isOrtho_map_isometry g (split.1 hne)
    · simp only [W, rotatedSummands, ite_eq_left hi, ite_eq_right hj]
      exact Submodule.isOrtho_iff_le.mpr ((inside hi).trans (outside hj).le)
    · simp only [W, rotatedSummands, ite_eq_right hi, ite_eq_left hj]
      exact (Submodule.isOrtho_iff_le.mpr ((inside hj).trans (outside hi).le)).symm
    · simpa only [W, rotatedSummands, ite_eq_right hi, ite_eq_right hj] using split.1 hne
  have line : B ≤ ⨆ i, W i := by
    change (⨆ i : L, U i.val) ≤ _
    rw [← preserves, Submodule.map_iSup]
    apply iSup_le
    intro i
    calc
      (U i.val).map g.toLinearMap = W i.val := by simp only [W, rotatedSummands, ite_eq_left i.property]
      _ ≤ iSup W := le_iSup W i.val
  have spans : iSup W = ⊤ := by
    apply top_unique
    rw [← split.2.submodule_iSup_eq_top]
    apply iSup_le
    intro i
    by_cases hi : i ∈ L
    · exact (le_iSup (fun j : L => U j.val) ⟨i, hi⟩).trans line
    · simpa only [W, rotatedSummands, ite_eq_right hi] using le_iSup W i
  exact ⟨ortho, (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).mpr
    ⟨(OrthogonalFamily.of_pairwise ortho).independent, spans⟩⟩

variable [FiniteDimensional ℝ V]

/-- The common fixed spaces of the rotated skew summands rotate by the original isometry. -/
theorem rotatedSummands_fixedSpaces (T : ι → Submodule ℝ (SkewOperator V)) (L : Set ι)
    (g : V ≃ₗᵢ[ℝ] V) (i : ι) :
    fixedSpace (rotatedSummands T L (conjugateSkew g) i) =
      rotatedSummands (fun j => fixedSpace (T j)) L g i := by
  classical
  by_cases hi : i ∈ L
  · simpa only [rotatedSummands, ite_eq_left hi] using fixedSpace_conjugate g (T i)
  · simp only [rotatedSummands, ite_eq_right hi]

end

end ThirteenPlanes.Cartan
