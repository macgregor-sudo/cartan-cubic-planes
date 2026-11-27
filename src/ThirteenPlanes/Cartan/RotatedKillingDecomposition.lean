module

public import ThirteenPlanes.Cartan.LieCompactConjugation
public import Mathlib.LinearAlgebra.DirectSum.Finite

@[expose] public section

/-! Partial conjugation of a Killing-orthogonal Cartan decomposition. -/

namespace ThirteenPlanes.Cartan

open LieAlgebra

noncomputable section

variable {K ι : Type*} [LieRing K] [LieAlgebra ℝ K] [Fintype ι] [DecidableEq ι]

/-- Apply the Lie automorphism to just the specified Cartan summands. -/
def rotatedKillingCartans (T : ι → LieSubalgebra ℝ K) (L : Set ι) (e : K ≃ₗ⁅ℝ⁆ K)
    (i : ι) : LieSubalgebra ℝ K := by
  classical
  exact if i ∈ L then (T i).map e.toLieHom else T i

/-- If conjugation preserves the sum of the selected Cartans, partial conjugation preserves
the Cartan property, pairwise Killing orthogonality and the internal direct sum. -/
theorem rotatedKillingCartans_isOD [Module.Finite ℝ K] (T : ι → LieSubalgebra ℝ K)
    (hT : IsKillingCartanOD T) (L : Set ι) (e : K ≃ₗ⁅ℝ⁆ K)
    (normalizes : (⨆ i : L, (T i.val).toSubmodule).map e.toLinearMap = ⨆ i : L, (T i.val).toSubmodule) :
    IsKillingCartanOD (rotatedKillingCartans T L e) := by
  classical
  let W := rotatedKillingCartans T L e
  let B := ⨆ i : L, (T i.val).toSubmodule
  have onLine {i} (hi : i ∈ L) : (W i).toSubmodule = (T i).toSubmodule.map e.toLinearMap := by
    simp only [W, rotatedKillingCartans, ite_eq_left hi]
    rfl
  have offLine {i} (hi : i ∉ L) : W i = T i := by
    simp only [W, rotatedKillingCartans, ite_eq_right hi]
  have inside {i} (hi : i ∈ L) : (W i).toSubmodule ≤ B := by
    rw [onLine hi]
    change (T i).toSubmodule.map e.toLinearMap ≤ ⨆ j : L, (T j.val).toSubmodule
    rw [← normalizes]
    exact Submodule.map_mono (le_iSup (fun j : L => (T j.val).toSubmodule) ⟨i, hi⟩)
  have outside {j} (hj : j ∉ L) (y : K) (hy : y ∈ T j) :
      B ≤ LinearMap.ker ((killingForm ℝ K).flip y) := by
    apply iSup_le
    intro i x hx
    have hne : i.val ≠ j := fun h => hj (h ▸ i.property)
    exact hT.2.1 hne x hx y hy
  have full := killingCartanOD_map e T hT
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ L
    · simpa only [rotatedKillingCartans, ite_eq_left hi] using full.1 i
    · simpa only [rotatedKillingCartans, ite_eq_right hi] using hT.1 i
  · intro i j hij x hx y hy
    change x ∈ W i at hx
    change y ∈ W j at hy
    by_cases hi : i ∈ L <;> by_cases hj : j ∈ L
    · apply full.2.1 hij x _ y _
      · simpa only [W, rotatedKillingCartans, ite_eq_left hi] using hx
      · simpa only [W, rotatedKillingCartans, ite_eq_left hj] using hy
    · rw [offLine hj] at hy
      exact outside hj y hy (inside hi hx)
    · rw [offLine hi] at hx
      exact (LieModule.traceForm_comm ℝ K K x y).trans (outside hi x hx (inside hj hy))
    · rw [offLine hi] at hx
      rw [offLine hj] at hy
      exact hT.2.1 hij x hx y hy
  · have line : B ≤ ⨆ i, (W i).toSubmodule := by
      change (⨆ i : L, (T i.val).toSubmodule) ≤ _
      rw [← normalizes, Submodule.map_iSup]
      exact iSup_le fun i => (onLine i.property).symm.le.trans (le_iSup (fun j => (W j).toSubmodule) i.val)
    have spans : (⨆ i, (W i).toSubmodule) = ⊤ := by
      apply top_unique
      rw [← hT.2.2.submodule_iSup_eq_top]
      apply iSup_le
      intro i
      by_cases hi : i ∈ L
      · exact (le_iSup (fun j : L => (T j.val).toSubmodule) ⟨i, hi⟩).trans line
      · simpa only [offLine hi] using le_iSup (fun j => (W j).toSubmodule) i
    let f := DirectSum.coeLinearMap (fun i => (W i).toSubmodule)
    have onto : Function.Surjective f := LinearMap.range_eq_top.mp (DirectSum.range_coeLinearMap.trans spans)
    have dim : Module.finrank ℝ (DirectSum ι fun i => ↥(W i).toSubmodule) = Module.finrank ℝ K := by
      have orig := (LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun i => (T i).toSubmodule)) hT.2.2).finrank_eq
      rw [Module.finrank_directSum] at orig ⊢
      rw [← orig]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ L
      · rw [onLine hi]
        exact (e.toLinearEquiv.submoduleMap (T i).toSubmodule).finrank_eq.symm
      · rw [offLine hi]
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mpr onto, onto⟩

end

end ThirteenPlanes.Cartan
