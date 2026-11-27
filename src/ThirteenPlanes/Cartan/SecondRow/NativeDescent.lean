/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.SecondRow.Descent
public import ThirteenPlanes.Cartan.SecondRowNativeCartans

@[expose] public section

set_option backward.privateInPublic true

/-! Native complex, quaternionic and Albert Cartan-decomposition correspondences. -/

namespace ThirteenPlanes.Cartan

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J))

theorem maximalRealCartan_iff_represented (T : Submodule ℝ K) :
    MaximalCommutativeSubspace (RealOperatorCommutative K) T ↔ IsRepresentedOperatorCartan T := by
  rw [isRepresentedOperatorCartan_iff_maximal]
  exact ⟨fun h => ⟨h.1, fun U hTU hU => (h.2 U hTU hU).ge⟩,
    fun h => ⟨h.1, fun U hTU hU => le_antisymm hTU (h.2 U hTU hU)⟩⟩

theorem maximalSecondRowCartan_iff_represented (C : Submodule ℝ (secondRowSpace M K)) :
    MaximalCommutativeSubspace (SecondRowOperatorCommutative M K) C ↔ IsSecondRowOperatorCartan M K C := by
  rw [IsSecondRowOperatorCartan, isOperatorCartanFor_iff_maximal]
  exact ⟨fun h => ⟨h.1, fun U hCU hU => (h.2 U hCU hU).ge⟩,
    fun h => ⟨h.1, fun U hCU hU => le_antisymm hCU (h.2 U hCU hU)⟩⟩

variable [FiniteDimensional ℝ J]

/-- The forward map uses the actual second-row operators and the inverse intersects each
individually stable Cartan with the fixed real algebra. -/
def SecondRowODCorrespondence (m : ℕ) : Prop :=
  ∃ e : {T : Fin m → Submodule ℝ K // RealOperatorCartanOD K T} ≃
      {C : Fin m → Submodule ℝ (secondRowSpace M K) // StableSecondRowCartanOD M K C},
    (∀ T i, (e T).val i = secondRowPieceInSpace M (T.val i)) ∧
    (∀ C i, (e.symm C).val i = secondRowRealIntersection M K (C.val i))

private theorem correspondence_of_extensions {m rank : ℕ} (dimension : Module.finrank ℝ K = m * rank)
    (realRank : ∀ T : Submodule ℝ K, IsRepresentedOperatorCartan T → Module.finrank ℝ T = rank)
    (ext : ∀ T : Submodule ℝ K, IsRepresentedOperatorCartan T → SecondRowCartanExtension M K T rank)
    (split : ∀ T : Fin m → Submodule ℝ K, RealOperatorCartanOD K T → SecondRowSplitting M T rank) :
    SecondRowODCorrespondence M K m := by
  apply secondRowCartanOD_equivalence M K dimension
    (fun T h => realRank T ((maximalRealCartan_iff_represented K T).mp h)) _ split
  intro T h
  have E := ext T ((maximalRealCartan_iff_represented K T).mp h)
  refine ⟨(maximalSecondRowCartan_iff_represented M K _).mpr E.isCartan, E.stable, ?_⟩
  intro C hC contains
  exact E.unique C ((maximalSecondRowCartan_iff_represented M K C).mp hC) contains

theorem complex_secondRowODCorrespondence : SecondRowODCorrespondence complexJordan complexOperatorAlgebra 4 :=
  correspondence_of_extensions complexJordan complexOperatorAlgebra (rank := 2) complex_secondRow_k_finrank
    (fun T h => (complex_representedCartan_dimensions T h).1) complex_secondRowCartanExtension
    (fun T h => complex_secondRow_splitting T h.orthogonalSplit
      (fun i => complex_representedCartan_frameType (T i)
        ((maximalRealCartan_iff_represented complexOperatorAlgebra (T i)).mp (h.cartan i))))

theorem quaternion_secondRowODCorrespondence : SecondRowODCorrespondence quaternionJordan quaternionOperatorAlgebra 7 :=
  correspondence_of_extensions quaternionJordan quaternionOperatorAlgebra (rank := 3) quaternion_secondRow_k_finrank
    (fun T h => (quaternion_representedCartan_dimensions T h).1) quaternion_secondRowCartanExtension
    (fun T h => quaternion_secondRow_splitting T h.orthogonalSplit
      (fun i => quaternion_representedCartan_frameType (T i)
        ((maximalRealCartan_iff_represented quaternionOperatorAlgebra (T i)).mp (h.cartan i))))

theorem albert_secondRowODCorrespondence (tori : AlbertCartansFrameType) :
    SecondRowODCorrespondence albertJordan albertJordan.skewDerivations 13 :=
  correspondence_of_extensions albertJordan albertJordan.skewDerivations (rank := 4) albert_secondRow_k_finrank
    (fun T h => (albert_representedCartan_dimensions tori T h).1) (albert_secondRowCartanExtension tori)
    (fun T h => albert_secondRow_splitting T h.orthogonalSplit
      (fun i => tori (T i) ((maximalRealCartan_iff_represented albertJordan.skewDerivations (T i)).mp (h.cartan i))))

end

end ThirteenPlanes.Cartan
