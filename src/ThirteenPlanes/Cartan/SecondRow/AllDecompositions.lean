/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.SecondRow.NativeDescent

@[expose] public section

set_option backward.privateInPublic true

/-! The Cartan correspondence for every finite family of individually stable summands. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators

noncomputable section

variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']

/-- In an internal direct sum of equal positive ranks, the ambient dimension determines
the number of summands. -/
theorem card_eq_of_cartan_ranks {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    [Fintype ι] (C : ι → Submodule ℝ V) (internal : DirectSum.IsInternal C)
    {rank m : ℕ} (positive : 0 < rank) (dims : ∀ i, Module.finrank ℝ (C i) = rank)
    (total : Module.finrank ℝ V = m * rank) : Fintype.card ι = m := by
  have (i : ι) : Module.Free ℝ (C i) := Module.Free.of_divisionRing ℝ (C i)
  have (i : ι) : Module.Finite ℝ (C i) := inferInstance
  have h := (LinearEquiv.ofBijective (DirectSum.coeLinearMap C) internal).finrank_eq
  rw [Module.finrank_directSum ℝ (fun i => ↥(C i)), total] at h
  exact Nat.eq_of_mul_eq_mul_right positive (by simpa [dims] using h)

private theorem card_eq_of_independent_spanning_ranks {V : Type*}
    [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V] [Fintype ι]
    (C : ι → Submodule ℝ V) (independent : iSupIndep C) (spans : iSup C = ⊤)
    {rank m : ℕ} (positive : 0 < rank) (dims : ∀ i, Module.finrank ℝ (C i) = rank)
    (total : Module.finrank ℝ V = m * rank) : Fintype.card ι = m :=
  card_eq_of_cartan_ranks C (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (R := ℝ) (M := V) (A := C) independent spans) positive dims total

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J)) [FiniteDimensional ℝ J]

theorem realOperatorCartanOD_reindex (e : ι' ≃ ι) (T : ι → Submodule ℝ K)
    (h : RealOperatorCartanOD K T) : RealOperatorCartanOD K (fun j => T (e j)) := by
  have hds := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top T).mp h.orthogonalSplit.2
  exact ⟨⟨fun _ _ hj => h.orthogonalSplit.1 (e.injective.ne hj),
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨hds.1.comp e.injective, e.iSup_comp.trans hds.2⟩⟩, fun j => h.cartan (e j)⟩

omit [DecidableEq ι] [DecidableEq ι'] [FiniteDimensional ℝ J] in
theorem stableSecondRowCartanOD_reindex (e : ι' ≃ ι) (C : ι → Submodule ℝ (secondRowSpace M K))
    (h : StableSecondRowCartanOD M K C) : StableSecondRowCartanOD M K (fun j => C (e j)) :=
  ⟨fun j => h.cartan (e j), fun j => h.stable (e j), h.independent.comp e.injective,
    e.iSup_comp.trans h.spans, fun i j hij => h.orthogonal (e i) (e j) (e.injective.ne hij)⟩

/-- The bijection retains the labels, for arbitrary finite label types. Its inverse
intersects each summand with the fixed real algebra. -/
def IndexedSecondRowODCorrespondence (ι : Type*) [DecidableEq ι] : Prop :=
  ∃ e : {T : ι → Submodule ℝ K // RealOperatorCartanOD K T} ≃
      {C : ι → Submodule ℝ (secondRowSpace M K) // StableSecondRowCartanOD M K C},
    (∀ T i, (e T).val i = secondRowPieceInSpace M (T.val i)) ∧
    (∀ C i, (e.symm C).val i = secondRowRealIntersection M K (C.val i))

set_option maxHeartbeats 1200000 in
theorem secondRowODCorrespondence_all_indices [Fintype ι] {m rank : ℕ} (positive : 0 < rank)
    (kDimension : Module.finrank ℝ K = m * rank)
    (gDimension : Module.finrank ℝ (secondRowSpace M K) = m * (rank + 2))
    (kRank : ∀ T, MaximalCommutativeSubspace (RealOperatorCommutative K) T → Module.finrank ℝ T = rank)
    (gRank : ∀ C, MaximalCommutativeSubspace (SecondRowOperatorCommutative M K) C →
      Module.finrank ℝ C = rank + 2)
    (finiteCorr : SecondRowODCorrespondence M K m) : IndexedSecondRowODCorrespondence M K ι := by
  obtain ⟨f, lift_eq, meet_eq⟩ := finiteCorr
  let lift (T : ι → Submodule ℝ K) (i : ι) := secondRowPieceInSpace M (T i)
  let meet (C : ι → Submodule ℝ (secondRowSpace M K)) (i : ι) := secondRowRealIntersection M K (C i)
  have forward (T : ι → Submodule ℝ K) (h : RealOperatorCartanOD K T) :
      StableSecondRowCartanOD M K (lift T) := by
    have card := card_eq_of_cartan_ranks T h.orthogonalSplit.2 positive (fun i => kRank _ (h.cartan i)) kDimension
    let e := Fintype.equivFinOfCardEq card
    let A := f ⟨fun j => T (e.symm j), realOperatorCartanOD_reindex K e.symm T h⟩
    have eq : (fun i => A.val (e i)) = lift T := by
      funext i
      simpa only [e.symm_apply_apply] using lift_eq ⟨_, realOperatorCartanOD_reindex K e.symm T h⟩ (e i)
    exact eq ▸ stableSecondRowCartanOD_reindex M K e A.val A.property
  have backward (C : ι → Submodule ℝ (secondRowSpace M K)) (h : StableSecondRowCartanOD M K C) :
      RealOperatorCartanOD K (meet C) := by
    have card := card_eq_of_independent_spanning_ranks (V := ↥(secondRowSpace M K)) C h.independent h.spans
      (by omega : 0 < rank + 2)
      (fun i => gRank _ (h.cartan i)) gDimension
    let e := Fintype.equivFinOfCardEq card
    let B := f.symm ⟨fun j => C (e.symm j), stableSecondRowCartanOD_reindex M K e.symm C h⟩
    have eq : (fun i => B.val (e i)) = meet C := by
      funext i
      simpa only [e.symm_apply_apply] using meet_eq ⟨_, stableSecondRowCartanOD_reindex M K e.symm C h⟩ (e i)
    exact eq ▸ realOperatorCartanOD_reindex K e B.val B.property
  let result : {T : ι → Submodule ℝ K // RealOperatorCartanOD K T} ≃
        {C : ι → Submodule ℝ (secondRowSpace M K) // StableSecondRowCartanOD M K C} :=
    { toFun := fun T => ⟨lift T.val, forward _ T.property⟩
      invFun := fun C => ⟨meet C.val, backward _ C.property⟩
      left_inv := fun T => Subtype.ext (funext fun i => secondRowRealIntersection_piece M K (T.val i))
      right_inv := by
        intro C
        have card := card_eq_of_independent_spanning_ranks (V := ↥(secondRowSpace M K)) C.val
          C.property.independent C.property.spans (by omega : 0 < rank + 2)
          (fun i => gRank _ (C.property.cartan i)) gDimension
        let e := Fintype.equivFinOfCardEq card
        let A : {C : Fin m → Submodule ℝ (secondRowSpace M K) // StableSecondRowCartanOD M K C} :=
          ⟨fun j => C.val (e.symm j), stableSecondRowCartanOD_reindex M K e.symm C.val C.property⟩
        apply Subtype.ext
        funext i
        have h := lift_eq (f.symm A) (e i)
        rw [f.apply_symm_apply, meet_eq] at h
        simpa only [A, e.symm_apply_apply] using h.symm }
  exact ⟨result, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The three represented real algebras admit maximal commuting subspaces, including
when no orthogonal Cartan decomposition is given. -/
theorem exists_representedOperatorCartan : ∃ T : Submodule ℝ K, IsRepresentedOperatorCartan T := by
  have zeroComm : RealOperatorCommutative K ⊥ := by
    intro X Y
    have hX : X.val = 0 := X.property
    rw [hX]
    exact Commute.zero_left _
  obtain ⟨T, _, hT, hMax⟩ := exists_maximal_subspace_with (RealOperatorCommutative K) ⊥ zeroComm
  exact ⟨T, (maximalRealCartan_iff_represented K T).mp ⟨hT, hMax⟩⟩

theorem complex_allSecondRowCartanOD [Fintype ι]
    (rank : ∀ C, IsSecondRowOperatorCartan complexJordan complexOperatorAlgebra C →
      Module.finrank ℝ C = 4) : IndexedSecondRowODCorrespondence complexJordan complexOperatorAlgebra ι :=
  secondRowODCorrespondence_all_indices _ _ (rank := 2) (m := 4) (by decide)
    complex_secondRow_k_finrank complex_secondRow_g_finrank
    (fun T h => (complex_representedCartan_dimensions T
      ((maximalRealCartan_iff_represented _ T).mp h)).1)
    (fun C h => rank C ((maximalSecondRowCartan_iff_represented _ _ C).mp h)) complex_secondRowODCorrespondence

theorem quaternion_allSecondRowCartanOD [Fintype ι]
    (rank : ∀ C, IsSecondRowOperatorCartan quaternionJordan quaternionOperatorAlgebra C →
      Module.finrank ℝ C = 5) : IndexedSecondRowODCorrespondence quaternionJordan quaternionOperatorAlgebra ι :=
  secondRowODCorrespondence_all_indices _ _ (rank := 3) (m := 7) (by decide)
    quaternion_secondRow_k_finrank quaternion_secondRow_g_finrank
    (fun T h => (quaternion_representedCartan_dimensions T
      ((maximalRealCartan_iff_represented _ T).mp h)).1)
    (fun C h => rank C ((maximalSecondRowCartan_iff_represented _ _ C).mp h)) quaternion_secondRowODCorrespondence

theorem albert_allSecondRowCartanOD [Fintype ι] (tori : AlbertCartansFrameType)
    (rank : ∀ C, IsSecondRowOperatorCartan albertJordan albertJordan.skewDerivations C →
      Module.finrank ℝ C = 6) : IndexedSecondRowODCorrespondence albertJordan albertJordan.skewDerivations ι :=
  secondRowODCorrespondence_all_indices _ _ (rank := 4) (m := 13) (by decide)
    albert_secondRow_k_finrank albert_secondRow_g_finrank
    (fun T h => (albert_representedCartan_dimensions tori T
      ((maximalRealCartan_iff_represented _ T).mp h)).1)
    (fun C h => rank C ((maximalSecondRowCartan_iff_represented _ _ C).mp h)) (albert_secondRowODCorrespondence tori)

end
end ThirteenPlanes.Cartan
