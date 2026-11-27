/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.SecondRow.LieDecompositions
public import ThirteenPlanes.Cartan.SecondRowOrdinaryCartans

@[expose] public section

set_option backward.privateInPublic true

/-! Both sides of the second-row correspondence as families of actual Lie subalgebras. -/

namespace ThirteenPlanes.Cartan

noncomputable section

variable {ι : Type*} [DecidableEq ι]
  {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]
  {M : TraceJordanData J} {K : Submodule ℝ (SkewOperator J)} (H : SecondRowCompactRealization M K)

/-- Definition 7 uses the negative operator trace on the represented real algebra. -/
def SecondRowRealLieOD (A : ι → LieSubalgebra ℝ H.realLie) : Prop :=
  (∀ i, (A i).IsCartanSubalgebra) ∧
    OrthogonalSplit (fun i => (A i).toSubmodule.comap H.realCoordinates.toLinearMap)

/-- Orthogonality for the ambient Killing form, with each Cartan individually fixed by conjugation. -/
def SecondRowStableLieOD (B : ι → LieSubalgebra ℝ H.operators) : Prop :=
  IsKillingCartanOD B ∧ ∀ i, (B i).toSubmodule.map H.theta.toLinearMap = (B i).toSubmodule

private def realLieFamilies :
    {T : ι → Submodule ℝ K // RealOperatorCartanOD K T} ≃
      {A : ι → LieSubalgebra ℝ H.realLie // SecondRowRealLieOD H A} where
  toFun T := by
    let A i := H.realOperatorCartanSubalgebra (T.val i)
      ((maximalRealCartan_iff_represented _ _).mp (T.property.cartan i))
    have back (i) : (A i).toSubmodule.comap H.realCoordinates.toLinearMap = T.val i :=
      Submodule.comap_map_eq_of_injective H.realCoordinates.injective _
    refine ⟨A, fun i => (H.realOperatorCartan_iff _).mp ?_, ?_⟩
    · rw [back]
      exact (maximalRealCartan_iff_represented K _).mp (T.property.cartan i)
    · exact (funext back).symm ▸ T.property.orthogonalSplit
  invFun A := ⟨fun i => (A.val i).toSubmodule.comap H.realCoordinates.toLinearMap, A.property.2,
    fun i => (maximalRealCartan_iff_represented _ _).mpr ((H.realOperatorCartan_iff _).mpr (A.property.1 i))⟩
  left_inv T := Subtype.ext <| funext fun i => Submodule.comap_map_eq_of_injective H.realCoordinates.injective (T.val i)
  right_inv A := Subtype.ext <| funext fun i => LieSubalgebra.toSubmodule_injective <|
    Submodule.map_comap_eq_of_surjective H.realCoordinates.surjective (A.val i).toSubmodule

private def stableLieFamilies
    (metric : ∀ X Y : secondRowSpace M K, complexTraceForm X.val Y.val = 0 ↔
      killingForm ℝ H.operators (H.coordinates X) (H.coordinates Y) = 0) :
    {P : ι → Submodule ℝ (secondRowSpace M K) // StableSecondRowCartanOD M K P} ≃
      {B : ι → LieSubalgebra ℝ H.operators // SecondRowStableLieOD H B} where
  toFun P := by
    let B i := H.operatorCartanSubalgebra (P.val i)
      ((maximalSecondRowCartan_iff_represented M K _).mp (P.property.cartan i))
    exact ⟨B, (secondRowLieCartanOD_iff H P.val B (fun _ => rfl) metric).mp P.property⟩
  invFun B := by
    let P i := (B.val i).toSubmodule.comap H.coordinates.toLinearMap
    have same (i) : (P i).map H.coordinates.toLinearMap = (B.val i).toSubmodule :=
      Submodule.map_comap_eq_of_surjective H.coordinates.surjective _
    exact ⟨P, (secondRowLieCartanOD_iff H P B.val same metric).mpr B.property⟩
  left_inv P := Subtype.ext <| funext fun i => Submodule.comap_map_eq_of_injective H.coordinates.injective (P.val i)
  right_inv B := Subtype.ext <| funext fun i => LieSubalgebra.toSubmodule_injective <|
    Submodule.map_comap_eq_of_surjective H.coordinates.surjective (B.val i).toSubmodule

/-- The Lie-theoretic bijection and the actual formulas for both directions. -/
def SecondRowLieODCorrespondence (ι : Type*) [DecidableEq ι] : Prop :=
  ∃ e : {A : ι → LieSubalgebra ℝ H.realLie // SecondRowRealLieOD H A} ≃
      {B : ι → LieSubalgebra ℝ H.operators // SecondRowStableLieOD H B},
    (∀ A i, ((e A).val i).toSubmodule =
      (secondRowPieceInSpace M ((A.val i).toSubmodule.comap H.realCoordinates.toLinearMap)).map H.coordinates.toLinearMap) ∧
    (∀ B i, ((e.symm B).val i).toSubmodule =
      (secondRowRealIntersection M K ((B.val i).toSubmodule.comap H.coordinates.toLinearMap)).map H.realCoordinates.toLinearMap)

set_option maxHeartbeats 800000 in
theorem secondRowLieODCorrespondence_of_operators (corr : IndexedSecondRowODCorrespondence M K ι)
    (proportional : ∃ a : ℝ, 0 < a ∧ ∀ X Y : H.operators,
      (complexTraceForm X.val Y.val).re = a * (-killingForm ℝ H.operators X Y)) :
    SecondRowLieODCorrespondence H ι := by
  obtain ⟨f, forward, backward⟩ := corr
  let k := realLieFamilies (ι := ι) H
  let g := stableLieFamilies (ι := ι) H (secondRow_trace_killing_orthogonal H proportional)
  refine ⟨k.symm.trans (f.trans g), ?_, ?_⟩
  · intro A i
    change ((f (k.symm A)).val i).map H.coordinates.toLinearMap = _
    rw [forward]
    rfl
  · intro B i
    change ((f.symm (g.symm B)).val i).map H.realCoordinates.toLinearMap = _
    rw [backward]
    rfl

end
end ThirteenPlanes.Cartan
