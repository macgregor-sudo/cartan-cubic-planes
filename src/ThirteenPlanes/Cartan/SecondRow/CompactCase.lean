/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.SecondRow.LieBijection
public import ThirteenPlanes.Cartan.SecondRowLieMetricComparison

@[expose] public section

set_option backward.privateInPublic true

/-! The compact Lie-theoretic conclusions of the second-row corollary. -/

namespace ThirteenPlanes.Cartan

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]
  {M : TraceJordanData J} {K : Submodule ℝ (SkewOperator J)} (H : SecondRowCompactRealization M K)

/-- The fixed algebra, ranks, unique Cartan extension, and labelled OD bijection for one row. -/
structure SecondRowLieCase (rank : ℕ) (ι : Type*) [DecidableEq ι] : Prop where
  compact : CompactKilling H.operators
  conjugation : ∃ σ : H.operators ≃ₗ⁅ℝ⁆ H.operators, (∀ X, σ X = H.theta X) ∧
    Function.Involutive σ ∧ ∀ X : H.operators, σ X = X ↔
      ∃ D : K, X = H.coordinates (secondRowRealInclusion M K D)
  ambientRank : ∀ C : LieSubalgebra ℝ H.operators, C.IsCartanSubalgebra → Module.finrank ℝ C = rank + 2
  extension : ∀ A : LieSubalgebra ℝ H.realLie, A.IsCartanSubalgebra →
    ∃ B : LieSubalgebra ℝ H.operators, B.IsCartanSubalgebra ∧
      B.toSubmodule = (secondRowPieceInSpace M (A.toSubmodule.comap H.realCoordinates.toLinearMap)).map H.coordinates.toLinearMap ∧
      Module.finrank ℝ B = rank + 2 ∧ B.toSubmodule.map H.theta.toLinearMap = B.toSubmodule ∧
      (∀ X ∈ A, (X : H.realLie).val ∈ B) ∧
      ∀ C : LieSubalgebra ℝ H.operators, C.IsCartanSubalgebra → (∀ X ∈ A, (X : H.realLie).val ∈ C) → C = B
  correspondence : SecondRowLieODCorrespondence H ι

omit [FiniteDimensional ℝ J] in
private theorem secondRow_lie_involution :
    ∃ σ : H.operators ≃ₗ⁅ℝ⁆ H.operators, (∀ X, σ X = H.theta X) ∧
      Function.Involutive σ ∧ ∀ X : H.operators, σ X = X ↔ ∃ D : K, X = H.coordinates (secondRowRealInclusion M K D) := by
  let σ := secondRowLieTheta M K H.operators H.carrier_eq
  have theta (X : secondRowSpace M K) : σ (H.coordinates X) = H.coordinates (secondRowTheta M K X) :=
    secondRowLieTheta_onSpace M K H.operators H.carrier_eq X
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro X
    obtain ⟨Y, rfl⟩ := H.coordinates.surjective X
    exact (theta Y).trans (H.theta_coordinates Y).symm
  · intro X
    obtain ⟨Y, rfl⟩ := H.coordinates.surjective X
    rw [theta, theta, secondRowTheta_involutive M K Y]
  · intro X
    obtain ⟨Y, rfl⟩ := H.coordinates.surjective X
    rw [theta, H.coordinates.injective.eq_iff, secondRowTheta_fixed_iff_real]
    exact ⟨fun ⟨D, h⟩ => ⟨D, congrArg H.coordinates h⟩, fun ⟨D, h⟩ => ⟨D, H.coordinates.injective h⟩⟩

set_option maxHeartbeats 1000000 in
/-- Transport the computed centralizer and native decomposition correspondence to compact
Lie subalgebras. Equal Cartan dimensions and proportional invariant metrics are used here. -/
theorem secondRowLieCase_of_native {rank : ℕ} {ι : Type*} [DecidableEq ι]
    (ext : ∀ T : Submodule ℝ K, IsRepresentedOperatorCartan T → SecondRowCartanExtension M K T rank)
    (uniform : ∀ C D : LieSubalgebra ℝ H.operators, C.IsCartanSubalgebra → D.IsCartanSubalgebra →
      Module.finrank ℝ C = Module.finrank ℝ D)
    (indexed : (∀ C, IsSecondRowOperatorCartan M K C → Module.finrank ℝ C = rank + 2) →
      IndexedSecondRowODCorrespondence M K ι)
    (metric : ∃ a : ℝ, 0 < a ∧ ∀ X Y : H.operators,
      (complexTraceForm X.val Y.val).re = a * (-killingForm ℝ H.operators X Y)) : SecondRowLieCase H rank ι := by
  obtain ⟨T, hT⟩ := exists_representedOperatorCartan K
  have ambient := H.ambient_rank_of_conjugacy uniform T (ext T hT)
  have opRank (C) (hC : IsSecondRowOperatorCartan M K C) : Module.finrank ℝ C = rank + 2 := by
    have hc := H.operatorCartanSubalgebra_spec C hC
    exact hc.2.symm.trans (ambient _ hc.1)
  refine ⟨H.compact, secondRow_lie_involution H, ambient, ?_, secondRowLieODCorrespondence_of_operators H (indexed opRank) metric⟩
  intro A hA
  let U := A.toSubmodule.comap H.realCoordinates.toLinearMap
  have hU := ext U ((H.realOperatorCartan_iff A).mpr hA)
  let B := H.liftCartan U hU
  obtain ⟨hB, dim, stable, contains, unique⟩ := H.liftCartan_spec U hU
  refine ⟨B, hB, rfl, dim, stable, ?_, ?_⟩
  · intro X hX
    obtain ⟨D, rfl⟩ := H.realCoordinates.surjective X
    exact contains ⟨D, hX⟩
  · intro C hC hContains
    exact unique C hC fun D => hContains (H.realCoordinates D.val) D.property

end
end ThirteenPlanes.Cartan
