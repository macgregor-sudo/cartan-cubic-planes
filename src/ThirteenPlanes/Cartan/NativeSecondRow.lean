module

public import ThirteenPlanes.Cartan.NativeConclusions
public import ThirteenPlanes.Cartan.ComplexCasimir
public import ThirteenPlanes.Cartan.QuaternionFullCasimir
public import ThirteenPlanes.Cartan.SecondRowFromFrames

@[expose] public section

/-! The second-row centralizers and orthogonal decompositions of the actual native models. -/

namespace ThirteenPlanes.Cartan

open scoped BigOperators RealInnerProductSpace
open RoundCubics QuaternionicMUB

noncomputable section

/-- The verified second-row centralizer statement on the actual compact Albert model. -/
theorem albert_secondRow_centralizer (T : Submodule ℝ albertJordan.skewDerivations)
    (hT : ∀ A B : T, Commute A.val.val.val B.val.val.val)
    (hMax : ∀ D : albertJordan.skewDerivations,
      (∀ H : T, operatorBracket H.val.val.val D.val.val = 0) ↔ D ∈ T)
    (hDim : Module.finrank ℝ (representedFixedPlane albertJordan T) = 2) :
    (∀ X : secondRowSpace albertJordan albertJordan.skewDerivations,
      (∀ H : T, operatorBracket (H.val.val.val.baseChange ℂ) X.val = 0) ↔
        X ∈ secondRowPieceInSpace albertJordan T) ∧
    (∀ X Y, X ∈ secondRowPiece albertJordan T → Y ∈ secondRowPiece albertJordan T → Commute X Y) ∧
    (secondRowPieceInSpace albertJordan T).map (secondRowTheta albertJordan albertJordan.skewDerivations).toLinearMap =
      secondRowPieceInSpace albertJordan T ∧
    (∀ B : Submodule ℝ (secondRowSpace albertJordan albertJordan.skewDerivations),
      (∀ X Y : B, Commute X.val.val Y.val.val) →
      (∀ H : T, secondRowCoordinates albertJordan albertJordan.skewDerivations (H.val, 0) ∈ B) →
      B ≤ secondRowPieceInSpace albertJordan T) :=
  secondRow_centralizer_of_fixedDimension albertJordan albertJordan.skewDerivations le_rfl T
    hT hMax albertJordan_closedPlane_has_frame hDim

/-- The verified second-row centralizer statement on the actual quaternionic model. -/
theorem quaternion_secondRow_centralizer (T : Submodule ℝ quaternionOperatorAlgebra)
    (hT : ∀ A B : T, Commute A.val.val.val B.val.val.val)
    (hMax : ∀ D : quaternionOperatorAlgebra,
      (∀ H : T, operatorBracket H.val.val.val D.val.val = 0) ↔ D ∈ T)
    (hDim : Module.finrank ℝ (representedFixedPlane quaternionJordan T) = 2) :
    (∀ X : secondRowSpace quaternionJordan quaternionOperatorAlgebra,
      (∀ H : T, operatorBracket (H.val.val.val.baseChange ℂ) X.val = 0) ↔
        X ∈ secondRowPieceInSpace quaternionJordan T) ∧
    (∀ X Y, X ∈ secondRowPiece quaternionJordan T → Y ∈ secondRowPiece quaternionJordan T → Commute X Y) ∧
    (secondRowPieceInSpace quaternionJordan T).map (secondRowTheta quaternionJordan quaternionOperatorAlgebra).toLinearMap =
      secondRowPieceInSpace quaternionJordan T ∧
    (∀ B : Submodule ℝ (secondRowSpace quaternionJordan quaternionOperatorAlgebra),
      (∀ X Y : B, Commute X.val.val Y.val.val) →
      (∀ H : T, secondRowCoordinates quaternionJordan quaternionOperatorAlgebra (H.val, 0) ∈ B) →
      B ≤ secondRowPieceInSpace quaternionJordan T) :=
  secondRow_centralizer_of_fixedDimension quaternionJordan quaternionOperatorAlgebra
    quaternionOperatorAlgebra_le T hT hMax quaternion_closedPlane_has_frame hDim

/-- The verified second-row centralizer statement on the actual complex model. -/
theorem complex_secondRow_centralizer (T : Submodule ℝ complexOperatorAlgebra)
    (hT : ∀ A B : T, Commute A.val.val.val B.val.val.val)
    (hMax : ∀ D : complexOperatorAlgebra,
      (∀ H : T, operatorBracket H.val.val.val D.val.val = 0) ↔ D ∈ T)
    (hDim : Module.finrank ℝ (representedFixedPlane complexJordan T) = 2) :
    (∀ X : secondRowSpace complexJordan complexOperatorAlgebra,
      (∀ H : T, operatorBracket (H.val.val.val.baseChange ℂ) X.val = 0) ↔
        X ∈ secondRowPieceInSpace complexJordan T) ∧
    (∀ X Y, X ∈ secondRowPiece complexJordan T → Y ∈ secondRowPiece complexJordan T → Commute X Y) ∧
    (secondRowPieceInSpace complexJordan T).map (secondRowTheta complexJordan complexOperatorAlgebra).toLinearMap =
      secondRowPieceInSpace complexJordan T ∧
    (∀ B : Submodule ℝ (secondRowSpace complexJordan complexOperatorAlgebra),
      (∀ X Y : B, Commute X.val.val Y.val.val) →
      (∀ H : T, secondRowCoordinates complexJordan complexOperatorAlgebra (H.val, 0) ∈ B) →
      B ≤ secondRowPieceInSpace complexJordan T) :=
  secondRow_centralizer_of_fixedDimension complexJordan complexOperatorAlgebra
    complexOperatorAlgebra_le T hT hMax complex_closedPlane_has_frame hDim

/-- The second-row orthogonal splitting on the native compact Albert algebra. -/
theorem albert_secondRow_splitting
    (T : Fin 13 → Submodule ℝ albertJordan.skewDerivations)
    (hT : OrthogonalSplit (E := albertJordan.skewDerivations) T)
    (hType : ∀ i, IsFrameType ((T i).map albertJordan.restrictDerivation) 4 (1 / 6)) :
    SecondRowSplitting albertJordan T 4 :=
  secondRow_of_frameTypeSplitting albertJordan albertJordan.skewDerivations le_rfl T hT
    4 (1 / 6) (Module.finrank ℝ albertDerivationOperators / 26) (by norm_num)
    albertFullCasimir hType (by rw [albertTraceFree_finrank]; decide)
    albertJordan_closedPlane_has_frame albertJordanAction albertJordan_commuting_eq_smul_id

/-- The second-row orthogonal splitting on the native complex commutator algebra. -/
theorem complex_secondRow_splitting
    (T : Fin 4 → Submodule ℝ complexOperatorAlgebra)
    (hT : OrthogonalSplit (E := complexOperatorAlgebra) T)
    (hType : ∀ i, IsFrameType
      ((T i).map (complexJordan.restrictOperators complexOperatorAlgebra complexOperatorAlgebra_le).toLinearMap)
      2 (1 / 3)) :
    SecondRowSplitting complexJordan T 2 :=
  secondRow_of_frameTypeSplitting complexJordan complexOperatorAlgebra complexOperatorAlgebra_le
    T hT 2 (1 / 3) 1 (by norm_num) (by
      change operatorCasimir complexRestrictedOperatorAlgebra = _
      rw [one_smul, complex_full_casimir_eq_id])
    hType (by rw [complexTraceEquiv.finrank_eq, fourPlane_dimension]; decide) complex_closedPlane_has_frame
    complexSU3Action complex_scalar_commutant

/-- The second-row orthogonal splitting on the actual quaternionic commutator algebra. -/
theorem quaternion_secondRow_splitting
    (T : Fin 7 → Submodule ℝ quaternionOperatorAlgebra)
    (hT : OrthogonalSplit (E := quaternionOperatorAlgebra) T)
    (hType : ∀ i, IsFrameType ((T i).map quaternionRestrictOperators.toLinearMap) 3 (1 / 4)) :
    SecondRowSplitting quaternionJordan T 3 :=
  secondRow_of_frameTypeSplitting quaternionJordan quaternionOperatorAlgebra quaternionOperatorAlgebra_le
    T hT 3 (1 / 4) (Module.finrank ℝ quaternionDerivationOperators / 14) (by norm_num)
    quaternionFullCasimir hType (by rw [quaternionTraceFree_finrank]; decide)
    quaternion_closedPlane_has_frame quaternionJordanAction quaternionJordan_commuting_eq_smul_id


end

end ThirteenPlanes.Cartan
