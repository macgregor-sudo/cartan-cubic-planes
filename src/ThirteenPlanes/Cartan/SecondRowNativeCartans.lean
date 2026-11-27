module

public import ThirteenPlanes.Cartan.SecondRowCartanExtension
public import ThirteenPlanes.Cartan.ComplexCartan
public import ThirteenPlanes.Cartan.ClassicalQuaternionicObstruction
public import ThirteenPlanes.Cartan.AlbertDerivationComplex

@[expose] public section

/-! The dimensions and lifted Cartans for the complex, quaternionic and Albert operators. -/

namespace ThirteenPlanes.Cartan

noncomputable section

section FrameType

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]

theorem representedCartan_dimensions_fromFrameType (M : TraceJordanData J)
    (K : Submodule ℝ (SkewOperator J)) (hK : K ≤ M.skewDerivations) (T : Submodule ℝ K)
    {rank : ℕ} {κ : ℝ}
    (h : IsFrameType (T.map (M.restrictOperators K hK).toLinearMap) rank κ) :
    Module.finrank ℝ T = rank ∧ Module.finrank ℝ (representedFixedPlane M T) = 2 := by
  let f := M.restrictOperators K hK
  refine ⟨(Submodule.equivMapOfInjective f.toLinearMap f.injective T).finrank_eq.trans h.2.1, ?_⟩
  change Module.finrank ℝ (M.fixedTraceless (T.map K.subtype)) = 2
  rw [M.fixedTraceless_eq_fixedSpace K hK]
  exact h.2.2.1

end FrameType

/-- Frame type for all compact Albert Cartans on the actual operator representation. -/
def AlbertCartansFrameType : Prop :=
  ∀ T : Submodule ℝ albertJordan.skewDerivations, IsRepresentedOperatorCartan T →
    IsFrameType (T.map albertJordan.restrictDerivation) 4 (1 / 6)

theorem complex_representedCartan_frameType (T : Submodule ℝ complexOperatorAlgebra)
    (h : IsRepresentedOperatorCartan T) :
    IsFrameType
      (T.map (complexJordan.restrictOperators complexOperatorAlgebra complexOperatorAlgebra_le).toLinearMap)
      2 (1 / 3) :=
  complexOperatorCartan_frameType T ⟨h.commutes, fun D hD => (h D).mp hD⟩

theorem quaternion_representedCartan_frameType (T : Submodule ℝ quaternionOperatorAlgebra)
    (h : IsRepresentedOperatorCartan T) :
    IsFrameType (T.map quaternionRestrictOperators.toLinearMap) 3 (1 / 4) :=
  quaternionicOperatorCartan_frameType T ⟨h.commutes, fun D hD => (h D).mp hD⟩

theorem complex_representedCartan_dimensions (T : Submodule ℝ complexOperatorAlgebra)
    (h : IsRepresentedOperatorCartan T) :
    Module.finrank ℝ T = 2 ∧ Module.finrank ℝ (representedFixedPlane complexJordan T) = 2 :=
  representedCartan_dimensions_fromFrameType complexJordan complexOperatorAlgebra
    complexOperatorAlgebra_le T (complex_representedCartan_frameType T h)

theorem quaternion_representedCartan_dimensions (T : Submodule ℝ quaternionOperatorAlgebra)
    (h : IsRepresentedOperatorCartan T) :
    Module.finrank ℝ T = 3 ∧ Module.finrank ℝ (representedFixedPlane quaternionJordan T) = 2 :=
  representedCartan_dimensions_fromFrameType quaternionJordan quaternionOperatorAlgebra
    quaternionOperatorAlgebra_le T (quaternion_representedCartan_frameType T h)

theorem albert_representedCartan_dimensions (hQuoted : AlbertCartansFrameType)
    (T : Submodule ℝ albertJordan.skewDerivations) (h : IsRepresentedOperatorCartan T) :
    Module.finrank ℝ T = 4 ∧ Module.finrank ℝ (representedFixedPlane albertJordan T) = 2 :=
  representedCartan_dimensions_fromFrameType albertJordan albertJordan.skewDerivations
    le_rfl T (hQuoted T h)

theorem complex_secondRowCartanExtension (T : Submodule ℝ complexOperatorAlgebra)
    (h : IsRepresentedOperatorCartan T) :
    SecondRowCartanExtension complexJordan complexOperatorAlgebra T 2 := by
  obtain ⟨hr, hp⟩ := complex_representedCartan_dimensions T h
  obtain ⟨hc, hm, ht, _⟩ := complex_secondRow_centralizer T h.commutes h.selfCent hp
  exact secondRowCartanExtension_of_centralizer complexJordan T hr hp hc hm ht

theorem quaternion_secondRowCartanExtension (T : Submodule ℝ quaternionOperatorAlgebra)
    (h : IsRepresentedOperatorCartan T) :
    SecondRowCartanExtension quaternionJordan quaternionOperatorAlgebra T 3 := by
  obtain ⟨hr, hp⟩ := quaternion_representedCartan_dimensions T h
  obtain ⟨hc, hm, ht, _⟩ := quaternion_secondRow_centralizer T h.commutes h.selfCent hp
  exact secondRowCartanExtension_of_centralizer quaternionJordan T hr hp hc hm ht

theorem albert_secondRowCartanExtension (hQuoted : AlbertCartansFrameType)
    (T : Submodule ℝ albertJordan.skewDerivations) (h : IsRepresentedOperatorCartan T) :
    SecondRowCartanExtension albertJordan albertJordan.skewDerivations T 4 := by
  obtain ⟨hr, hp⟩ := albert_representedCartan_dimensions hQuoted T h
  obtain ⟨hc, hm, ht, _⟩ := albert_secondRow_centralizer T h.commutes h.selfCent hp
  exact secondRowCartanExtension_of_centralizer albertJordan T hr hp hc hm ht

theorem complex_secondRow_k_finrank : Module.finrank ℝ complexOperatorAlgebra = 8 := by
  rw [complexOperatorAlgebra, LinearMap.finrank_range_of_inj complexCommutatorLinear_injective,
    ← complexTraceToSkewEquiv.finrank_eq, fourPlane_dimension]

theorem quaternion_secondRow_k_finrank : Module.finrank ℝ quaternionOperatorAlgebra = 21 :=
  compactSp3Operators.finrank_eq.symm.trans compactSp3_finrank

theorem albert_secondRow_k_finrank : Module.finrank ℝ albertJordan.skewDerivations = 52 :=
  nativeAlbertDerivationSkewEquiv.finrank_eq.symm.trans nativeAlbertDerivations_finrank

/-- The actual row has the two dimensions of its real and imaginary coordinate summands. -/
theorem secondRowSpace_finrank {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]
    (M : TraceJordanData J) (K : Submodule ℝ (SkewOperator J)) :
    Module.finrank ℝ (secondRowSpace M K) = Module.finrank ℝ K + Module.finrank ℝ M.traceFree := by
  let b := (stdOrthonormalBasis ℝ K).toBasis.prod (stdOrthonormalBasis ℝ M.traceFree).toBasis
  have h := Module.finrank_eq_card_basis b
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  exact (secondRowCoordinates M K).finrank_eq.symm.trans h

theorem complex_secondRow_g_finrank :
    Module.finrank ℝ (secondRowSpace complexJordan complexOperatorAlgebra) = 16 := by
  rw [secondRowSpace_finrank, complex_secondRow_k_finrank, complexTraceEquiv.finrank_eq,
    fourPlane_dimension]

theorem quaternion_secondRow_g_finrank :
    Module.finrank ℝ (secondRowSpace quaternionJordan quaternionOperatorAlgebra) = 35 := by
  rw [secondRowSpace_finrank, quaternion_secondRow_k_finrank, quaternionTraceFree_finrank]

theorem albert_secondRow_g_finrank :
    Module.finrank ℝ (secondRowSpace albertJordan albertJordan.skewDerivations) = 78 := by
  rw [secondRowSpace_finrank, albert_secondRow_k_finrank, albertTraceFree_finrank]

end
end ThirteenPlanes.Cartan
