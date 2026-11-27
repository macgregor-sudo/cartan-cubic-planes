module

public import ThirteenPlanes.ClosedBlocks.HarmonicPatterns

@[expose] public section

/-! Concrete raw-trace versions of the closed decomposition classification. -/

namespace ThirteenPlanes.ClosedBlocks

open RoundCubics Peirce

noncomputable section

abbrev realTraceCubic : SymmetricCubic RealTracelessSymmetric3 :=
  (Real.sqrt 6)⁻¹ • realCartanCubic

/-- Closed decompositions of the four actual Hermitian trace cubics, with
explicit realizations for the complex and Albert cases. -/
def HermitianBlockClassification : Prop :=
    (∀ {ι : Type*} [Fintype ι] (d : Decomposition realTraceCubic ι),
      1 < Fintype.card ι → (∀ i, ModelPieceDimension (Module.finrank ℝ (d.piece i))) → False) ∧
    ((∀ {ι : Type*} [Fintype ι] (d : Decomposition matrixEqualCubic ι),
      1 < Fintype.card ι → (∀ i, ModelPieceDimension (Module.finrank ℝ (d.piece i))) →
      Fintype.card ι = 4 ∧ ∀ i, Module.finrank ℝ (d.piece i) = 2) ∧
      ∃ d : Decomposition matrixEqualCubic (Fin 4), ∀ i, Module.finrank ℝ (d.piece i) = 2) ∧
    (∀ {ι : Type*} [Fintype ι] (d : Decomposition QuaternionicMUB.quaternionTraceCubic ι),
      1 < Fintype.card ι → (∀ i, ModelPieceDimension (Module.finrank ℝ (d.piece i))) → False) ∧
    ((∀ {ι : Type*} [Fintype ι] (d : Decomposition nativeEqualCubic ι), 1 < Fintype.card ι →
      (Fintype.card ι = 13 ∧ ∀ i, Module.finrank ℝ (d.piece i) = 2) ∨
      (Fintype.card ι = 10 ∧ ∃ i, Module.finrank ℝ (d.piece i) = 8 ∧
        (∀ j, j ≠ i → Module.finrank ℝ (d.piece j) = 2) ∧
        ∃ I : d.piece i ≃ₗᵢ[ℝ] TracelessHermitian3,
          nativeEqualCubic.pullback (W := ↥(d.piece i)) (d.piece i).subtype =
            matrixEqualCubic.pullback (W := ↥(d.piece i)) I.toLinearMap)) ∧
      (∃ d : Decomposition nativeEqualCubic (Fin 13), ∀ i, Module.finrank ℝ (d.piece i) = 2) ∧
      (∃ d : Decomposition nativeEqualCubic (Fin 10),
        Module.finrank ℝ (d.piece 0) = 8 ∧
        (∀ i : Fin 10, i ≠ 0 → Module.finrank ℝ (d.piece i) = 2) ∧
        ∃ I : d.piece 0 ≃ₗᵢ[ℝ] TracelessHermitian3,
          nativeEqualCubic.pullback (W := ↥(d.piece 0)) (d.piece 0).subtype =
            matrixEqualCubic.pullback (W := ↥(d.piece 0)) I.toLinearMap))

theorem classifyHermitianBlockDecompositions_of_noTwoFives (hno : NativeNoTwoFives) :
    HermitianBlockClassification := by
  unfold HermitianBlockClassification
  have hp : Real.sqrt 6 ≠ 0 := by positivity
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ⟨?_, exists_nativeAlbert_thirteen_plane_decomposition, complementsOfOctet.{0}.2.2⟩⟩
  · intro ι _ d hproper hd
    let d' : Decomposition realCartanCubic ι :=
      ⟨d.piece, d.nonzero, d.orthogonal, d.exhaustive, fun i =>
        (isClosedPiece_smul_iff (inv_ne_zero hp) _).mp (d.closed i)⟩
    exact realModel_no_proper_closedBlocks d' hproper hd
  · intro ι _ d hproper hd
    exact complexModel_closedBlocks (d.smul hp) hproper hd
  · obtain ⟨d, h⟩ := exists_complex_four_plane_decomposition
    let d' : Decomposition matrixEqualCubic (Fin 4) :=
      ⟨d.piece, d.nonzero, d.orthogonal, d.exhaustive, fun i =>
        (isClosedPiece_smul_iff hp _).mp (d.closed i)⟩
    exact ⟨d', h⟩
  · intro ι _ d hproper hd
    exact quaternionicModel_no_proper_closedBlocks (d.smul hp) hproper hd
  · intro ι _ d hproper
    exact nativeModel_closedBlocks_of_noTwoFives hno d hproper

end

end ThirteenPlanes.ClosedBlocks
