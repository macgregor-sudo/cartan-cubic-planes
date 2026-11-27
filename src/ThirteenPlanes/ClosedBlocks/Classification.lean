module

public import ThirteenPlanes.ClosedBlocks.ModelClassification
public import ThirteenPlanes.ClosedBlocks.RealTraceHarmonic
public import ThirteenPlanes.ClosedBlocks.TwoFivesTransport
public import ThirteenPlanes.RealDerivations.Eigenspace
public import ThirteenPlanes.RealWindow.Normalize

@[expose] public section

set_option backward.privateInPublic true

/-! The closed-block exclusions and classifications on their actual models. -/

namespace ThirteenPlanes.ClosedBlocks

open RoundCubics Peirce

/-- Two orthogonal embedded real Cartan five-spaces cannot occur in the Albert model. -/
theorem nativeNoTwoFives : NativeNoTwoFives :=
  nativeNoTwoFives_of_normalization_and_derivation_bound
    (fun _ closed I hc => nativeRealBlock_to_standard closed I hc)
    RealDerivations.realTraceDerivation_gram_eigenspace_finrank_le_two


private theorem actualRealBlock_harmonic {U : Submodule ℝ NativeTraceless}
    (I : U ≃ₗᵢ[ℝ] RealTracelessSymmetric3)
    (hc : nativeEqualCubic.pullback (W := ↥U) U.subtype =
      (Real.sqrt 6)⁻¹ • realCartanCubic.pullback (W := ↥U) I.toLinearMap) :
    (nativeEqualCubic.pullback (W := ↥U) U.subtype).TraceFree ∧ Module.finrank ℝ U = 5 := by
  constructor
  · rw [hc]
    have hs : (Real.sqrt 6)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    have hh := @traceFree_pullback_iff ↥U ↥RealTracelessSymmetric3
      inferInstance (Submodule.innerProductSpace U) inferInstance
      inferInstance (inferInstance : InnerProductSpace ℝ ↥RealTracelessSymmetric3) realCartanCubic I
    exact (traceFree_smul_iff _ hs).mpr (hh.mpr realCartanCubic_traceFree)
  · rw [I.toLinearEquiv.finrank_eq, ← realCartanEquiv.finrank_eq]
    norm_num [Module.finrank_prod]

/-- Two orthogonal copies of the real trace cubic cannot be embedded as closed blocks in Albert. -/
theorem noTwoOrthogonalRealQutrits {U S : Submodule ℝ NativeTraceless}
    (hu : IsClosedPiece nativeEqualCubic U) (hs : IsClosedPiece nativeEqualCubic S) (ho : U.IsOrtho S)
    (I : U ≃ₗᵢ[ℝ] RealTracelessSymmetric3) (J : S ≃ₗᵢ[ℝ] RealTracelessSymmetric3)
    (hI : nativeEqualCubic.pullback (W := ↥U) U.subtype =
      (Real.sqrt 6)⁻¹ • realCartanCubic.pullback (W := ↥U) I.toLinearMap)
    (hJ : nativeEqualCubic.pullback (W := ↥S) S.subtype =
      (Real.sqrt 6)⁻¹ • realCartanCubic.pullback (W := ↥S) J.toLinearMap) :
    False := by
  obtain ⟨htU, hdU⟩ := actualRealBlock_harmonic I hI
  obtain ⟨htS, hdS⟩ := actualRealBlock_harmonic J hJ
  exact nativeNoTwoFives U S hu hs ho htU htS hdU hdS

/-- A proper closed Albert decomposition contains no real or quaternionic block. -/
theorem noRealOrQuaternionicBlock {ι : Type*} [Fintype ι]
    (d : Decomposition nativeEqualCubic ι) (proper : 1 < Fintype.card ι) (i : ι) :
    Module.finrank ℝ (d.piece i) ≠ 5 ∧ Module.finrank ℝ (d.piece i) ≠ 14 :=
  noRealOrQuaternionicBlock_of_noTwoFives nativeNoTwoFives d proper i

/-- The exhaustive closed-block classification for the four Hermitian trace models. -/
theorem classifyHermitianBlockDecompositions : HermitianBlockClassification :=
  classifyHermitianBlockDecompositions_of_noTwoFives nativeNoTwoFives

/-- Every proper harmonic round decomposition is four planes, thirteen planes, or an octet and nine planes. -/
theorem classifyHarmonicRoundDecompositions
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {h : SymmetricCubic V} {c : ℝ} {ι : Type*} [Fintype ι]
    (d : Decomposition h ι) (round : IsRound h c) (tf : h.TraceFree) (proper : 1 < Fintype.card ι) :
    HarmonicBlockDecompositionPattern c d :=
  classifyHarmonicRoundDecompositions_of_noTwoFives nativeNoTwoFives d round tf proper

end ThirteenPlanes.ClosedBlocks
