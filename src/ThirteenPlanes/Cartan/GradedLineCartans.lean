module

public import ThirteenPlanes.Cartan.GradedLineCartansSupport
public import ThirteenPlanes.Cartan.GradeRealAlbert
public import ThirteenPlanes.Cartan.GradedLineRestrictionNativeCore

@[expose] public section

set_option backward.privateInPublic true

/-! The real derivations of a graded line are the sum of its four native Cartans. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ρ : TernaryAction} (hρ : IsTernaryGrading ρ) (l : SignedPlaneIndex)

private abbrev LinePoints (l : SignedPlaneIndex) := {p : SignedPlaneIndex // signedPointOnLine p l}

private theorem albertComplexLineCartans_map :
    ((⨆ p : LinePoints l, (albertGradingComplexPair hρ p.val).toSubmodule).map albertGradingRep) =
      (albertGradingBasis hρ).lineDerivations (signedProjectiveLine l) := by
  rw [Submodule.map_iSup, (albertGradingBasis hρ).lineDerivations_eq_iSup_gradePairs]
  exact iSup_congr (fun p : LinePoints l => albertComplexGradePair_map hρ p.val)

private theorem albertGradingRep_ofReal_eq_mapC (D : NativeAlbertDerivations) :
    albertGradingRep (LieComplex.ofReal D) = JC.mapC D.val := by
  change (albertDerivationComplexEquiv (LieComplex.ofReal D)).val = _
  rw [albertDerivationComplexEquiv_apply_ofReal, extendAlbertDerivation_val]

/-- In the native real derivation Lie algebra, the line space is the sum of its point Cartans. -/
theorem iSup_realCartan_eq_comap_realLineDerivations :
    (⨆ p : {p : SignedPlaneIndex // signedPointOnLine p l},
      (albertGradingRealCartan hρ p.val).toSubmodule) =
      ((albertGradingBasis hρ).realLineDerivations (signedProjectiveLine l)).comap
        nativeAlbertDerivations.toSubmodule.subtype := by
  change (⨆ p : LinePoints l, (LieComplex.descend (albertGradingComplexPair hρ p.val)).toSubmodule) = _
  rw [LieComplex.iSup_toSubmodule_descend_eq
    (H := fun p : LinePoints l => albertGradingComplexPair hρ p.val)
    (fun p : LinePoints l => albertGradingComplexPair_stable hρ p.val)]
  ext D
  change (LieComplex.ofReal D ∈ ⨆ p : LinePoints l, (albertGradingComplexPair hρ p.val).toSubmodule) ↔
    D.val ∈ (albertGradingBasis hρ).realLineDerivations (signedProjectiveLine l)
  rw [NormalizedTernaryBasis.mem_realLineDerivations, ← albertGradingRep_ofReal_eq_mapC,
    ← albertComplexLineCartans_map hρ l]
  constructor
  · exact Submodule.mem_map_of_mem
  · rintro ⟨X, hX, h⟩
    exact albertGradingRep_injective h ▸ hX

private theorem realLineDerivations_le_native :
    (albertGradingBasis hρ).realLineDerivations (signedProjectiveLine l) ≤
      nativeAlbertDerivations.toSubmodule := by
  intro D hD
  have hC := (albertGradingBasis hρ).lineDerivations_le (signedProjectiveLine l)
    (NormalizedTernaryBasis.mem_realLineDerivations _ _ |>.mp hD)
  change (albertGradingBasis hρ).IsDerivation (JC.mapC D) at hC
  let E : ComplexAlbertDerivations := ⟨JC.mapC D, mem_complexAlbertDerivations.mpr (by
    simpa only [NormalizedTernaryBasis.IsDerivation, albertGradingBasis_product] using hC)⟩
  have hE : (complexDerivationRealPart E).val = D := by
    apply LinearMap.ext
    intro x
    rw [complexDerivationRealPart_apply]
    rfl
  exact hE ▸ (complexDerivationRealPart E).property

/-- As literal real endomorphisms of the full compact Albert algebra, the ambient
line operator space is exactly the sum of its four real point Cartans. -/
theorem realLineDerivations_eq_map_iSup_realCartans :
    (albertGradingBasis hρ).realLineDerivations (signedProjectiveLine l) =
      (⨆ p : {p : SignedPlaneIndex // signedPointOnLine p l},
        (albertGradingRealCartan hρ p.val).toSubmodule).map
        nativeAlbertDerivations.toSubmodule.subtype := by
  rw [iSup_realCartan_eq_comap_realLineDerivations hρ l]
  apply le_antisymm
  · intro D hD
    exact ⟨⟨D, realLineDerivations_le_native hρ l hD⟩, hD, rfl⟩
  · rintro D ⟨E, hE, rfl⟩
    exact hE

end
end ThirteenPlanes.Cartan
