module

public import ThirteenPlanes.Cartan.F4.FrameTransport
public import ThirteenPlanes.Cartan.SecondRowNativeCartans
public import ThirteenPlanes.Cartan.F4.Decomposition

@[expose] public section

/-! The ordinary native Lie Cartan and the two exact operator interfaces for F₄. -/

namespace ThirteenPlanes.Cartan

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The native Lie subalgebra underlying a Cartan of the literal skew derivations. -/
def nativeAlbertCartanOfRepresented (T : Submodule ℝ albertJordan.skewDerivations)
    (hT : IsRepresentedOperatorCartan T) : LieSubalgebra ℝ NativeAlbertDerivations where
  toSubmodule := T.comap nativeAlbertDerivationSkewEquiv.toLinearMap
  lie_mem' := by
    intro X Y hX hY
    have hc := hT.commutes ⟨nativeAlbertDerivationSkewEquiv X, hX⟩
      ⟨nativeAlbertDerivationSkewEquiv Y, hY⟩
    have hbr : ⁅X, Y⁆ = 0 := Subtype.ext (sub_eq_zero.mpr hc.eq)
    change nativeAlbertDerivationSkewEquiv ⁅X, Y⁆ ∈ T
    rw [hbr]
    exact T.zero_mem

theorem nativeAlbertCartanOfRepresented_isCartan (compact : CompactKilling NativeAlbertDerivations)
    (T : Submodule ℝ albertJordan.skewDerivations) (hT : IsRepresentedOperatorCartan T) :
    (nativeAlbertCartanOfRepresented T hT).IsCartanSubalgebra := by
  apply (compactCartan_iff_cartan compact _).mp
  intro X
  have hX := hT (nativeAlbertDerivationSkewEquiv X)
  constructor
  · intro hc
    apply hX.mp
    intro Y
    let Y₀ := nativeAlbertDerivationSkewEquiv.symm Y.val
    have hY₀ : Y₀ ∈ nativeAlbertCartanOfRepresented T hT := by
      change nativeAlbertDerivationSkewEquiv (nativeAlbertDerivationSkewEquiv.symm Y.val) ∈ T
      rw [LinearEquiv.apply_symm_apply]
      exact Y.property
    change Commute X.val Y₀.val
    exact sub_eq_zero.mp (congrArg Subtype.val (hc Y₀ hY₀))
  · intro hX' Y hY
    have hc := hX.mpr hX' ⟨nativeAlbertDerivationSkewEquiv Y, hY⟩
    exact Subtype.ext (sub_eq_zero.mpr hc.eq)

theorem nativeAlbertCartanOfRepresented_restricted_eq
    (T : Submodule ℝ albertJordan.skewDerivations) (hT : IsRepresentedOperatorCartan T) :
    nativeAlbertRestrictedCartan (nativeAlbertCartanOfRepresented T hT) =
      T.map albertJordan.restrictDerivation := by
  change (T.comap nativeAlbertDerivationSkewEquiv.toLinearMap).map
    (albertJordan.restrictDerivation.comp nativeAlbertDerivationSkewEquiv.toLinearMap) = _
  rw [Submodule.map_comp, Submodule.map_comap_eq_of_surjective nativeAlbertDerivationSkewEquiv.surjective]

/-- The frame assertion for ordinary native Lie Cartans gives the represented frame assertion. -/
theorem albertCartansFrameType_of_native (compact : CompactKilling NativeAlbertDerivations)
    (h : ∀ T : LieSubalgebra ℝ NativeAlbertDerivations, T.IsCartanSubalgebra →
      IsFrameType (nativeAlbertRestrictedCartan T) 4 (1 / 6)) :
    AlbertCartansFrameType := by
  intro T hT
  rw [← nativeAlbertCartanOfRepresented_restricted_eq T hT]
  exact h _ (nativeAlbertCartanOfRepresented_isCartan compact T hT)

theorem isAlbertCompactCartan_iff_isRepresented (T : Submodule ℝ albertJordan.skewDerivations) :
    IsAlbertCompactCartan T ↔ IsRepresentedOperatorCartan T := by
  rw [isRepresentedOperatorCartan_iff_maximal]
  constructor
  · rintro ⟨hcomm, hmax⟩
    refine ⟨fun X Y => hcomm X.val X.property Y.val Y.property, ?_⟩
    intro S hTS hS
    exact (hmax S hTS (fun X hX Y hY => hS ⟨X, hX⟩ ⟨Y, hY⟩)).le
  · rintro ⟨hcomm, hmax⟩
    refine ⟨fun X hX Y hY => hcomm ⟨X, hX⟩ ⟨Y, hY⟩, ?_⟩
    intro S hTS hS
    exact le_antisymm (hmax S hTS (fun X Y => hS X.val X.property Y.val Y.property)) hTS

theorem compactF4ToriFrameType_iff_albertCartansFrameType :
    CompactF4ToriFrameType ↔ AlbertCartansFrameType :=
  ⟨fun h T hT => h T ((isAlbertCompactCartan_iff_isRepresented T).mpr hT),
    fun h T hT => h T ((isAlbertCompactCartan_iff_isRepresented T).mp hT)⟩

end

end ThirteenPlanes.Cartan
