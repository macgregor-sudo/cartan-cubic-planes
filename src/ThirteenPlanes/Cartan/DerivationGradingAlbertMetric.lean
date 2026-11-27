module

public import ThirteenPlanes.Cartan.DerivationGradingCompactness
public import ThirteenPlanes.Cartan.AlbertDerivationComplex

@[expose] public section

/-! The invariant positive trace form on the literal real Albert derivations. -/

namespace ThirteenPlanes.Cartan

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The paper's represented form on the actual Lie algebra of compact Albert derivations. -/
def nativeAlbertTracePairing : LinearMap.BilinForm ℝ NativeAlbertDerivations :=
  endTracePairing nativeAlbertDerivations

theorem nativeAlbertTracePairing_apply (X Y : NativeAlbertDerivations) :
    nativeAlbertTracePairing X Y = -LinearMap.trace ℝ Glennie.Albert (X.val * Y.val) :=
  endTracePairing_apply _ X Y

/-- Removing the unit direction leaves the represented trace form unchanged. -/
theorem nativeAlbertTracePairing_eq_traceless (X Y : NativeAlbertDerivations) :
    nativeAlbertTracePairing X Y = -LinearMap.trace ℝ albertJordan.traceFree
      ((albertJordan.restrictDerivation (nativeAlbertDerivationSkewEquiv X)).val *
       (albertJordan.restrictDerivation (nativeAlbertDerivationSkewEquiv Y)).val) := by
  have h := albertJordan.restrictDerivation_inner
    (nativeAlbertDerivationSkewEquiv X) (nativeAlbertDerivationSkewEquiv Y)
  rw [skewOperator_inner, skewOperator_inner] at h
  rw [nativeAlbertTracePairing_apply]
  exact h.symm

theorem nativeAlbertTracePairing_symmetric (X Y : NativeAlbertDerivations) :
    nativeAlbertTracePairing X Y = nativeAlbertTracePairing Y X :=
  endTracePairing_symmetric _ X Y

theorem nativeAlbertTracePairing_invariant (X Y Z : NativeAlbertDerivations) :
    nativeAlbertTracePairing ⁅X,Y⁆ Z = nativeAlbertTracePairing X ⁅Y,Z⁆ :=
  endTracePairing_invariant _ X Y Z

theorem nativeAlbertTracePairing_positive (X : NativeAlbertDerivations) (hx : X ≠ 0) :
    0 < nativeAlbertTracePairing X X :=
  endTracePairing_positive nativeAlbertDerivations nativeAlbertDerivation_skew X hx

theorem nativeAlbertTracePairing_definite (X : NativeAlbertDerivations)
    (hX : nativeAlbertTracePairing X X = 0) : X = 0 := by
  by_contra hx
  exact (nativeAlbertTracePairing_positive X hx).ne' hX

/-- A centre-free real Albert derivation Lie algebra has negative definite Killing form. -/
theorem nativeAlbert_compactKilling_of_centerFree
    (hCenter : ∀ X : NativeAlbertDerivations, (∀ Y : NativeAlbertDerivations, ⁅X,Y⁆ = 0) → X = 0) :
    CompactKilling NativeAlbertDerivations :=
  compactKilling_of_invariantPositive nativeAlbertTracePairing nativeAlbertTracePairing_symmetric
    nativeAlbertTracePairing_positive nativeAlbertTracePairing_invariant hCenter

/-- Two disjoint self-centralizing abelian subalgebras suffice to force compact Killing form. -/
theorem nativeAlbert_compactKilling_of_disjoint_cartans
    (T U : LieSubalgebra ℝ NativeAlbertDerivations) (hT : IsCompactCartan T) (hU : IsCompactCartan U)
    (hdis : Disjoint T U) : CompactKilling NativeAlbertDerivations := by
  apply nativeAlbert_compactKilling_of_centerFree
  intro X hX
  have hI : X ∈ T ⊓ U := ⟨(hT X).mp (fun Y _ => hX Y), (hU X).mp (fun Y _ => hX Y)⟩
  rw [hdis.eq_bot] at hI
  change X ∈ (⊥ : Submodule ℝ NativeAlbertDerivations) at hI
  rwa [Submodule.mem_bot] at hI

end
end ThirteenPlanes.Cartan
