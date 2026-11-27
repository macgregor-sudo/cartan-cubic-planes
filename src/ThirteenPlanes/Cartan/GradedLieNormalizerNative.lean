module

public import ThirteenPlanes.Cartan.GradedLieNormalizerAlbert
public import ThirteenPlanes.Cartan.GradedRecutAction

@[expose] public section

/-! The native Lie-algebra action of an actual Albert exponential on a real operator subspace. -/

namespace ThirteenPlanes.Cartan

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Exponential normalization in the actual native Albert derivation Lie algebra. -/
theorem nativeAlbertExp_normalizes_comap (D : NativeAlbertDerivations)
    (S : Submodule ℝ (Module.End ℝ Glennie.Albert))
    (closed : ∀ X ∈ S, operatorBracket D.val X ∈ S) :
    let T := S.comap nativeAlbertDerivations.toSubmodule.subtype
    let k := albertExpCompactAutomorphism (nativeAlbertDerivationSkewEquiv D)
    T.map (nativeAlbertLieAction k).toLinearEquiv.toLinearMap = T := by
  let k := albertExpCompactAutomorphism (nativeAlbertDerivationSkewEquiv D)
  let f := nativeAlbertLieAction k
  let T := S.comap nativeAlbertDerivations.toSubmodule.subtype
  have h : S.map k.equiv.conj.toLinearMap = S :=
    albertExpCompactAutomorphism_normalizes (nativeAlbertDerivationSkewEquiv D) S closed
  change T.map f.toLinearEquiv.toLinearMap = T
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    change (f X).val ∈ S
    rw [show (f X).val = k.equiv.conj X.val from nativeAlbertLieAction_val k X, ← h]
    exact Submodule.mem_map_of_mem hX
  · intro X hX
    have hx : X.val ∈ S := hX
    have hc : X.val ∈ S.map k.equiv.conj.toLinearMap := h.symm ▸ hx
    obtain ⟨Y, hY, he⟩ := hc
    let E := f.symm X
    have hE : k.equiv.conj E.val = X.val :=
      (nativeAlbertLieAction_val k E).symm.trans (congrArg Subtype.val (f.apply_symm_apply X))
    have hRaw : Y = E.val := k.equiv.conj.injective (he.trans hE.symm)
    refine ⟨E, ?_, f.apply_symm_apply X⟩
    change E.val ∈ S
    exact hRaw ▸ hY

end

end ThirteenPlanes.Cartan
