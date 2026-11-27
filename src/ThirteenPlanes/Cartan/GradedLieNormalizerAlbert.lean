module

public import ThirteenPlanes.Cartan.GradedLieNormalizer
public import ThirteenPlanes.Cartan.AlbertDerivationComplex
public import ThirteenPlanes.Cartan.GradedLineInnerAction

@[expose] public section

/-! The exponential normalizer on the literal compact Albert and traceless carriers. -/

namespace ThirteenPlanes.Cartan

open NormedSpace

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The native compact Albert automorphism given by the exponential of the actual derivation. -/
def albertExpCompactAutomorphism (D : albertJordan.skewDerivations) : Glennie.CompactAutomorphism :=
  nativeAlbertAutomorphism (albertJordan.expAutomorphism D)

@[simp] theorem albertExpCompactAutomorphism_apply (D : albertJordan.skewDerivations)
    (x : Glennie.Albert) :
    (albertExpCompactAutomorphism D).equiv x =
      exp (LinearMap.toContinuousLinearMap D.val.val) x :=
  albertJordan.expAutomorphism_apply D x

@[simp] theorem albertExpCompactAutomorphism_symm_apply (D : albertJordan.skewDerivations)
    (x : Glennie.Albert) :
    (albertExpCompactAutomorphism D).equiv.symm x =
      exp (-LinearMap.toContinuousLinearMap D.val.val) x :=
  albertJordan.expAutomorphism_symm_apply D x

theorem albertExpCompactAutomorphism_traceAction (D : albertJordan.skewDerivations) :
    (albertJordanAction (albertExpCompactAutomorphism D)).traceAction albertJordan =
      (albertJordan.expAutomorphism D).traceAction albertJordan := by
  apply LinearIsometryEquiv.ext
  intro x
  apply Subtype.ext
  rfl

/-- The inverse and action in the operator conjugation are the literal exponentials. -/
theorem albertExpCompactAutomorphism_conjugate_apply (D : albertJordan.skewDerivations)
    (X : Module.End ℝ Glennie.Albert) (x : Glennie.Albert) :
    ((albertExpCompactAutomorphism D).equiv.conj X) x =
      exp (LinearMap.toContinuousLinearMap D.val.val)
        (X (exp (-LinearMap.toContinuousLinearMap D.val.val) x)) := by
  rw [LinearEquiv.conj_apply_apply, albertExpCompactAutomorphism_apply,
    albertExpCompactAutomorphism_symm_apply]

/-- Normalization on any actual real Albert operator subspace stable under the derivation commutator. -/
theorem albertExpCompactAutomorphism_normalizes (D : albertJordan.skewDerivations)
    (S : Submodule ℝ (Module.End ℝ Glennie.Albert))
    (closed : ∀ X ∈ S, operatorBracket D.val.val X ∈ S) :
    S.map (albertExpCompactAutomorphism D).equiv.conj.toLinearMap = S :=
  albertJordan.expAutomorphism_normalizes D S closed

/-- The full skew derivation realization of a specified real operator subspace. -/
def albertSkewDerivationsIn (S : Submodule ℝ (Module.End ℝ Glennie.Albert)) :
    Submodule ℝ albertJordan.skewDerivations :=
  S.comap ((skewOperators Glennie.Albert).subtype.comp albertJordan.skewDerivations.subtype)

/-- The projected trace-kernel action of the actual native exponential normalizes the
restricted representation of any derivation subspace closed under its commutator. -/
theorem albertExpCompactAutomorphism_normalizes_trace (D : albertJordan.skewDerivations)
    (S : Submodule ℝ (Module.End ℝ Glennie.Albert))
    (closed : ∀ X ∈ S, operatorBracket D.val.val X ∈ S) :
    ((albertSkewDerivationsIn S).map albertJordan.restrictDerivation).map
        (conjugateSkew ((albertJordanAction (albertExpCompactAutomorphism D)).traceAction albertJordan)).toLinearMap =
      (albertSkewDerivationsIn S).map albertJordan.restrictDerivation := by
  let K := albertSkewDerivationsIn S
  let g := albertJordan.expAutomorphism D
  have hK : K.map (g.conjugateDerivationEquiv albertJordan).toLinearMap = K := by
    apply albertJordan.expAutomorphism_normalizes_derivationSubspace D K
    intro X hx
    let d := nativeAlbertDerivationSkewEquiv.symm D
    let x := nativeAlbertDerivationSkewEquiv.symm X
    let Y := nativeAlbertDerivationSkewEquiv ⁅d, x⁆
    have hY : Y.val.val = operatorBracket D.val.val X.val.val := rfl
    have hRaw : X.val.val ∈ S := hx
    refine ⟨Y, ?_, hY⟩
    change Y.val.val ∈ S
    rw [hY]
    exact closed X.val.val hRaw
  rw [albertExpCompactAutomorphism_traceAction]
  change (K.map albertJordan.restrictDerivation).map
    (conjugateSkew (g.traceAction albertJordan)).toLinearMap = _
  rw [g.restrictDerivation_map_conjugate albertJordan, hK]

end

end ThirteenPlanes.Cartan
