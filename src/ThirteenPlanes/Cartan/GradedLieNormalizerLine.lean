module

public import ThirteenPlanes.Cartan.GradedLieNormalizerNative
public import ThirteenPlanes.Cartan.GradedLineRestrictionNativeCore

@[expose] public section

/-! Exponential normalization of the actual graded Albert line derivations. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Exponential normalization on the actual real Albert line operator space. -/
theorem albertExp_normalizes_rawGradingLine {ρ : TernaryAction} (hρ : IsTernaryGrading ρ)
    (l : SignedPlaneIndex) (D : NativeAlbertDerivations)
    (hD : D.val ∈ (albertGradingBasis hρ).realLineDerivations (signedProjectiveLine l)) :
    let S := (albertGradingBasis hρ).realLineDerivations (signedProjectiveLine l)
    let k := albertExpCompactAutomorphism (nativeAlbertDerivationSkewEquiv D)
    S.map k.equiv.conj.toLinearMap = S :=
  albertExpCompactAutomorphism_normalizes (nativeAlbertDerivationSkewEquiv D)
    ((albertGradingBasis hρ).realLineDerivations (signedProjectiveLine l))
    (fun _ hX => (albertGradingBasis hρ).realLineDerivations_bracket (signedProjectiveLine l) hD hX)

/-- Exponential normalization of the actual real line as a subspace of native derivations. -/
theorem nativeAlbertExp_normalizes_realLineDerivations {ρ : TernaryAction} (hρ : IsTernaryGrading ρ)
    (l : SignedPlaneIndex) (D : NativeAlbertDerivations)
    (hD : D.val ∈ (albertGradingBasis hρ).realLineDerivations (signedProjectiveLine l)) :
    let T := ((albertGradingBasis hρ).realLineDerivations (signedProjectiveLine l)).comap
      nativeAlbertDerivations.toSubmodule.subtype
    let k := albertExpCompactAutomorphism (nativeAlbertDerivationSkewEquiv D)
    T.map (nativeAlbertLieAction k).toLinearEquiv.toLinearMap = T :=
  nativeAlbertExp_normalizes_comap D ((albertGradingBasis hρ).realLineDerivations (signedProjectiveLine l))
    (fun _ hX => (albertGradingBasis hρ).realLineDerivations_bracket (signedProjectiveLine l) hD hX)

end

end ThirteenPlanes.Cartan
