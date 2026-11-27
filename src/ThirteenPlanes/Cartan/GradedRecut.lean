module

public import ThirteenPlanes.Cartan.GradeRealAlbertOD
public import ThirteenPlanes.Cartan.GradedLineRestrictionNative
public import ThirteenPlanes.Cartan.GradedLieNormalizerRecut
public import ThirteenPlanes.Cartan.GradedRecutDecomposition

@[expose] public section

/-! Rotation of the four compact Albert Cartans over a projective line by any special unitary matrix. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading NormedSpace

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ρ : TernaryAction} (hρ : IsTernaryGrading ρ) (l : SignedPlaneIndex)

/-- The sum of the four real graded Cartans belonging to the projective line. -/
def gradedLineCartanSum : Submodule ℝ NativeAlbertDerivations :=
  ⨆ p : recutLinePoints l, (albertGradingRealCartan hρ p.val).toSubmodule

set_option maxHeartbeats 800000 in
/-- Every special unitary matrix lifts in the prescribed Jordan coordinates to the exponential
of a derivation in the four-Cartan line sum. It normalizes that sum, and the resulting partial
conjugation is a Cartan decomposition with the stated fixed planes and conjugacy obstruction. -/
theorem ternaryGrading_lineRecut (I : Graded.FullHermitian3 ≃ₗ[ℝ] lineAlgebraOf ρ l)
    (product : ∀ x y, (I (Graded.fullHermitianProduct x y)).val = Glennie.jordan (I x).val (I y).val)
    (U : ComplexSpecialUnitary3) :
    ∃ X : NativeAlbertDerivations, X ∈ gradedLineCartanSum hρ l ∧
      let k := albertExpCompactAutomorphism (nativeAlbertDerivationSkewEquiv X)
      let W := rotatedKillingCartans (albertGradingRealCartan hρ) (recutLinePoints l) (nativeAlbertLieAction k)
      (∀ z : Glennie.Albert, k.equiv z = exp
        (LinearMap.toContinuousLinearMap (nativeAlbertDerivationSkewEquiv X).val.val) z) ∧
      (lineAlgebraOf ρ l).map k.equiv.toLinearMap = lineAlgebraOf ρ l ∧
      (∀ x : Graded.FullHermitian3, k.equiv (I x).val = (I (hermitianUnitaryConjugation U x)).val) ∧
      (gradedLineCartanSum hρ l).map (nativeAlbertLieAction k).toLinearMap = gradedLineCartanSum hρ l ∧
      IsKillingCartanOD W ∧ (∀ p, albertRealFixed (W p) = recutPointPlanes ρ l k p) ∧
      (¬ permutesGradedLinePlanes ρ l k → ¬ ∃ (a : Glennie.CompactAutomorphism) (π : Equiv.Perm SignedPlaneIndex),
        ∀ p, (albertGradingRealCartan hρ p).map (nativeAlbertLieAction a).toLieHom = W (π p)) := by
  let K := (albertGradingBasis hρ).realLineDerivations (signedProjectiveLine l)
  obtain ⟨D, hD, hline, hU⟩ := lift_specialUnitary_on_line (lineAlgebraOf ρ l) K
    (nativeGradedLine_productClosed hρ l) I product (nativeGradedLineRestriction_surjective hρ l) U
  let X := nativeAlbertDerivationSkewEquiv.symm D
  let k := albertExpCompactAutomorphism (nativeAlbertDerivationSkewEquiv X)
  have hS : gradedLineCartanSum hρ l = K.comap nativeAlbertDerivations.toSubmodule.subtype :=
    iSup_realCartan_eq_comap_realLineDerivations hρ l
  have hX : X ∈ gradedLineCartanSum hρ l := by
    rw [hS]
    exact hD
  have normalizes : (gradedLineCartanSum hρ l).map (nativeAlbertLieAction k).toLinearMap = gradedLineCartanSum hρ l :=
    nativeAlbertExp_normalizes_gradedCartanLine hρ l X hD
  obtain ⟨hOD, _, _, fixed⟩ := ternaryGrading_derivationCartanOD hρ
  refine ⟨X, hX, albertExpCompactAutomorphism_apply (nativeAlbertDerivationSkewEquiv X), ?_, ?_, normalizes, ?_⟩
  · simpa only [X, nativeAlbertDerivationSkewEquiv.apply_symm_apply, albertExpCompactAutomorphism] using hline
  · simpa only [X, nativeAlbertDerivationSkewEquiv.apply_symm_apply, albertExpCompactAutomorphism] using hU
  · exact recut_decomposition_of_graded_fixedPlanes hρ l (albertGradingRealCartan hρ) hOD fixed k normalizes

end

end ThirteenPlanes.Cartan
