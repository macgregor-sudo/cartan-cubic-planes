module

public import ThirteenPlanes.HessianSpectrum
public import ThirteenPlanes.SignedSkewStabilizerTransport

@[expose] public section

set_option backward.privateInPublic true

/-! The exact native derivation algebra is the skew stabilizer of the signed cubic. -/

namespace ThirteenPlanes

noncomputable section

open SignedSkew

private def signedSkewToDerivation :
    skewStabilizer signedEqualCubic →ₗ[ℝ] AlbertSequential.AlbertDerivation where
  toFun A := ⟨extendSignedEnd A.val.val, (extendSignedEnd_derivation_iff A.val.val).2
    ⟨A.val.property, (insert_zero_iff_centerDerivation signedEqualCubic _ A.val.property).mp A.property⟩⟩
  map_add' A B := Subtype.ext (extendSignedEnd.map_add A.val.val B.val.val)
  map_smul' r A := Subtype.ext (extendSignedEnd.map_smul r A.val.val)

/-- The actual signed cubic's skew stabilizer is the native Albert derivation module. -/
def signedSkewStabilizer_nativeDerivationEquiv :
    skewStabilizer signedEqualCubic ≃ₗ[ℝ] AlbertSequential.AlbertDerivation := by
  refine LinearEquiv.ofBijective signedSkewToDerivation ⟨?_, ?_⟩
  · intro A B h
    have he := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    have ht := congrArg (fun f : AlbertSequential.Albert →ₗ[ℝ] AlbertSequential.Albert =>
      f (signedSplitSequentialEquiv (x,0))) he
    change extendSignedEnd A.val.val _ = extendSignedEnd B.val.val _ at ht
    simp only [extendSignedEnd_on_image, liftSignedEnd_apply] at ht
    exact congrArg Prod.fst (signedSplitSequentialEquiv.injective ht)
  · intro D
    obtain ⟨A, hA⟩ := extendSignedEnd_surj D
    have h : extendSignedEnd A ∈ AlbertSequential.albertDerivations := hA ▸ D.property
    obtain ⟨hs,hc⟩ := (extendSignedEnd_derivation_iff A).mp h
    exact ⟨⟨⟨A,hs⟩,(insert_zero_iff_centerDerivation signedEqualCubic A hs).mpr hc⟩, Subtype.ext hA⟩

/-- The exact infinitesimal stabilizer dimension of the signed cubic is 52. -/
theorem signedSkewStabilizer_finrank : Module.finrank ℝ (skewStabilizer signedEqualCubic) = 52 :=
  signedSkewStabilizer_nativeDerivationEquiv.finrank_eq.trans AlbertSequential.finrank_albertDerivation

/-- Multiplying the signed cubic by a nonzero strength preserves its exact skew stabilizer rank. -/
theorem signedSkewStabilizer_smul_finrank {r : ℝ} (hr : r ≠ 0) :
    Module.finrank ℝ (skewStabilizer (r • signedEqualCubic)) = 52 := by
  have hsub : skewStabilizer (r • signedEqualCubic) = skewStabilizer signedEqualCubic := by
    ext A
    rw [mem_skewStabilizer, mem_skewStabilizer]
    have hmul : (r • signedEqualCubic).insert A.val = r • signedEqualCubic.insert A.val := by
      apply SymmetricCubic.ext
      intro x y z
      simp only [SymmetricCubic.apply_insert, SymmetricCubic.apply_smul]
      ring
    rw [hmul]
    exact smul_eq_zero.trans (or_iff_right hr)
  rw [hsub, signedSkewStabilizer_finrank]

end

end ThirteenPlanes
