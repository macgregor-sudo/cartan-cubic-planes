module

public import ThirteenPlanes.AlbertGrading.Grading.Statements
public import ThirteenPlanes.Qutrit.Native

@[expose] public section

set_option backward.privateInPublic true

/-! The actual Section 3 input to the native Albert grading theorem. -/

namespace ThirteenPlanes.Cartan

open Graded JordanFrames RoundCubics AlbertGrading.Grading

noncomputable section

private def hermitianCarrierEquiv : FullHermitian3 ≃ₗ[ℝ] AlbertSequential.Hermitian3 where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem generatedFrameSubalgebra_eq (F G : Fin 3 → Glennie.Albert) :
    generatedSubalgebra (Set.range F ∪ Set.range G) = framePairGenerated nativeFullCubic 1 F G := by
  unfold generatedSubalgebra framePairGenerated
  congr 1
  ext B
  constructor
  · rintro ⟨hu, hs, hc⟩
    exact ⟨hu, fun {x y} hx hy => hc x y hx hy,
      fun i => hs (Or.inl ⟨i, rfl⟩), fun i => hs (Or.inr ⟨i, rfl⟩)⟩
  · rintro ⟨hu, hc, hf, hg⟩
    refine ⟨hu, ?_, fun x y hx hy => hc hx hy⟩
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hf i
    · exact hg i

private theorem inverseHermitianIso {A : Submodule ℝ Glennie.Albert}
    (he : (1 : Glennie.Albert) ∈ A) (hc : IsClosedPiece nativeFullCubic A)
    (I : A ≃ₗ[ℝ] AlbertSequential.Hermitian3) (hu : (I ⟨1, he⟩).val = 1)
    (hp : ∀ x y : A, (I ⟨nativeFullCubic.L x.val y.val, hc x.property y.property⟩).val =
      symmetricMatrixProduct (I x).val (I y).val) :
    ∃ K : FullHermitian3 ≃ₗ[ℝ] A, (K hermitianOne).val = 1 ∧
      ∀ X Y, (K (fullHermitianProduct X Y)).val = Glennie.jordan (K X).val (K Y).val := by
  let H := hermitianCarrierEquiv
  let K := H.trans I.symm
  refine ⟨K, ?_, ?_⟩
  · have hu' : I ⟨1, he⟩ = H hermitianOne := Subtype.ext hu
    exact congrArg Subtype.val (I.symm_apply_eq.mpr hu'.symm)
  · intro X Y
    let z : A :=
      ⟨Glennie.jordan (K X).val (K Y).val, hc (K X).property (K Y).property⟩
    have hz : I z = H (fullHermitianProduct X Y) := by
      apply Subtype.ext
      have hh := hp (K X) (K Y)
      change (I z).val = symmetricMatrixProduct (I (I.symm (H X))).val (I (I.symm (H Y))).val at hh
      rw [I.apply_symm_apply, I.apply_symm_apply] at hh
      exact hh.trans rfl
    change (I.symm (H (fullHermitianProduct X Y))).val = z.val
    exact congrArg (fun a : A => a.val) (I.symm_apply_eq.mpr hz.symm)

/-- Two actual orthogonal Albert frame planes supply the grading theorem's unital qutrit input. -/
theorem nativeQutritGeneration : AlbertGrading.FrameProperties.QutritGeneration := by
  intro F G hF hG orth
  rw [generatedFrameSubalgebra_eq]
  obtain ⟨_, _, _, _, he, hc, I, _, _, hu, _, hp, _, _⟩ :=
    native_framePair_generated_qutrit hF hG orth
  exact inverseHermitianIso he hc I hu hp

end

end ThirteenPlanes.Cartan
