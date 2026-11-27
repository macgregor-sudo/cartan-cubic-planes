module

public import ThirteenPlanes.Cartan.F4.Tori
public import ThirteenPlanes.Cartan.F4.CartanInterfaces
public import ThirteenPlanes.Cartan.SecondRow.MagicSquare

@[expose] public section

/-! The compact F₄ torus theorem discharges the former inputs of both corollaries. -/

namespace ThirteenPlanes.Cartan

open RoundCubics JordanFrames

noncomputable section

/-- Every operator-trace orthogonal decomposition of compact F₄ gives thirteen mutually
unbiased native frames whose zero-weight planes fill the traceless representation. -/
theorem compactF4_cartanDecomposition_byFramePlanes
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → Submodule ℝ albertJordan.skewDerivations)
    (hCartan : ∀ i, IsAlbertCompactCartan (T i))
    (hOrth : Pairwise fun i j => ∀ X ∈ T i, ∀ Y ∈ T j, albertTracelessOperatorTrace X Y = 0)
    (hSum : DirectSum.IsInternal T) :
    Fintype.card ι = 13 ∧
      (∀ i, Module.finrank ℝ (albertZeroWeightPlane (T i)) = 2 ∧
        IsClosedPiece nativeEqualCubic (albertZeroWeightPlane (T i))) ∧
      OrthogonalSplit (fun i => albertZeroWeightPlane (T i)) ∧
      ∃ F : ι → Fin 3 → Glennie.Albert, (∀ i, Glennie.Frame (F i)) ∧
        (∀ i, albertZeroWeightPlane (T i) = nativeFramePlane (F i)) ∧
        (∀ i j, i ≠ j → ∀ a b, Glennie.inner (F i a) (F j b) = 1 / 3) :=
  compactF4_cartanDecomposition_fixedPlanes compactF4Tori_frameType T hCartan hOrth hSum

/-- The compact second-row corollary with the compact magic-square identification as its
sole quoted theorem. -/
theorem compactSecondRowCorollary_ofMagicSquare (magic : SecondRowMagicSquareInput)
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Nonempty (magic.complexRealization.operators ≃ₗ⁅ℝ⁆ (secondRowCompactSU 3 × secondRowCompactSU 3)) ∧
    Nonempty (magic.quaternionRealization.operators ≃ₗ⁅ℝ⁆ secondRowCompactSU 6) ∧
    Nonempty (LieComplex magic.albertRealization.operators ≃ₗ⁅ℂ⁆ LieAlgebra.e₆ ℂ) ∧
    SecondRowLieCase magic.complexRealization 2 ι ∧
    SecondRowLieCase magic.quaternionRealization 3 ι ∧
    SecondRowLieCase magic.albertRealization 4 ι :=
  compactSecondRowCorollary magic
    (compactF4ToriFrameType_iff_albertCartansFrameType.mp compactF4Tori_frameType) ι

end

end ThirteenPlanes.Cartan
