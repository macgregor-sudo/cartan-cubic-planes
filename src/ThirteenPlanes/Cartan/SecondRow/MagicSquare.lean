/- SPDX-License-Identifier: Apache-2.0 -/
module

public import ThirteenPlanes.Cartan.SecondRow.CompactCase
public import ThirteenPlanes.Cartan.CompactCartanRank
public import ThirteenPlanes.Cartan.SecondRowNamedMetrics

@[expose] public section

set_option backward.privateInPublic true

/-! The compact second row in Appendix B. -/

namespace ThirteenPlanes.Cartan

noncomputable section

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]
  {M : TraceJordanData J} {K : Submodule ℝ (SkewOperator J)}

private theorem secondRow_commonCartanDimension (H : SecondRowCompactRealization M K)
    (C D : LieSubalgebra ℝ H.operators) (hC : C.IsCartanSubalgebra) (hD : D.IsCartanSubalgebra) :
    Module.finrank ℝ C = Module.finrank ℝ D := by
  let : Module.Finite ℝ H.operators := Module.Finite.of_surjective H.coordinates.toLinearMap H.coordinates.surjective
  exact compactCartanSubalgebras_finrank_eq H.compact C D hC hD

/-- Corollary B.2, with the compact magic-square identifications and the compact F₄ torus
description as literature inputs. The real Cartans use the manuscript's operator trace
metric and their lifts are individually stable, Killing-orthogonal ordinary Lie Cartans. -/
theorem compactSecondRowCorollary (magic : SecondRowMagicSquareInput) (tori : AlbertCartansFrameType)
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Nonempty (magic.complexRealization.operators ≃ₗ⁅ℝ⁆ (secondRowCompactSU 3 × secondRowCompactSU 3)) ∧
    Nonempty (magic.quaternionRealization.operators ≃ₗ⁅ℝ⁆ secondRowCompactSU 6) ∧
    Nonempty (LieComplex magic.albertRealization.operators ≃ₗ⁅ℂ⁆ LieAlgebra.e₆ ℂ) ∧
    SecondRowLieCase magic.complexRealization 2 ι ∧
    SecondRowLieCase magic.quaternionRealization 3 ι ∧
    SecondRowLieCase magic.albertRealization 4 ι := by
  refine ⟨magic.complex_type, magic.quaternion_type, magic.albert_type, ?_, ?_, ?_⟩
  · exact secondRowLieCase_of_native magic.complexRealization complex_secondRowCartanExtension
      (secondRow_commonCartanDimension _) complex_allSecondRowCartanOD (complexSecondRow_metricAgreement magic)
  · exact secondRowLieCase_of_native magic.quaternionRealization quaternion_secondRowCartanExtension
      (secondRow_commonCartanDimension _) quaternion_allSecondRowCartanOD (quaternionSecondRow_metricAgreement magic)
  · exact secondRowLieCase_of_native magic.albertRealization (albert_secondRowCartanExtension tori)
      (secondRow_commonCartanDimension _) (albert_allSecondRowCartanOD tori) (albertSecondRow_metricAgreement magic)

end
end ThirteenPlanes.Cartan
