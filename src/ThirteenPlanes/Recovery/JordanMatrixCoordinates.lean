module

public import ThirteenPlanes.Recovery.JordanModels

@[expose] public section

set_option backward.privateInPublic true

namespace ThirteenPlanes.RoundCubics

open AlbertSequential AlbertSequential.NativeAnalysis
open scoped BigOperators RealInnerProductSpace

noncomputable section

section AssociativeModels

variable {D : Type} [Ring D] [StarRing D] [Algebra ℝ D] [StarModule ℝ D]
  [IsScalarTower ℝ D D] [SMulCommClass ℝ D D]

private abbrev FullMatrix := selfAdjoint (Matrix (Fin 3) (Fin 3) D)

private def matrixJordan (M N : FullMatrix (D := D)) : FullMatrix (D := D) :=
  ⟨(1 / 2 : ℝ) • (M.val * N.val + N.val * M.val), by
    rw [selfAdjoint.mem_iff, star_smul, star_add, star_mul, star_mul, M.property,
      N.property, star_trivial, add_comm]⟩

/-- The actual Hermitian matrices over the real, complex, and quaternionic coefficient
algebras map onto the corresponding native carriers. -/
def matrixHermitianCoordinates (A : AssocCD D) :
    FullMatrix (D := D) ≃ₗ[ℝ] hermitianTraceCarrier (jordanSubalgebraH3 A.subalgebra) :=
  (assocHermEquiv A).trans (hermitianCoordinates (jordanSubalgebraH3 A.subalgebra))

theorem matrixHermitianCoordinates_preserves (A : AssocCD D) :
    matrixHermitianCoordinates A 1 = hermitianUnit (jordanSubalgebraH3 A.subalgebra) ∧
    (∀ M N, matrixHermitianCoordinates A (matrixJordan M N) =
      hermitianJordanProduct (jordanSubalgebraH3 A.subalgebra)
        (matrixHermitianCoordinates A M) (matrixHermitianCoordinates A N)) ∧
    (∀ M, Glennie.trace (matrixHermitianCoordinates A M : Glennie.Albert) =
      ∑ i, A.re (M.val i i)) ∧
    ∀ M N, ⟪matrixHermitianCoordinates A M, matrixHermitianCoordinates A N⟫ =
      ∑ i, A.re ((M.val * N.val) i i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change hermitianCoordinates _ (assocHermEquiv A 1) = hermitianCoordinates _ _
    exact congrArg (hermitianCoordinates _) (Subtype.ext (assocHermEquiv_one A))
  · intro M N
    change hermitianCoordinates _ (assocHermEquiv A (matrixJordan M N)) =
      hermitianJordanProduct _ (hermitianCoordinates _ (assocHermEquiv A M))
        (hermitianCoordinates _ (assocHermEquiv A N))
    rw [← hermitianCoordinates_product]
    apply congrArg (hermitianCoordinates _)
    apply Subtype.ext
    change (assocHermEquiv A (matrixJordan M N)).val =
      jordanMul (assocHermEquiv A M).val (assocHermEquiv A N).val
    rw [assocHermEquiv_apply, assocHermEquiv_apply, assocHermEquiv_apply]
    exact jordanMul_assocMatToAlbert A (M := M) (N := N)
  · intro M
    change Glennie.trace (hermitianCoordinates _ (assocHermEquiv A M) : Glennie.Albert) = _
    rw [hermitianCoordinates_apply, recoveredCoordinateEquiv_trace, assocHermEquiv_apply]
    rfl
  · intro M N
    change Glennie.inner (hermitianCoordinates _ (assocHermEquiv A M))
      (hermitianCoordinates _ (assocHermEquiv A N)) = _
    rw [hermitianCoordinates_apply, hermitianCoordinates_apply, recoveredCoordinateEquiv_tracePairing,
      assocHermEquiv_apply, assocHermEquiv_apply, tracePairing_assocMatToAlbert]

end AssociativeModels

/-- The three associative coefficient choices agree with the corresponding literal matrix carriers. -/
theorem associativeHermitianCarriers_eq :
    jordanSubalgebraH3 assocCD_R.subalgebra = H3Subalgebra .R ∧
    jordanSubalgebraH3 assocCD_C.subalgebra = H3Subalgebra .C ∧
    jordanSubalgebraH3 assocCD_H.subalgebra = H3Subalgebra .H :=
  ⟨rfl, rfl, rfl⟩

/-- The octonionic level contains the whole compact Albert matrix algebra. -/
theorem octonionicHermitianCarrier_eq_top :
    (H3Subalgebra .O).carrier.map recoveredCoordinateEquiv.toLinearMap = ⊤ := by
  rw [H3Subalgebra_O_eq_top]
  change (⊤ : Submodule ℝ Albert).map recoveredCoordinateEquiv.toLinearMap = ⊤
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr recoveredCoordinateEquiv.surjective]

end
end ThirteenPlanes.RoundCubics
