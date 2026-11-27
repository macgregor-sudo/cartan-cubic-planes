module

public import ThirteenPlanes.Cartan.AlbertQutritGeneration
public import ThirteenPlanes.AlbertGrading.Grading.GradedSystem

@[expose] public section

/-! The Hermitian matrix model of each native graded Albert line. -/

namespace ThirteenPlanes.Cartan

open AlbertGrading.Grading Graded

/-- Each projective line of an actual ternary Albert grading has a unital
complex Hermitian Jordan model. -/
theorem nativeGradedLine_has_hermitianModel {ρ : TernaryAction}
    (hρ : IsTernaryGrading ρ) (l : SignedPlaneIndex) :
    ∃ I : FullHermitian3 ≃ₗ[ℝ] lineAlgebraOf ρ l,
      (I hermitianOne).val = 1 ∧
      ∀ X Y, (I (fullHermitianProduct X Y)).val =
        Glennie.jordan (I X).val (I Y).val :=
  (AlbertGrading.graded_part_five nativeQutritGeneration hρ l).2.1

end ThirteenPlanes.Cartan
