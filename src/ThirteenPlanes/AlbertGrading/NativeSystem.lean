module

public import ThirteenPlanes.Cartan.AlbertQutritGeneration
public import ThirteenPlanes.AlbertGrading.Grading.GradedSystem

@[expose] public section

/-! Native geometric inputs for graded Albert systems. -/

namespace ThirteenPlanes.AlbertGrading

/-- The native marked qutrit proof supplies the unmarked generation interface. -/
theorem nativeQutritGeneration : FrameProperties.QutritGeneration := Cartan.nativeQutritGeneration

/-- The graded system for every actual ternary grading. -/
theorem nativeGradedSystem : Statements.GradedSystem := gradedSystem nativeQutritGeneration

end ThirteenPlanes.AlbertGrading
