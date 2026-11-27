module

public import ThirteenPlanes.FlowStatements
public import ThirteenPlanes.PencilFlow.Gradient.Field
public import ThirteenPlanes.PencilFlow.Gradient.Floor
public import ThirteenPlanes.PencilFlow.Pencil.Invariant
public import ThirteenPlanes.PencilFlow.Pencil.Floor
public import ThirteenPlanes.PencilFlow.Dynamics.PositiveMixing
public import ThirteenPlanes.PencilFlow.Dynamics.Variance
public import ThirteenPlanes.PencilFlow.Hessian.PointSpectrum
public import ThirteenPlanes.PencilFlow.Hessian.LocalFlow
public import ThirteenPlanes.PencilFlow.Model.FourPlanes

@[expose] public section

/-! Section 9, "The one-loop flow returns to the round cubic." -/

namespace ThirteenPlanes.PencilFlow.Proofs

/-- Lemma 9-gradient, Proposition pencil-invariant, Theorem flow and the pencil parts of
Proposition variance. -/
theorem flowResults (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : FlowResults V where
  gradientScaling := gradientScaling V
  gradientPotential := gradientPotential V
  gradientOfOneLoopPotential := gradientOfOneLoopPotential V
  gradientDissipation := gradientDissipation V
  pencilContractions := pencilContractions V
  pencilInvariant := pencilInvariant V
  coefficientEquations := coefficientEquations V
  fixedRatios := fixedRatios V
  positiveMixing_tendsToRound := positiveMixing_tendsToRound V
  equalSplitEnergy := equalSplitEnergy V
  infraredExponent := infraredExponent V
  pencilFloorConditions := pencilFloorConditions V
  relativeVarianceDescent := relativeVarianceDescent V

/-- Proposition variance (a), (b) and Proposition 9-hessian. -/
theorem potentialResults (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] : PotentialResults V where
  potentialFloor := potentialFloor V
  harmonicIsotropicFloor := harmonicIsotropicFloor V
  roundPointHessianSpectrum := roundPointHessianSpectrum V
  roundPointHessianMultiplicities := roundPointHessianMultiplicities V
  roundOrbitLocalConvergence := roundOrbitLocalConvergence V

end ThirteenPlanes.PencilFlow.Proofs
