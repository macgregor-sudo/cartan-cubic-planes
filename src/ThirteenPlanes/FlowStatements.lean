module

public import ThirteenPlanes.EikonalRigidityStatements
public import ThirteenPlanes.PencilFlow.TensorStatements

@[expose] public section

/-! Proposition types for the five numbered results on the one-loop flow in Section 9. -/

namespace ThirteenPlanes.PencilFlow

open Statements

/-- The unrestricted gradient lemma and the closed-plane part of the flow theorem. -/
structure FlowResults (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Prop where
  gradientScaling : GradientScaling V
  gradientPotential : GradientPotential V
  gradientOfOneLoopPotential : Gradient V
  gradientDissipation : GradientDissipation V
  pencilContractions : PencilContractions V
  pencilInvariant : PencilInvariant V
  coefficientEquations : FlowCoordinates V
  fixedRatios : FixedRatios V
  positiveMixing_tendsToRound : PositiveMixingLimit V
  equalSplitEnergy : EqualSplitEnergy V
  infraredExponent : InfraredExponent V
  pencilFloorConditions : PencilFloorConditions V
  relativeVarianceDescent : VarianceC V

/-- The sphere floor and the round-orbit Hessian on a nonzero Euclidean space. -/
structure PotentialResults (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] : Prop where
  potentialFloor : VarianceA V
  harmonicIsotropicFloor : VarianceB V
  roundPointHessianSpectrum : HessianA V
  roundPointHessianMultiplicities : HessianB V
  roundOrbitLocalConvergence : HessianC V

end ThirteenPlanes.PencilFlow
