module

public import ThirteenPlanes.PencilFlow.Hessian.Stabilizer

@[expose] public section

/-! Proposition 9-hessian, parts (a) and (b): the Hessian at a normalized harmonic round cubic. -/

open Filter Set
open scoped BigOperators RealInnerProductSpace Topology

namespace ThirteenPlanes.PencilFlow.HessianBridge

noncomputable section

open SymmetricCubic Statements

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A floor cubic is a zero of the rescaled field (it minimizes the A-function). -/
theorem rescaledField_floor (hn : 0 < Module.finrank ℝ V) {C : SymmetricCubic V}
    (hfl : aFunction C = floorValue (Module.finrank ℝ V)) : rescaledField C = 0 := by
  have hmin : IsLocalMin aFunction C :=
    Filter.Eventually.of_forall fun y => hfl ▸ floorValue_le_aFunction hn y
  have h0 := hmin.hasFDerivAt_eq_zero (aFunction_hasFDerivAt C)
  have h1 : -rescaledField C = 0 :=
    (InnerProductSpace.toDual ℝ (SymmetricCubic V)).map_eq_zero_iff.mp h0
  exact neg_eq_zero.mp h1

end

end ThirteenPlanes.PencilFlow.HessianBridge

namespace ThirteenPlanes.PencilFlow.Proofs

open Statements HessianBridge

/-- Proposition 9-hessian (a). -/
theorem roundPointHessianSpectrum (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] : Statements.HessianA V := by
  intro h c hT hR
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hfl := unitRound_floor hT hR
  exact ⟨rescaledField_floor hn hfl, hessianOperator_formula hn hfl, hessianOperator_ker hn hfl,
    one_lt_traceEigenvalue _, hessianOperator_eigenspace_trace hn hfl, finrank_traceSpace,
    hessianOperator_eigenspace_one hn hfl, rotationAdjoint_projection hn hfl⟩

/-- Proposition 9-hessian (b). -/
theorem roundPointHessianMultiplicities (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] : Statements.HessianB V := by
  intro h c hT hR
  have hn : 0 < Module.finrank ℝ V := Module.finrank_pos
  have hfl := unitRound_floor hT hR
  refine ⟨?_, mem_skewStabilizer_iff_rotation _, ?_⟩
  · have := finrank_rotationSpace_add_skewStabilizer (unitRoundCubic h c)
    omega
  · rw [hessianOperator_eigenspace_one hn hfl]
    have h1 := finrank_three_summands hn hfl
    have h2 := finrank_traceSpace (V := V)
    omega

end ThirteenPlanes.PencilFlow.Proofs
