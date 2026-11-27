module

public import ThirteenPlanes.Cartan.Conjugation
public import ThirteenPlanes.Cartan.QuaternionFaithful
public import ThirteenPlanes.Cartan.QuaternionInvariant

@[expose] public section

set_option backward.privateInPublic true

/-! Equivariance and the full Casimir of the compact quaternionic commutator representation. -/

namespace ThirteenPlanes.Cartan

open QuaternionicMUB
open scoped Matrix BigOperators RealInnerProductSpace

noncomputable section

/-- The complete quaternionic representation with trace normalized on the fourteen-dimensional carrier. -/
abbrev quaternionRestrictOperators : quaternionOperatorAlgebra →ₗᵢ[ℝ]
    SkewOperator quaternionJordan.traceFree :=
  quaternionJordan.restrictOperators quaternionOperatorAlgebra quaternionOperatorAlgebra_le

def quaternionTraceRepresentation : quaternionSkewMatrices →ₗ[ℝ]
    SkewOperator quaternionJordan.traceFree :=
  quaternionRestrictOperators.toLinearMap.comp quaternionCommutatorEquiv.toLinearMap

/-- Unitary conjugation on the skew-Hermitian quaternionic matrices. -/
def quaternionSkewPullback (U : QBasis) (A : quaternionSkewMatrices) : quaternionSkewMatrices :=
  ⟨quaternionicPullback U A.val, by
    change (U.matᴴ * A.val * U.mat)ᴴ = -(U.matᴴ * A.val * U.mat)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      A.property]
    simp only [neg_mul, mul_neg, mul_assoc]⟩

theorem quaternionCommutator_conjugate (U : QBasis) (A : quaternionSkewMatrices) :
    conjugateSkew (quaternionJordanAction U).action (quaternionCommutatorLinear A) =
      quaternionCommutatorLinear (quaternionSkewPullback U A) := by
  let g := (quaternionJordanAction U).action
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply fullMat_injective
  change fullMat (g (quaternionCommutator A (g.symm x))) =
    fullMat (quaternionCommutator (quaternionSkewPullback U A) x)
  have h (y : HermitianHilbert) : fullMat (g y) = unitaryConjugate U (fullMat y) :=
    quaternionJordanAction_matrix U y
  have hinv : unitaryConjugate U (fullMat (g.symm x)) = fullMat x :=
    (h (g.symm x)).symm.trans (congrArg fullMat (g.apply_symm_apply x))
  have hsub (X Y : QMat) : unitaryConjugate U (X - Y) =
      unitaryConjugate U X - unitaryConjugate U Y := by
    simp only [unitaryConjugate, mul_sub, sub_mul]
  rw [h, quaternionCommutator_matrix, quaternionCommutator_matrix,
    hsub, unitaryConjugate_mul, unitaryConjugate_mul, hinv]
  rfl

theorem quaternionTraceRepresentation_conjugate (U : QBasis) (A : quaternionSkewMatrices) :
    conjugateSkew ((quaternionJordanAction U).traceAction quaternionJordan)
      (quaternionTraceRepresentation A) =
    quaternionTraceRepresentation (quaternionSkewPullback U A) := by
  have h := (quaternionJordanAction U).conjugate_restrictDerivation quaternionJordan
    ⟨quaternionCommutatorLinear A, quaternionOperatorAlgebra_le ⟨A, rfl⟩⟩
  have h' : (quaternionJordanAction U).conjugateDerivation quaternionJordan
      ⟨quaternionCommutatorLinear A, quaternionOperatorAlgebra_le ⟨A, rfl⟩⟩ =
      ⟨quaternionCommutatorLinear (quaternionSkewPullback U A),
        quaternionOperatorAlgebra_le ⟨quaternionSkewPullback U A, rfl⟩⟩ :=
    Subtype.ext (quaternionCommutator_conjugate U A)
  rw [h'] at h
  exact h

/-- The full space of quaternionic commutators restricted to the literal trace kernel. -/
abbrev quaternionDerivationOperators : Submodule ℝ (SkewOperator quaternionJordan.traceFree) :=
  LinearMap.range quaternionRestrictOperators.toLinearMap

theorem quaternionTraceRepresentation_range : LinearMap.range quaternionTraceRepresentation =
    quaternionDerivationOperators := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    exact ⟨quaternionCommutatorEquiv A, rfl⟩
  · rintro _ ⟨D, rfl⟩
    obtain ⟨A, rfl⟩ := quaternionCommutatorEquiv.surjective D
    exact ⟨A, rfl⟩

private theorem quaternionSkewPullback_surjective (U : QBasis) :
    Function.Surjective (quaternionSkewPullback U) := by
  intro A
  let B : quaternionSkewMatrices := ⟨(quaternionicPullback U).symm A.val, by
    change (U.mat * A.val * U.matᴴ)ᴴ = -(U.mat * A.val * U.matᴴ)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      A.property]
    simp only [neg_mul, mul_neg, mul_assoc]⟩
  exact ⟨B, Subtype.ext ((quaternionicPullback U).apply_symm_apply A.val)⟩

theorem quaternionDerivationOperators_normalizes (U : QBasis) :
    quaternionDerivationOperators.map
        (conjugateSkew ((quaternionJordanAction U).traceAction quaternionJordan)).toLinearMap =
      quaternionDerivationOperators := by
  rw [← quaternionTraceRepresentation_range]
  apply le_antisymm
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨quaternionSkewPullback U A, (quaternionTraceRepresentation_conjugate U A).symm⟩
  · rintro _ ⟨A, rfl⟩
    obtain ⟨B, rfl⟩ := quaternionSkewPullback_surjective U A
    exact ⟨quaternionTraceRepresentation B, ⟨B, rfl⟩, quaternionTraceRepresentation_conjugate U B⟩


end

end ThirteenPlanes.Cartan
